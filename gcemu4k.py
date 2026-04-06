    #!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AC'S Dolphin emu 0.2 — GameCube Emulator
=========================================
Real PowerPC 750CL (Gekko) CPU core with Cython acceleration.
Single-file with auto-compile at first run + pure Python fallback.

Features:
  - PowerPC 750CL integer ISA (~90 instructions decoded)
  - GameCube memory map (24 MB main RAM, HW register bus)
  - VI / PI / MI / DI / SI / EXI register stubs
  - DOL executable loader + GCM/ISO header parser
  - Framebuffer display from VI EFB address
  - 60 FPS tkinter GUI (Dolphin-style)

(C) A.C Holdings / Team Flames 1999-2026
"""
from __future__ import annotations

import ctypes
import hashlib
import importlib
import math
import os
import struct
import sys
import tempfile
import textwrap
import threading
import time
import tkinter as tk
from dataclasses import dataclass, field
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from typing import Any, Callable, Dict, List, Optional, Tuple

# ======================================================================
# Constants
# ======================================================================
VERSION = "0.2"
TARGET_FPS = 60
FRAME_TIME_MS = 16  # ~16.67 ms
CANVAS_W, CANVAS_H = 640, 480

RAM_SIZE      = 24 * 1024 * 1024   # 24 MB main RAM
ARAM_SIZE     = 16 * 1024 * 1024   # 16 MB audio RAM
RAM_BASE      = 0x80000000
RAM_UNCACHED  = 0xC0000000
HW_BASE       = 0xCC000000

# Hardware register offsets from HW_BASE
VI_BASE  = 0x002000
PI_BASE  = 0x003000
MI_BASE  = 0x004000
DSP_BASE = 0x005000
DI_BASE  = 0x006000
SI_BASE  = 0x006400
EXI_BASE = 0x006800
AI_BASE  = 0x006C00

# Gekko clock ≈ 486 MHz, cycles per frame ≈ 8.1M
CYCLES_PER_FRAME = 8_100_000
# We run fewer cycles in Python for responsiveness
PY_CYCLES_PER_SLICE = 50_000

# SPR numbers
SPR_LR   = 8
SPR_CTR  = 9
SPR_XER  = 1
SPR_SRR0 = 26
SPR_SRR1 = 27
SPR_SPRG0 = 272
SPR_SPRG1 = 273
SPR_SPRG2 = 274
SPR_SPRG3 = 275
SPR_HID0 = 1008
SPR_HID2 = 920
SPR_DEC  = 22
SPR_TBL  = 268
SPR_TBU  = 269
SPR_GQR0 = 912  # GQR0-7 = 912-919
SPR_DSISR = 18
SPR_DAR   = 19
SPR_DBAT0U = 536
SPR_IBAT0U = 528

MASK32 = 0xFFFFFFFF

# ======================================================================
# Cython source — PowerPC Gekko CPU hot-loop
# ======================================================================
CYTHON_SRC = r'''
# cython: boundscheck=False, wraparound=False, cdivision=True
# cython: language_level=3
from libc.stdlib cimport malloc, calloc, free
from libc.string cimport memset, memcpy
from libc.stdint cimport (uint8_t, uint16_t, uint32_t, uint64_t,
                          int8_t, int16_t, int32_t, int64_t)

cdef uint32_t MASK32 = 0xFFFFFFFF

cdef inline int32_t sign_extend_16(uint32_t v) noexcept nogil:
    if v & 0x8000:
        return <int32_t>(v | 0xFFFF0000)
    return <int32_t>v

cdef inline int32_t sign_extend_26(uint32_t v) noexcept nogil:
    if v & 0x02000000:
        return <int32_t>(v | 0xFC000000)
    return <int32_t>v

cdef inline uint32_t rotl32(uint32_t v, int n) noexcept nogil:
    n = n & 31
    return ((v << n) | (v >> (32 - n))) & MASK32

cdef inline uint32_t mask32(int mb, int me) noexcept nogil:
    cdef uint32_t m
    if mb <= me:
        m = (MASK32 >> mb) & (MASK32 << (31 - me))
    else:
        m = (MASK32 >> mb) | (MASK32 << (31 - me))
    return m

cdef class CyGekko:
    cdef public uint32_t gpr[32]
    cdef public uint32_t pc, lr, ctr, cr, xer, msr
    cdef public uint32_t srr0, srr1
    cdef public uint32_t sprg[4]
    cdef public uint32_t hid0, hid2, dec_reg
    cdef public uint32_t tbl, tbu
    cdef public uint32_t fpscr
    cdef public uint32_t gqr[8]
    cdef public double fpr[32]
    cdef public uint64_t cycles
    cdef public bint halted

    # RAM pointer — set from Python via set_ram()
    cdef uint8_t *ram
    cdef uint32_t ram_size

    # HW register read/write callbacks (set from Python)
    cdef object hw_read32_cb, hw_write32_cb

    def __cinit__(self):
        self.ram = NULL
        self.ram_size = 0
        self.hw_read32_cb = None
        self.hw_write32_cb = None
        self.reset()

    cpdef void reset(self):
        cdef int i
        for i in range(32):
            self.gpr[i] = 0
            self.fpr[i] = 0.0
        self.pc = 0; self.lr = 0; self.ctr = 0
        self.cr = 0; self.xer = 0; self.msr = 0
        self.srr0 = 0; self.srr1 = 0
        for i in range(4):
            self.sprg[i] = 0
        for i in range(8):
            self.gqr[i] = 0
        self.hid0 = 0; self.hid2 = 0; self.dec_reg = 0
        self.tbl = 0; self.tbu = 0; self.fpscr = 0
        self.cycles = 0; self.halted = False

    def set_ram(self, ram_buf: bytearray):
        """Attach Python bytearray as RAM backing store."""
        cdef Py_buffer buf
        if PyObject_GetBuffer(ram_buf, &buf, PyBUF_WRITABLE) < 0:
            raise ValueError("Cannot get buffer")
        self.ram = <uint8_t*>buf.buf
        self.ram_size = <uint32_t>buf.len
        PyBuffer_Release(&buf)

    def set_hw_callbacks(self, read_cb, write_cb):
        self.hw_read32_cb = read_cb
        self.hw_write32_cb = write_cb

    # --- Memory access ---------------------------------------------------
    cdef inline uint32_t _translate(self, uint32_t addr) noexcept nogil:
        # Cached: 0x80000000+
        if addr >= 0x80000000 and addr < 0x80000000 + self.ram_size:
            return addr - 0x80000000
        # Uncached: 0xC0000000+
        if addr >= 0xC0000000 and addr < 0xC0000000 + self.ram_size:
            return addr - 0xC0000000
        # Real mode low
        if addr < self.ram_size:
            return addr
        return 0xFFFFFFFF

    cdef uint32_t read32(self, uint32_t addr):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa + 3 < self.ram_size:
            return ((self.ram[pa] << 24) | (self.ram[pa+1] << 16) |
                    (self.ram[pa+2] << 8) | self.ram[pa+3])
        # HW register space
        if addr >= 0xCC000000 and addr < 0xCD000000:
            if self.hw_read32_cb is not None:
                return <uint32_t>self.hw_read32_cb(addr)
        return 0

    cdef uint16_t read16(self, uint32_t addr):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa + 1 < self.ram_size:
            return (self.ram[pa] << 8) | self.ram[pa+1]
        if addr >= 0xCC000000 and addr < 0xCD000000:
            if self.hw_read32_cb is not None:
                return <uint16_t>(self.hw_read32_cb(addr) & 0xFFFF)
        return 0

    cdef uint8_t read8(self, uint32_t addr):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa < self.ram_size:
            return self.ram[pa]
        return 0

    cdef void write32(self, uint32_t addr, uint32_t val):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa + 3 < self.ram_size:
            self.ram[pa]   = (val >> 24) & 0xFF
            self.ram[pa+1] = (val >> 16) & 0xFF
            self.ram[pa+2] = (val >> 8) & 0xFF
            self.ram[pa+3] = val & 0xFF
            return
        if addr >= 0xCC000000 and addr < 0xCD000000:
            if self.hw_write32_cb is not None:
                self.hw_write32_cb(addr, val)

    cdef void write16(self, uint32_t addr, uint16_t val):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa + 1 < self.ram_size:
            self.ram[pa]   = (val >> 8) & 0xFF
            self.ram[pa+1] = val & 0xFF
            return
        if addr >= 0xCC000000 and addr < 0xCD000000:
            if self.hw_write32_cb is not None:
                self.hw_write32_cb(addr, <uint32_t>val)

    cdef void write8(self, uint32_t addr, uint8_t val):
        cdef uint32_t pa = self._translate(addr)
        if pa != 0xFFFFFFFF and pa < self.ram_size:
            self.ram[pa] = val
            return

    # --- CR helpers -------------------------------------------------------
    cdef inline void set_cr_field(self, int field, uint32_t val) noexcept nogil:
        cdef int shift = (7 - field) * 4
        self.cr = (self.cr & ~(<uint32_t>0xF << shift)) | ((val & 0xF) << shift)

    cdef inline void cmp_update_cr0(self, int32_t result) noexcept nogil:
        cdef uint32_t c = 0
        if result < 0:
            c = 8
        elif result > 0:
            c = 4
        else:
            c = 2
        if self.xer & 0x80000000:
            c |= 1
        self.set_cr_field(0, c)

    cdef inline void cmp_set_cr(self, int crfd, int32_t a, int32_t b) noexcept nogil:
        cdef uint32_t c = 0
        if a < b:   c = 8
        elif a > b: c = 4
        else:       c = 2
        if self.xer & 0x80000000: c |= 1
        self.set_cr_field(crfd, c)

    cdef inline void cmpl_set_cr(self, int crfd, uint32_t a, uint32_t b) noexcept nogil:
        cdef uint32_t c = 0
        if a < b:   c = 8
        elif a > b: c = 4
        else:       c = 2
        if self.xer & 0x80000000: c |= 1
        self.set_cr_field(crfd, c)

    # --- SPR access -------------------------------------------------------
    cdef uint32_t get_spr(self, uint32_t spr):
        if spr == 8:   return self.lr
        if spr == 9:   return self.ctr
        if spr == 1:   return self.xer
        if spr == 26:  return self.srr0
        if spr == 27:  return self.srr1
        if spr == 22:  return self.dec_reg
        if spr == 1008: return self.hid0
        if spr == 920:  return self.hid2
        if spr == 268: return self.tbl
        if spr == 269: return self.tbu
        if 272 <= spr <= 275:
            return self.sprg[spr - 272]
        if 912 <= spr <= 919:
            return self.gqr[spr - 912]
        return 0

    cdef void set_spr(self, uint32_t spr, uint32_t val):
        if spr == 8:   self.lr = val; return
        if spr == 9:   self.ctr = val; return
        if spr == 1:   self.xer = val; return
        if spr == 26:  self.srr0 = val; return
        if spr == 27:  self.srr1 = val; return
        if spr == 22:  self.dec_reg = val; return
        if spr == 1008: self.hid0 = val; return
        if spr == 920:  self.hid2 = val; return
        if 272 <= spr <= 275:
            self.sprg[spr - 272] = val; return
        if 912 <= spr <= 919:
            self.gqr[spr - 912] = val; return

    # --- Main execute loop -----------------------------------------------
    cpdef int run(self, int max_cycles):
        cdef uint32_t instr, opcode, rd, ra, rb, rs, rt
        cdef int32_t simm, result32
        cdef uint32_t uimm, xo, bo, bi, bd, target, ea, val
        cdef uint32_t sh, mb, me, m, rotated
        cdef int crfd, spr_raw, spr_num
        cdef int cycles_done = 0
        cdef bint rc, oe, aa, lk

        while cycles_done < max_cycles and not self.halted:
            instr = self.read32(self.pc)
            opcode = (instr >> 26) & 0x3F

            # ---- D-form: addi (14), addis (15) ----
            if opcode == 14:  # addi
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                if ra == 0:
                    self.gpr[rd] = <uint32_t>simm & MASK32
                else:
                    self.gpr[rd] = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 15:  # addis
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                val = (<uint32_t>simm << 16) & MASK32
                if ra == 0:
                    self.gpr[rd] = val
                else:
                    self.gpr[rd] = (self.gpr[ra] + val) & MASK32
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: ori (24), oris (25), xori (26), xoris (27) ----
            elif opcode == 24:  # ori
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] | uimm
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 25:  # oris
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] | (uimm << 16)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 26:  # xori
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] ^ uimm
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 27:  # xoris
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] ^ (uimm << 16)
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: andi. (28), andis. (29) ----
            elif opcode == 28:  # andi.
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] & uimm
                self.cmp_update_cr0(<int32_t>self.gpr[ra])
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 29:  # andis.
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.gpr[ra] = self.gpr[rs] & (uimm << 16)
                self.cmp_update_cr0(<int32_t>self.gpr[ra])
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: compare immediate ----
            elif opcode == 11:  # cmpi (cmpwi)
                crfd = (instr >> 23) & 0x7
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                self.cmp_set_cr(crfd, <int32_t>self.gpr[ra], simm)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 10:  # cmpli (cmplwi)
                crfd = (instr >> 23) & 0x7
                ra = (instr >> 16) & 0x1F
                uimm = instr & 0xFFFF
                self.cmpl_set_cr(crfd, self.gpr[ra], uimm)
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: addic (12), addic. (13) ----
            elif opcode == 12:  # addic
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                val = (self.gpr[ra] + <uint32_t>simm) & MASK32
                # Set CA
                if <uint64_t>self.gpr[ra] + <uint64_t><uint32_t>simm > MASK32:
                    self.xer |= 0x20000000
                else:
                    self.xer &= ~<uint32_t>0x20000000
                self.gpr[rd] = val
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 13:  # addic.
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                val = (self.gpr[ra] + <uint32_t>simm) & MASK32
                if <uint64_t>self.gpr[ra] + <uint64_t><uint32_t>simm > MASK32:
                    self.xer |= 0x20000000
                else:
                    self.xer &= ~<uint32_t>0x20000000
                self.gpr[rd] = val
                self.cmp_update_cr0(<int32_t>val)
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: mulli (7) ----
            elif opcode == 7:  # mulli
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                self.gpr[rd] = (<uint32_t>(<int32_t>self.gpr[ra] * simm)) & MASK32
                self.pc = (self.pc + 4) & MASK32

            # ---- D-form: subfic (8) ----
            elif opcode == 8:  # subfic
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                val = (<uint32_t>simm - self.gpr[ra]) & MASK32
                # CA: carry out of ~rA + simm + 1
                if <uint64_t>(~self.gpr[ra] & MASK32) + <uint64_t><uint32_t>simm + 1 > MASK32:
                    self.xer |= 0x20000000
                else:
                    self.xer &= ~<uint32_t>0x20000000
                self.gpr[rd] = val
                self.pc = (self.pc + 4) & MASK32

            # ---- I-form: b/bl (18) ----
            elif opcode == 18:
                aa = (instr >> 1) & 1
                lk = instr & 1
                target = instr & 0x03FFFFFC
                if target & 0x02000000:
                    target |= 0xFC000000
                if lk:
                    self.lr = (self.pc + 4) & MASK32
                if aa:
                    self.pc = target & MASK32
                else:
                    self.pc = (self.pc + <int32_t>target) & MASK32

            # ---- B-form: bc/bcl (16) ----
            elif opcode == 16:
                bo = (instr >> 21) & 0x1F
                bi = (instr >> 16) & 0x1F
                bd = instr & 0xFFFC
                if bd & 0x8000:
                    bd |= 0xFFFF0000
                aa = (instr >> 1) & 1
                lk = instr & 1
                # Decrement CTR if BO[2] == 0
                if not (bo & 4):
                    self.ctr = (self.ctr - 1) & MASK32
                # Evaluate conditions
                cdef bint ctr_ok = True
                cdef bint cond_ok = True
                if not (bo & 4):
                    if bo & 2:
                        ctr_ok = (self.ctr == 0)
                    else:
                        ctr_ok = (self.ctr != 0)
                if not (bo & 16):
                    cdef uint32_t cr_bit = (self.cr >> (31 - bi)) & 1
                    if bo & 8:
                        cond_ok = (cr_bit == 1)
                    else:
                        cond_ok = (cr_bit == 0)
                if lk:
                    self.lr = (self.pc + 4) & MASK32
                if ctr_ok and cond_ok:
                    if aa:
                        self.pc = bd & MASK32
                    else:
                        self.pc = (self.pc + <int32_t>bd) & MASK32
                else:
                    self.pc = (self.pc + 4) & MASK32

            # ---- XL-form: extended opcode 19 ----
            elif opcode == 19:
                xo = (instr >> 1) & 0x3FF
                if xo == 16:  # bclr
                    bo = (instr >> 21) & 0x1F
                    bi = (instr >> 16) & 0x1F
                    lk = instr & 1
                    if not (bo & 4):
                        self.ctr = (self.ctr - 1) & MASK32
                    ctr_ok = True; cond_ok = True
                    if not (bo & 4):
                        ctr_ok = (self.ctr == 0) if (bo & 2) else (self.ctr != 0)
                    if not (bo & 16):
                        cr_bit = (self.cr >> (31 - bi)) & 1
                        cond_ok = (cr_bit == 1) if (bo & 8) else (cr_bit == 0)
                    target = self.lr & 0xFFFFFFFC
                    if lk:
                        self.lr = (self.pc + 4) & MASK32
                    if ctr_ok and cond_ok:
                        self.pc = target
                    else:
                        self.pc = (self.pc + 4) & MASK32

                elif xo == 528:  # bcctr
                    bo = (instr >> 21) & 0x1F
                    bi = (instr >> 16) & 0x1F
                    lk = instr & 1
                    cond_ok = True
                    if not (bo & 16):
                        cr_bit = (self.cr >> (31 - bi)) & 1
                        cond_ok = (cr_bit == 1) if (bo & 8) else (cr_bit == 0)
                    if lk:
                        self.lr = (self.pc + 4) & MASK32
                    if cond_ok:
                        self.pc = self.ctr & 0xFFFFFFFC
                    else:
                        self.pc = (self.pc + 4) & MASK32

                elif xo == 150:  # isync
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 0:  # mcrf
                    crfd = (instr >> 23) & 7
                    cdef int crfs = (instr >> 18) & 7
                    cdef uint32_t crval = (self.cr >> ((7 - crfs) * 4)) & 0xF
                    self.set_cr_field(crfd, crval)
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 257:  # crand
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    val = ((self.cr >> (31-ra)) & 1) & ((self.cr >> (31-rb)) & 1)
                    self.cr = (self.cr & ~(<uint32_t>1 << (31-rd))) | (val << (31-rd))
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 449:  # cror
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    val = ((self.cr >> (31-ra)) & 1) | ((self.cr >> (31-rb)) & 1)
                    self.cr = (self.cr & ~(<uint32_t>1 << (31-rd))) | (val << (31-rd))
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 193:  # crxor
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    val = ((self.cr >> (31-ra)) & 1) ^ ((self.cr >> (31-rb)) & 1)
                    self.cr = (self.cr & ~(<uint32_t>1 << (31-rd))) | (val << (31-rd))
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 33:  # crnor
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    val = ~(((self.cr >> (31-ra)) & 1) | ((self.cr >> (31-rb)) & 1)) & 1
                    self.cr = (self.cr & ~(<uint32_t>1 << (31-rd))) | (val << (31-rd))
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 50:  # rfi
                    self.msr = self.srr1
                    self.pc = self.srr0 & 0xFFFFFFFC
                else:
                    self.pc = (self.pc + 4) & MASK32

            # ---- M-form: rlwinm (21), rlwimi (20), rlwnm (23) ----
            elif opcode == 21:  # rlwinm
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                sh = (instr >> 11) & 0x1F
                mb = (instr >> 6) & 0x1F
                me = (instr >> 1) & 0x1F
                rc = instr & 1
                rotated = rotl32(self.gpr[rs], sh)
                m = mask32(mb, me)
                self.gpr[ra] = rotated & m
                if rc:
                    self.cmp_update_cr0(<int32_t>self.gpr[ra])
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 20:  # rlwimi
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                sh = (instr >> 11) & 0x1F
                mb = (instr >> 6) & 0x1F
                me = (instr >> 1) & 0x1F
                rc = instr & 1
                rotated = rotl32(self.gpr[rs], sh)
                m = mask32(mb, me)
                self.gpr[ra] = (rotated & m) | (self.gpr[ra] & ~m)
                if rc:
                    self.cmp_update_cr0(<int32_t>self.gpr[ra])
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 23:  # rlwnm
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                rb = (instr >> 11) & 0x1F
                mb = (instr >> 6) & 0x1F
                me = (instr >> 1) & 0x1F
                rc = instr & 1
                rotated = rotl32(self.gpr[rs], self.gpr[rb] & 31)
                m = mask32(mb, me)
                self.gpr[ra] = rotated & m
                if rc:
                    self.cmp_update_cr0(<int32_t>self.gpr[ra])
                self.pc = (self.pc + 4) & MASK32

            # ---- Load/Store D-form ----
            elif opcode == 32:  # lwz
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.gpr[rd] = self.read32(ea & MASK32)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 33:  # lwzu
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.gpr[rd] = self.read32(ea)
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 34:  # lbz
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.gpr[rd] = self.read8(ea & MASK32)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 35:  # lbzu
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.gpr[rd] = self.read8(ea)
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 40:  # lhz
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.gpr[rd] = self.read16(ea & MASK32)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 41:  # lhzu
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.gpr[rd] = self.read16(ea)
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 42:  # lha (load halfword algebraic)
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                val = self.read16(ea & MASK32)
                self.gpr[rd] = <uint32_t>sign_extend_16(val)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 36:  # stw
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.write32(ea & MASK32, self.gpr[rs])
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 37:  # stwu
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.write32(ea, self.gpr[rs])
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 38:  # stb
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.write8(ea & MASK32, self.gpr[rs] & 0xFF)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 39:  # stbu
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.write8(ea, self.gpr[rs] & 0xFF)
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 44:  # sth
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                self.write16(ea & MASK32, self.gpr[rs] & 0xFFFF)
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 45:  # sthu
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (self.gpr[ra] + <uint32_t>simm) & MASK32
                self.write16(ea, self.gpr[rs] & 0xFFFF)
                self.gpr[ra] = ea
                self.pc = (self.pc + 4) & MASK32

            # ---- lmw (46) / stmw (47) ----
            elif opcode == 46:  # lmw
                rd = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                while rd < 32:
                    self.gpr[rd] = self.read32(ea & MASK32)
                    ea = (ea + 4) & MASK32
                    rd += 1
                self.pc = (self.pc + 4) & MASK32

            elif opcode == 47:  # stmw
                rs = (instr >> 21) & 0x1F
                ra = (instr >> 16) & 0x1F
                simm = sign_extend_16(instr & 0xFFFF)
                ea = (0 if ra == 0 else self.gpr[ra]) + <uint32_t>simm
                while rs < 32:
                    self.write32(ea & MASK32, self.gpr[rs])
                    ea = (ea + 4) & MASK32
                    rs += 1
                self.pc = (self.pc + 4) & MASK32

            # ---- FP load/store (stub: just move bits) ----
            elif opcode == 50:  # lfd
                self.pc = (self.pc + 4) & MASK32
            elif opcode == 54:  # stfd
                self.pc = (self.pc + 4) & MASK32
            elif opcode == 48:  # lfs
                self.pc = (self.pc + 4) & MASK32
            elif opcode == 52:  # stfs
                self.pc = (self.pc + 4) & MASK32

            # ---- Extended opcode 31 ----
            elif opcode == 31:
                xo = (instr >> 1) & 0x3FF
                rc = instr & 1

                if xo == 266:  # add
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[rd] = (self.gpr[ra] + self.gpr[rb]) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 40:  # subf (rd = rb - ra)
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[rd] = (self.gpr[rb] - self.gpr[ra]) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 10:  # addc
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    cdef uint64_t res64 = <uint64_t>self.gpr[ra] + <uint64_t>self.gpr[rb]
                    self.gpr[rd] = <uint32_t>(res64 & MASK32)
                    if res64 > MASK32:
                        self.xer |= 0x20000000
                    else:
                        self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 138:  # adde
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    cdef uint32_t ca_in = 1 if (self.xer & 0x20000000) else 0
                    res64 = <uint64_t>self.gpr[ra] + <uint64_t>self.gpr[rb] + ca_in
                    self.gpr[rd] = <uint32_t>(res64 & MASK32)
                    if res64 > MASK32:
                        self.xer |= 0x20000000
                    else:
                        self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 234:  # addme
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    ca_in = 1 if (self.xer & 0x20000000) else 0
                    res64 = <uint64_t>self.gpr[ra] + <uint64_t>MASK32 + ca_in
                    self.gpr[rd] = <uint32_t>(res64 & MASK32)
                    if res64 > MASK32:
                        self.xer |= 0x20000000
                    else:
                        self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 202:  # addze
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    ca_in = 1 if (self.xer & 0x20000000) else 0
                    res64 = <uint64_t>self.gpr[ra] + ca_in
                    self.gpr[rd] = <uint32_t>(res64 & MASK32)
                    if res64 > MASK32:
                        self.xer |= 0x20000000
                    else:
                        self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 104:  # neg
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    self.gpr[rd] = (~self.gpr[ra] + 1) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 235:  # mullw
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[rd] = (<uint32_t>(<int32_t>self.gpr[ra] * <int32_t>self.gpr[rb])) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 75:  # mulhw
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    cdef int64_t mres = <int64_t><int32_t>self.gpr[ra] * <int64_t><int32_t>self.gpr[rb]
                    self.gpr[rd] = <uint32_t>((mres >> 32) & MASK32)
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 11:  # mulhwu
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    cdef uint64_t umres = <uint64_t>self.gpr[ra] * <uint64_t>self.gpr[rb]
                    self.gpr[rd] = <uint32_t>((umres >> 32) & MASK32)
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 491:  # divw
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    if self.gpr[rb] != 0:
                        self.gpr[rd] = <uint32_t>(<int32_t>self.gpr[ra] / <int32_t>self.gpr[rb]) & MASK32
                    else:
                        self.gpr[rd] = 0
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 459:  # divwu
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    if self.gpr[rb] != 0:
                        self.gpr[rd] = (self.gpr[ra] / self.gpr[rb]) & MASK32
                    else:
                        self.gpr[rd] = 0
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[rd])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 28:  # and
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = self.gpr[rs] & self.gpr[rb]
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 60:  # andc
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = self.gpr[rs] & (~self.gpr[rb] & MASK32)
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 444:  # or (also mr)
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = self.gpr[rs] | self.gpr[rb]
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 412:  # orc
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = self.gpr[rs] | (~self.gpr[rb] & MASK32)
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 316:  # xor
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = self.gpr[rs] ^ self.gpr[rb]
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 476:  # nand
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = ~(self.gpr[rs] & self.gpr[rb]) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 124:  # nor
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = ~(self.gpr[rs] | self.gpr[rb]) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 284:  # eqv
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.gpr[ra] = ~(self.gpr[rs] ^ self.gpr[rb]) & MASK32
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 24:  # slw
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    sh = self.gpr[rb] & 0x3F
                    self.gpr[ra] = (self.gpr[rs] << sh) & MASK32 if sh < 32 else 0
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 536:  # srw
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    sh = self.gpr[rb] & 0x3F
                    self.gpr[ra] = (self.gpr[rs] >> sh) if sh < 32 else 0
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 792:  # sraw
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    sh = self.gpr[rb] & 0x3F
                    if sh < 32:
                        result32 = <int32_t>self.gpr[rs] >> sh
                        self.gpr[ra] = <uint32_t>result32
                        if (<int32_t>self.gpr[rs] < 0) and (self.gpr[rs] & ((1 << sh) - 1)):
                            self.xer |= 0x20000000
                        else:
                            self.xer &= ~<uint32_t>0x20000000
                    else:
                        if <int32_t>self.gpr[rs] < 0:
                            self.gpr[ra] = MASK32
                            self.xer |= 0x20000000
                        else:
                            self.gpr[ra] = 0
                            self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 824:  # srawi
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    sh = (instr >> 11) & 0x1F
                    result32 = <int32_t>self.gpr[rs] >> sh
                    self.gpr[ra] = <uint32_t>result32
                    if (<int32_t>self.gpr[rs] < 0) and sh > 0 and (self.gpr[rs] & ((1 << sh) - 1)):
                        self.xer |= 0x20000000
                    else:
                        self.xer &= ~<uint32_t>0x20000000
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 26:  # cntlzw
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    val = self.gpr[rs]
                    cdef int n = 0
                    if val == 0:
                        n = 32
                    else:
                        while not (val & 0x80000000):
                            val <<= 1
                            n += 1
                    self.gpr[ra] = n
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 954:  # extsb
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    val = self.gpr[rs] & 0xFF
                    if val & 0x80:
                        val |= 0xFFFFFF00
                    self.gpr[ra] = val
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 922:  # extsh
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    val = self.gpr[rs] & 0xFFFF
                    if val & 0x8000:
                        val |= 0xFFFF0000
                    self.gpr[ra] = val
                    if rc: self.cmp_update_cr0(<int32_t>self.gpr[ra])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 0:  # cmp
                    crfd = (instr >> 23) & 7
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.cmp_set_cr(crfd, <int32_t>self.gpr[ra], <int32_t>self.gpr[rb])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 32:  # cmpl
                    crfd = (instr >> 23) & 7
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    self.cmpl_set_cr(crfd, self.gpr[ra], self.gpr[rb])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 339:  # mfspr
                    rd = (instr >> 21) & 0x1F
                    spr_raw = ((instr >> 16) & 0x1F) | (((instr >> 11) & 0x1F) << 5)
                    self.gpr[rd] = self.get_spr(spr_raw)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 467:  # mtspr
                    rs = (instr >> 21) & 0x1F
                    spr_raw = ((instr >> 16) & 0x1F) | (((instr >> 11) & 0x1F) << 5)
                    self.set_spr(spr_raw, self.gpr[rs])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 19:  # mfcr
                    rd = (instr >> 21) & 0x1F
                    self.gpr[rd] = self.cr
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 144:  # mtcrf
                    rs = (instr >> 21) & 0x1F
                    cdef uint32_t crm = (instr >> 12) & 0xFF
                    cdef uint32_t cr_mask = 0
                    cdef int fi
                    for fi in range(8):
                        if crm & (1 << (7 - fi)):
                            cr_mask |= <uint32_t>0xF << ((7 - fi) * 4)
                    self.cr = (self.gpr[rs] & cr_mask) | (self.cr & ~cr_mask)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 83:  # mfmsr
                    rd = (instr >> 21) & 0x1F
                    self.gpr[rd] = self.msr
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 146:  # mtmsr
                    rs = (instr >> 21) & 0x1F
                    self.msr = self.gpr[rs]
                    self.pc = (self.pc + 4) & MASK32

                # X-form load/store indexed
                elif xo == 23:  # lwzx
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.gpr[rd] = self.read32(ea & MASK32)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 151:  # stwx
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.write32(ea & MASK32, self.gpr[rs])
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 87:  # lbzx
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.gpr[rd] = self.read8(ea & MASK32)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 215:  # stbx
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.write8(ea & MASK32, self.gpr[rs] & 0xFF)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 279:  # lhzx
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.gpr[rd] = self.read16(ea & MASK32)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 407:  # sthx
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    self.write16(ea & MASK32, self.gpr[rs] & 0xFFFF)
                    self.pc = (self.pc + 4) & MASK32

                elif xo == 343:  # lhax
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    val = self.read16(ea & MASK32)
                    self.gpr[rd] = <uint32_t>sign_extend_16(val)
                    self.pc = (self.pc + 4) & MASK32

                # Cache / sync / TLB (NOPs for now)
                elif xo == 598 or xo == 470 or xo == 54 or xo == 86:
                    # dcbi, dcbi, dcbst, dcbf
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 246 or xo == 1014 or xo == 982:
                    # dcbtst, dcbz, icbi
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 566 or xo == 595 or xo == 370:
                    # tlbsync, mfsr, tlbia
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 595:  # mfsr
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 210:  # mtsr
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 242:  # mtsrin
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 306:  # tlbie
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 278:  # dcbt (hint)
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 4:    # tw (trap word - just skip for now)
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 534:  # lwbrx
                    rd = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    val = self.read32(ea & MASK32)
                    # Byte-reverse
                    self.gpr[rd] = ((val & 0xFF) << 24) | ((val & 0xFF00) << 8) | ((val >> 8) & 0xFF00) | ((val >> 24) & 0xFF)
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 662:  # stwbrx
                    rs = (instr >> 21) & 0x1F
                    ra = (instr >> 16) & 0x1F
                    rb = (instr >> 11) & 0x1F
                    ea = (0 if ra == 0 else self.gpr[ra]) + self.gpr[rb]
                    val = self.gpr[rs]
                    val = ((val & 0xFF) << 24) | ((val & 0xFF00) << 8) | ((val >> 8) & 0xFF00) | ((val >> 24) & 0xFF)
                    self.write32(ea & MASK32, val)
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 598:  # sync
                    self.pc = (self.pc + 4) & MASK32
                elif xo == 854:  # eieio
                    self.pc = (self.pc + 4) & MASK32
                else:
                    # Unknown XO=31 sub-opcode — skip
                    self.pc = (self.pc + 4) & MASK32

            # ---- FP opcode 59 / 63 (stubs) ----
            elif opcode == 59 or opcode == 63:
                self.pc = (self.pc + 4) & MASK32

            # ---- sc (17) ----
            elif opcode == 17:  # sc (system call)
                self.srr0 = (self.pc + 4) & MASK32
                self.srr1 = self.msr
                self.pc = 0x80000C00  # syscall vector
                self.msr &= ~<uint32_t>0x0000EE70  # clear EE, PR, IR, DR etc.

            # ---- twi (3) — trap word immediate ----
            elif opcode == 3:
                self.pc = (self.pc + 4) & MASK32  # skip

            else:
                # Unknown primary opcode — skip
                self.pc = (self.pc + 4) & MASK32

            cycles_done += 1
            self.cycles += 1
            self.tbl = <uint32_t>(self.cycles & MASK32)
            self.tbu = <uint32_t>((self.cycles >> 32) & MASK32)

        return cycles_done
'''

# ======================================================================
# Cython compilation (auto-compile on first run, cache .so)
# ======================================================================
_CY_CORE = None

def _try_compile_cython() -> Optional[Any]:
    """Attempt to compile embedded Cython source. Returns module or None."""
    global _CY_CORE
    if _CY_CORE is not None:
        return _CY_CORE
    try:
        from Cython.Build import cythonize
        import sysconfig
        from distutils.core import Distribution, Extension
        from distutils.command.build_ext import build_ext

        src_hash = hashlib.md5(CYTHON_SRC.encode()).hexdigest()[:12]
        cache_dir = os.path.join(tempfile.gettempdir(), f"ac_dolphin_cy_{src_hash}")
        mod_name = "cy_gekko"
        so_glob = os.path.join(cache_dir, mod_name + "*.so")

        # Check cache
        import glob
        cached = glob.glob(so_glob)
        if not cached:
            cached = glob.glob(os.path.join(cache_dir, mod_name + "*.pyd"))
        if cached:
            sys.path.insert(0, cache_dir)
            mod = importlib.import_module(mod_name)
            _CY_CORE = mod
            return mod

        os.makedirs(cache_dir, exist_ok=True)
        pyx_path = os.path.join(cache_dir, mod_name + ".pyx")
        with open(pyx_path, "w") as f:
            f.write(CYTHON_SRC)

        ext = Extension(mod_name, [pyx_path])
        dist = Distribution({"ext_modules": cythonize([ext], language_level=3,
                                                       compiler_directives={"boundscheck": False,
                                                                            "wraparound": False})})
        dist.ext_modules = cythonize([ext], language_level=3)
        cmd = build_ext(dist)
        cmd.build_lib = cache_dir
        cmd.build_temp = os.path.join(cache_dir, "tmp")
        cmd.ensure_finalized()
        cmd.run()

        sys.path.insert(0, cache_dir)
        mod = importlib.import_module(mod_name)
        _CY_CORE = mod
        return mod

    except Exception as e:
        print(f"[AC'S Dolphin] Cython compile failed ({e}), using pure Python core")
        return None


# ======================================================================
# Pure-Python Gekko CPU (fallback)
# ======================================================================
def _sign16(v: int) -> int:
    return v - 0x10000 if v & 0x8000 else v

def _sign26(v: int) -> int:
    return v - 0x4000000 if v & 0x2000000 else v

def _rotl32(v: int, n: int) -> int:
    n &= 31
    return ((v << n) | (v >> (32 - n))) & MASK32

def _mask32(mb: int, me: int) -> int:
    if mb <= me:
        return (MASK32 >> mb) & (MASK32 << (31 - me))
    return (MASK32 >> mb) | (MASK32 << (31 - me))

class PyGekko:
    """Pure-Python PowerPC 750CL (Gekko) CPU core."""
    __slots__ = (
        "gpr", "fpr", "pc", "lr", "ctr", "cr", "xer", "msr",
        "srr0", "srr1", "sprg", "hid0", "hid2", "dec_reg",
        "tbl", "tbu", "fpscr", "gqr", "cycles", "halted",
        "_ram", "_hw_r32", "_hw_w32",
    )

    def __init__(self):
        self._ram: Optional[bytearray] = None
        self._hw_r32: Optional[Callable] = None
        self._hw_w32: Optional[Callable] = None
        self.reset()

    def reset(self):
        self.gpr = [0] * 32
        self.fpr = [0.0] * 32
        self.pc = 0; self.lr = 0; self.ctr = 0
        self.cr = 0; self.xer = 0; self.msr = 0
        self.srr0 = 0; self.srr1 = 0
        self.sprg = [0] * 4; self.gqr = [0] * 8
        self.hid0 = 0; self.hid2 = 0; self.dec_reg = 0
        self.tbl = 0; self.tbu = 0; self.fpscr = 0
        self.cycles = 0; self.halted = False

    def set_ram(self, buf: bytearray):
        self._ram = buf

    def set_hw_callbacks(self, r32, w32):
        self._hw_r32 = r32; self._hw_w32 = w32

    # ---- memory helpers ----
    def _xlat(self, a: int) -> int:
        sz = len(self._ram)
        if 0x80000000 <= a < 0x80000000 + sz: return a - 0x80000000
        if 0xC0000000 <= a < 0xC0000000 + sz: return a - 0xC0000000
        if a < sz: return a
        return -1

    def read32(self, a: int) -> int:
        p = self._xlat(a)
        if p >= 0 and p + 3 < len(self._ram):
            return (self._ram[p] << 24) | (self._ram[p+1] << 16) | (self._ram[p+2] << 8) | self._ram[p+3]
        if 0xCC000000 <= a < 0xCD000000 and self._hw_r32:
            return self._hw_r32(a) & MASK32
        return 0

    def read16(self, a: int) -> int:
        p = self._xlat(a)
        if p >= 0 and p + 1 < len(self._ram):
            return (self._ram[p] << 8) | self._ram[p+1]
        if 0xCC000000 <= a < 0xCD000000 and self._hw_r32:
            return self._hw_r32(a) & 0xFFFF
        return 0

    def read8(self, a: int) -> int:
        p = self._xlat(a)
        if p >= 0 and p < len(self._ram):
            return self._ram[p]
        return 0

    def write32(self, a: int, v: int):
        p = self._xlat(a)
        if p >= 0 and p + 3 < len(self._ram):
            self._ram[p]   = (v >> 24) & 0xFF
            self._ram[p+1] = (v >> 16) & 0xFF
            self._ram[p+2] = (v >> 8) & 0xFF
            self._ram[p+3] = v & 0xFF
            return
        if 0xCC000000 <= a < 0xCD000000 and self._hw_w32:
            self._hw_w32(a, v)

    def write16(self, a: int, v: int):
        p = self._xlat(a)
        if p >= 0 and p + 1 < len(self._ram):
            self._ram[p]   = (v >> 8) & 0xFF
            self._ram[p+1] = v & 0xFF
            return
        if 0xCC000000 <= a < 0xCD000000 and self._hw_w32:
            self._hw_w32(a, v & 0xFFFF)

    def write8(self, a: int, v: int):
        p = self._xlat(a)
        if p >= 0 and p < len(self._ram):
            self._ram[p] = v & 0xFF

    # ---- CR helpers ----
    def _set_cr_field(self, f: int, v: int):
        s = (7 - f) * 4
        self.cr = (self.cr & ~(0xF << s)) | ((v & 0xF) << s)

    def _cmp_cr0(self, r: int):
        r = r if r < 0x80000000 else r - 0x100000000
        c = 8 if r < 0 else (4 if r > 0 else 2)
        if self.xer & 0x80000000: c |= 1
        self._set_cr_field(0, c)

    def _cmp_cr(self, f: int, a: int, b: int):
        a = a if a < 0x80000000 else a - 0x100000000
        b = b if b < 0x80000000 else b - 0x100000000
        c = 8 if a < b else (4 if a > b else 2)
        if self.xer & 0x80000000: c |= 1
        self._set_cr_field(f, c)

    def _cmpl_cr(self, f: int, a: int, b: int):
        c = 8 if a < b else (4 if a > b else 2)
        if self.xer & 0x80000000: c |= 1
        self._set_cr_field(f, c)

    # ---- SPR ----
    def _get_spr(self, n: int) -> int:
        if n == 8:  return self.lr
        if n == 9:  return self.ctr
        if n == 1:  return self.xer
        if n == 26: return self.srr0
        if n == 27: return self.srr1
        if n == 22: return self.dec_reg
        if n == 1008: return self.hid0
        if n == 920:  return self.hid2
        if n == 268: return self.tbl
        if n == 269: return self.tbu
        if 272 <= n <= 275: return self.sprg[n - 272]
        if 912 <= n <= 919: return self.gqr[n - 912]
        return 0

    def _set_spr(self, n: int, v: int):
        if n == 8:  self.lr = v
        elif n == 9:  self.ctr = v
        elif n == 1:  self.xer = v
        elif n == 26: self.srr0 = v
        elif n == 27: self.srr1 = v
        elif n == 22: self.dec_reg = v
        elif n == 1008: self.hid0 = v
        elif n == 920:  self.hid2 = v
        elif 272 <= n <= 275: self.sprg[n - 272] = v
        elif 912 <= n <= 919: self.gqr[n - 912] = v

    # ---- Main execute loop ----
    def run(self, max_cycles: int) -> int:
        gpr = self.gpr; ram = self._ram; M = MASK32
        done = 0
        while done < max_cycles and not self.halted:
            instr = self.read32(self.pc)
            op = (instr >> 26) & 0x3F

            if op == 14:  # addi
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                s = _sign16(instr & 0xFFFF)
                gpr[d] = (s if a == 0 else gpr[a] + s) & M
                self.pc = (self.pc + 4) & M
            elif op == 15:  # addis
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                v = (_sign16(instr & 0xFFFF) << 16) & M
                gpr[d] = (v if a == 0 else (gpr[a] + v) & M)
                self.pc = (self.pc + 4) & M
            elif op == 24:  # ori
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] | (instr & 0xFFFF)
                self.pc = (self.pc + 4) & M
            elif op == 25:  # oris
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] | ((instr & 0xFFFF) << 16)
                self.pc = (self.pc + 4) & M
            elif op == 26:  # xori
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] ^ (instr & 0xFFFF)
                self.pc = (self.pc + 4) & M
            elif op == 27:  # xoris
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] ^ ((instr & 0xFFFF) << 16)
                self.pc = (self.pc + 4) & M
            elif op == 28:  # andi.
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] & (instr & 0xFFFF)
                self._cmp_cr0(gpr[a])
                self.pc = (self.pc + 4) & M
            elif op == 29:  # andis.
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                gpr[a] = gpr[s] & ((instr & 0xFFFF) << 16)
                self._cmp_cr0(gpr[a])
                self.pc = (self.pc + 4) & M
            elif op == 11:  # cmpi
                f = (instr >> 23) & 7; a = (instr >> 16) & 0x1F
                self._cmp_cr(f, gpr[a], _sign16(instr & 0xFFFF) & M)
                self.pc = (self.pc + 4) & M
            elif op == 10:  # cmpli
                f = (instr >> 23) & 7; a = (instr >> 16) & 0x1F
                self._cmpl_cr(f, gpr[a], instr & 0xFFFF)
                self.pc = (self.pc + 4) & M
            elif op == 7:  # mulli
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                sa = gpr[a] if gpr[a] < 0x80000000 else gpr[a] - 0x100000000
                gpr[d] = (sa * _sign16(instr & 0xFFFF)) & M
                self.pc = (self.pc + 4) & M
            elif op == 12 or op == 13:  # addic / addic.
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                s = _sign16(instr & 0xFFFF)
                r64 = gpr[a] + (s & M)
                gpr[d] = r64 & M
                self.xer = (self.xer | 0x20000000) if r64 > M else (self.xer & ~0x20000000)
                if op == 13: self._cmp_cr0(gpr[d])
                self.pc = (self.pc + 4) & M
            elif op == 8:  # subfic
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                s = _sign16(instr & 0xFFFF)
                gpr[d] = ((s & M) - gpr[a]) & M
                self.pc = (self.pc + 4) & M
            elif op == 18:  # b/bl
                aa = (instr >> 1) & 1; lk = instr & 1
                t = instr & 0x03FFFFFC
                if t & 0x02000000: t |= 0xFC000000
                if lk: self.lr = (self.pc + 4) & M
                self.pc = (t & M) if aa else ((self.pc + _sign26(t)) & M)
            elif op == 16:  # bc
                bo = (instr >> 21) & 0x1F; bi = (instr >> 16) & 0x1F
                bd = instr & 0xFFFC
                if bd & 0x8000: bd |= 0xFFFF0000
                aa = (instr >> 1) & 1; lk = instr & 1
                if not (bo & 4): self.ctr = (self.ctr - 1) & M
                ctr_ok = True if (bo & 4) else ((self.ctr == 0) if (bo & 2) else (self.ctr != 0))
                cond_ok = True if (bo & 16) else (((self.cr >> (31 - bi)) & 1) == (1 if (bo & 8) else 0))
                if lk: self.lr = (self.pc + 4) & M
                if ctr_ok and cond_ok:
                    self.pc = (bd & M) if aa else ((self.pc + _sign16(bd & 0xFFFF)) & M)
                else:
                    self.pc = (self.pc + 4) & M
            elif op == 19:  # XL
                xo = (instr >> 1) & 0x3FF
                if xo == 16:  # bclr
                    bo = (instr >> 21) & 0x1F; bi = (instr >> 16) & 0x1F; lk = instr & 1
                    if not (bo & 4): self.ctr = (self.ctr - 1) & M
                    ctr_ok = True if (bo & 4) else ((self.ctr == 0) if (bo & 2) else (self.ctr != 0))
                    cond_ok = True if (bo & 16) else (((self.cr >> (31 - bi)) & 1) == (1 if (bo & 8) else 0))
                    tgt = self.lr & 0xFFFFFFFC
                    if lk: self.lr = (self.pc + 4) & M
                    self.pc = tgt if (ctr_ok and cond_ok) else (self.pc + 4) & M
                elif xo == 528:  # bcctr
                    bo = (instr >> 21) & 0x1F; bi = (instr >> 16) & 0x1F; lk = instr & 1
                    cond_ok = True if (bo & 16) else (((self.cr >> (31 - bi)) & 1) == (1 if (bo & 8) else 0))
                    if lk: self.lr = (self.pc + 4) & M
                    self.pc = (self.ctr & 0xFFFFFFFC) if cond_ok else (self.pc + 4) & M
                elif xo == 50:  # rfi
                    self.msr = self.srr1; self.pc = self.srr0 & 0xFFFFFFFC
                else:
                    self.pc = (self.pc + 4) & M
            elif op == 21:  # rlwinm
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                sh = (instr >> 11) & 0x1F; mb = (instr >> 6) & 0x1F; me = (instr >> 1) & 0x1F
                gpr[a] = _rotl32(gpr[s], sh) & _mask32(mb, me)
                if instr & 1: self._cmp_cr0(gpr[a])
                self.pc = (self.pc + 4) & M
            elif op == 20:  # rlwimi
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                sh = (instr >> 11) & 0x1F; mb = (instr >> 6) & 0x1F; me = (instr >> 1) & 0x1F
                m = _mask32(mb, me); r = _rotl32(gpr[s], sh)
                gpr[a] = (r & m) | (gpr[a] & ~m & M)
                if instr & 1: self._cmp_cr0(gpr[a])
                self.pc = (self.pc + 4) & M
            elif op == 23:  # rlwnm
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                b = (instr >> 11) & 0x1F; mb = (instr >> 6) & 0x1F; me = (instr >> 1) & 0x1F
                gpr[a] = _rotl32(gpr[s], gpr[b] & 31) & _mask32(mb, me)
                if instr & 1: self._cmp_cr0(gpr[a])
                self.pc = (self.pc + 4) & M
            # Load/store
            elif op == 32:  # lwz
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                gpr[d] = self.read32(ea & M)
                self.pc = (self.pc + 4) & M
            elif op == 33:  # lwzu
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (gpr[a] + _sign16(instr & 0xFFFF)) & M
                gpr[d] = self.read32(ea); gpr[a] = ea
                self.pc = (self.pc + 4) & M
            elif op == 34:  # lbz
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                gpr[d] = self.read8(ea & M)
                self.pc = (self.pc + 4) & M
            elif op == 35:  # lbzu
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (gpr[a] + _sign16(instr & 0xFFFF)) & M
                gpr[d] = self.read8(ea); gpr[a] = ea
                self.pc = (self.pc + 4) & M
            elif op == 40:  # lhz
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                gpr[d] = self.read16(ea & M)
                self.pc = (self.pc + 4) & M
            elif op == 42:  # lha
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                v = self.read16(ea & M)
                gpr[d] = _sign16(v) & M
                self.pc = (self.pc + 4) & M
            elif op == 36:  # stw
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                self.write32(ea & M, gpr[s])
                self.pc = (self.pc + 4) & M
            elif op == 37:  # stwu
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (gpr[a] + _sign16(instr & 0xFFFF)) & M
                self.write32(ea, gpr[s]); gpr[a] = ea
                self.pc = (self.pc + 4) & M
            elif op == 38:  # stb
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                self.write8(ea & M, gpr[s] & 0xFF)
                self.pc = (self.pc + 4) & M
            elif op == 44:  # sth
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                self.write16(ea & M, gpr[s] & 0xFFFF)
                self.pc = (self.pc + 4) & M
            elif op == 46:  # lmw
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                while d < 32:
                    gpr[d] = self.read32(ea & M); ea += 4; d += 1
                self.pc = (self.pc + 4) & M
            elif op == 47:  # stmw
                s = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F
                ea = (0 if a == 0 else gpr[a]) + _sign16(instr & 0xFFFF)
                while s < 32:
                    self.write32(ea & M, gpr[s]); ea += 4; s += 1
                self.pc = (self.pc + 4) & M
            elif op == 31:  # extended
                xo = (instr >> 1) & 0x3FF; rc = instr & 1
                d = (instr >> 21) & 0x1F; a = (instr >> 16) & 0x1F; b = (instr >> 11) & 0x1F
                if xo == 266:    gpr[d] = (gpr[a] + gpr[b]) & M
                elif xo == 40:   gpr[d] = (gpr[b] - gpr[a]) & M
                elif xo == 235:
                    sa = gpr[a] if gpr[a] < 0x80000000 else gpr[a] - 0x100000000
                    sb = gpr[b] if gpr[b] < 0x80000000 else gpr[b] - 0x100000000
                    gpr[d] = (sa * sb) & M
                elif xo == 491:
                    if gpr[b] != 0:
                        sa = gpr[a] if gpr[a] < 0x80000000 else gpr[a] - 0x100000000
                        sb = gpr[b] if gpr[b] < 0x80000000 else gpr[b] - 0x100000000
                        gpr[d] = int(sa / sb) & M
                    else: gpr[d] = 0
                elif xo == 104:  gpr[d] = (~gpr[a] + 1) & M
                elif xo == 28:   gpr[a] = gpr[d] & gpr[b]  # and: rS=d, rA=a, rB=b
                elif xo == 444:  gpr[a] = gpr[d] | gpr[b]  # or
                elif xo == 316:  gpr[a] = gpr[d] ^ gpr[b]  # xor
                elif xo == 476:  gpr[a] = ~(gpr[d] & gpr[b]) & M  # nand
                elif xo == 124:  gpr[a] = ~(gpr[d] | gpr[b]) & M  # nor
                elif xo == 60:   gpr[a] = gpr[d] & (~gpr[b] & M)  # andc
                elif xo == 412:  gpr[a] = gpr[d] | (~gpr[b] & M)  # orc
                elif xo == 284:  gpr[a] = ~(gpr[d] ^ gpr[b]) & M  # eqv
                elif xo == 24:   # slw
                    sh = gpr[b] & 0x3F
                    gpr[a] = (gpr[d] << sh) & M if sh < 32 else 0
                elif xo == 536:  # srw
                    sh = gpr[b] & 0x3F
                    gpr[a] = gpr[d] >> sh if sh < 32 else 0
                elif xo == 792:  # sraw
                    sh = gpr[b] & 0x3F
                    if sh < 32:
                        sv = gpr[d] if gpr[d] < 0x80000000 else gpr[d] - 0x100000000
                        gpr[a] = (sv >> sh) & M
                    else:
                        gpr[a] = M if gpr[d] & 0x80000000 else 0
                elif xo == 824:  # srawi
                    sh = b  # SH field is in rB position
                    sv = gpr[d] if gpr[d] < 0x80000000 else gpr[d] - 0x100000000
                    gpr[a] = (sv >> sh) & M
                elif xo == 26:   # cntlzw
                    v = gpr[d]; n = 0
                    if v == 0: n = 32
                    else:
                        while not (v & 0x80000000): v <<= 1; n += 1
                    gpr[a] = n
                elif xo == 954:  # extsb
                    v = gpr[d] & 0xFF
                    gpr[a] = (v | 0xFFFFFF00) if v & 0x80 else v
                elif xo == 922:  # extsh
                    v = gpr[d] & 0xFFFF
                    gpr[a] = (v | 0xFFFF0000) if v & 0x8000 else v
                elif xo == 0:    self._cmp_cr((instr >> 23) & 7, gpr[a], gpr[b])  # cmp
                elif xo == 32:   self._cmpl_cr((instr >> 23) & 7, gpr[a], gpr[b])  # cmpl
                elif xo == 339:  # mfspr
                    sn = (a) | (b << 5); gpr[d] = self._get_spr(sn)
                elif xo == 467:  # mtspr
                    sn = (a) | (b << 5); self._set_spr(sn, gpr[d])
                elif xo == 19:   gpr[d] = self.cr  # mfcr
                elif xo == 144:  # mtcrf
                    crm = (instr >> 12) & 0xFF; cm = 0
                    for fi in range(8):
                        if crm & (1 << (7 - fi)): cm |= 0xF << ((7 - fi) * 4)
                    self.cr = (gpr[d] & cm) | (self.cr & ~cm & M)
                elif xo == 83:   gpr[d] = self.msr  # mfmsr
                elif xo == 146:  self.msr = gpr[d]  # mtmsr
                # Indexed load/store
                elif xo == 23:   gpr[d] = self.read32(((0 if a == 0 else gpr[a]) + gpr[b]) & M)
                elif xo == 151:  self.write32(((0 if a == 0 else gpr[a]) + gpr[b]) & M, gpr[d])
                elif xo == 87:   gpr[d] = self.read8(((0 if a == 0 else gpr[a]) + gpr[b]) & M)
                elif xo == 215:  self.write8(((0 if a == 0 else gpr[a]) + gpr[b]) & M, gpr[d] & 0xFF)
                elif xo == 279:  gpr[d] = self.read16(((0 if a == 0 else gpr[a]) + gpr[b]) & M)
                elif xo == 407:  self.write16(((0 if a == 0 else gpr[a]) + gpr[b]) & M, gpr[d] & 0xFFFF)
                elif xo == 343:  # lhax
                    v = self.read16(((0 if a == 0 else gpr[a]) + gpr[b]) & M)
                    gpr[d] = _sign16(v) & M
                elif xo == 10:   # addc
                    r64 = gpr[a] + gpr[b]
                    gpr[d] = r64 & M
                    self.xer = (self.xer | 0x20000000) if r64 > M else (self.xer & ~0x20000000)
                elif xo == 138:  # adde
                    ca = 1 if (self.xer & 0x20000000) else 0
                    r64 = gpr[a] + gpr[b] + ca
                    gpr[d] = r64 & M
                    self.xer = (self.xer | 0x20000000) if r64 > M else (self.xer & ~0x20000000)
                elif xo == 202:  # addze
                    ca = 1 if (self.xer & 0x20000000) else 0
                    r64 = gpr[a] + ca
                    gpr[d] = r64 & M
                    self.xer = (self.xer | 0x20000000) if r64 > M else (self.xer & ~0x20000000)
                else:
                    pass  # cache/TLB/sync ops — NOP
                if rc and xo in (266, 40, 235, 491, 104, 28, 444, 316, 476,
                                  124, 60, 412, 284, 24, 536, 792, 824, 26, 954, 922):
                    self._cmp_cr0(gpr[a] if xo in (28, 444, 316, 476, 124, 60, 412,
                                                     284, 24, 536, 792, 824, 26, 954, 922) else gpr[d])
                self.pc = (self.pc + 4) & M
            elif op == 17:  # sc
                self.srr0 = (self.pc + 4) & M; self.srr1 = self.msr
                self.pc = 0x80000C00; self.msr &= ~0x0000EE70
            elif op in (48, 50, 52, 54):  # lfs, lfd, stfs, stfd (FP stub)
                self.pc = (self.pc + 4) & M
            elif op in (59, 63):  # FP compute stubs
                self.pc = (self.pc + 4) & M
            elif op == 3:  # twi
                self.pc = (self.pc + 4) & M
            else:
                self.pc = (self.pc + 4) & M

            done += 1
            self.cycles += 1
            self.tbl = self.cycles & M
            self.tbu = (self.cycles >> 32) & M

        return done


# ======================================================================
# Hardware Register Bus
# ======================================================================
class HardwareBus:
    """GameCube hardware register stubs (VI, PI, MI, DI, SI, EXI, AI)."""
    def __init__(self):
        self.vi_regs: Dict[int, int] = {}
        self.pi_regs: Dict[int, int] = {}
        self.mi_regs: Dict[int, int] = {}
        self.di_regs: Dict[int, int] = {}
        self.si_regs: Dict[int, int] = {}
        self.exi_regs: Dict[int, int] = {}
        self.ai_regs: Dict[int, int] = {}
        # VI framebuffer config
        self.vi_xfb_addr = 0  # external framebuffer address in RAM
        self.vi_width = 640
        self.vi_height = 480
        self.vi_vcount = 0
        self.vi_interrupt = False
        self.frame_complete = False

    def reset(self):
        for d in (self.vi_regs, self.pi_regs, self.mi_regs,
                  self.di_regs, self.si_regs, self.exi_regs, self.ai_regs):
            d.clear()
        self.vi_xfb_addr = 0
        self.vi_vcount = 0
        self.vi_interrupt = False
        self.frame_complete = False

    def read32(self, addr: int) -> int:
        offset = addr - HW_BASE
        if VI_BASE <= offset < VI_BASE + 0x100:
            vi_off = offset - VI_BASE
            if vi_off == 0x2C:  # VI_VCOUNT — vertical line counter
                self.vi_vcount = (self.vi_vcount + 1) % 525
                return self.vi_vcount
            if vi_off == 0x1C:  # VI_TFBL — top field base (XFB address)
                return self.vi_xfb_addr
            return self.vi_regs.get(vi_off, 0)
        elif PI_BASE <= offset < PI_BASE + 0x100:
            pi_off = offset - PI_BASE
            if pi_off == 0x00:  # INTSR — interrupt cause
                return self.pi_regs.get(0, 0)
            if pi_off == 0x04:  # INTMR — interrupt mask
                return self.pi_regs.get(4, 0)
            return self.pi_regs.get(pi_off, 0)
        elif MI_BASE <= offset < MI_BASE + 0x100:
            return self.mi_regs.get(offset - MI_BASE, 0)
        elif DI_BASE <= offset < DI_BASE + 0x40:
            return self.di_regs.get(offset - DI_BASE, 0)
        elif SI_BASE <= offset < SI_BASE + 0x100:
            si_off = offset - SI_BASE
            if si_off == 0x34:  # SI_STATUS — report no controller
                return 0x08000000  # "no device"
            return self.si_regs.get(si_off, 0)
        elif EXI_BASE <= offset < EXI_BASE + 0x40:
            return self.exi_regs.get(offset - EXI_BASE, 0)
        elif AI_BASE <= offset < AI_BASE + 0x40:
            return self.ai_regs.get(offset - AI_BASE, 0)
        return 0

    def write32(self, addr: int, val: int):
        offset = addr - HW_BASE
        val &= MASK32
        if VI_BASE <= offset < VI_BASE + 0x100:
            vi_off = offset - VI_BASE
            self.vi_regs[vi_off] = val
            if vi_off == 0x1C:  # VI_TFBL
                self.vi_xfb_addr = val & 0x01FFFFFF  # physical RAM addr
            elif vi_off == 0x00:  # VI_VTR
                pass
        elif PI_BASE <= offset < PI_BASE + 0x100:
            pi_off = offset - PI_BASE
            if pi_off == 0x00:  # Clear interrupts by writing 1
                self.pi_regs[0] = self.pi_regs.get(0, 0) & ~val
            else:
                self.pi_regs[pi_off] = val
        elif MI_BASE <= offset < MI_BASE + 0x100:
            self.mi_regs[offset - MI_BASE] = val
        elif DI_BASE <= offset < DI_BASE + 0x40:
            self.di_regs[offset - DI_BASE] = val
        elif SI_BASE <= offset < SI_BASE + 0x100:
            self.si_regs[offset - SI_BASE] = val
        elif EXI_BASE <= offset < EXI_BASE + 0x40:
            self.exi_regs[offset - EXI_BASE] = val
        elif AI_BASE <= offset < AI_BASE + 0x40:
            self.ai_regs[offset - AI_BASE] = val

    def tick_vi(self):
        """Call once per frame to advance VI state."""
        self.vi_vcount = 0
        self.frame_complete = True
        # Set VI interrupt in PI
        self.pi_regs[0] = self.pi_regs.get(0, 0) | 0x00000008  # VI int


# ======================================================================
# DOL Loader
# ======================================================================
class DOLLoader:
    """Load a GameCube DOL executable into RAM."""
    @staticmethod
    def load(data: bytes, ram: bytearray) -> int:
        """Load DOL sections into RAM. Returns entry point address."""
        if len(data) < 0x100:
            raise ValueError("DOL too small")

        # DOL header: 7 text sections + 11 data sections
        text_offsets = [struct.unpack_from(">I", data, 0x00 + i*4)[0] for i in range(7)]
        data_offsets = [struct.unpack_from(">I", data, 0x1C + i*4)[0] for i in range(11)]
        text_addrs   = [struct.unpack_from(">I", data, 0x48 + i*4)[0] for i in range(7)]
        data_addrs   = [struct.unpack_from(">I", data, 0x64 + i*4)[0] for i in range(11)]
        text_sizes   = [struct.unpack_from(">I", data, 0x90 + i*4)[0] for i in range(7)]
        data_sizes   = [struct.unpack_from(">I", data, 0xAC + i*4)[0] for i in range(11)]
        bss_addr     = struct.unpack_from(">I", data, 0xD8)[0]
        bss_size     = struct.unpack_from(">I", data, 0xDC)[0]
        entry        = struct.unpack_from(">I", data, 0xE0)[0]

        # Load text sections
        for i in range(7):
            if text_sizes[i] > 0 and text_offsets[i] > 0:
                vaddr = text_addrs[i]
                paddr = vaddr & 0x01FFFFFF  # strip 0x80000000
                if paddr + text_sizes[i] <= len(ram):
                    ram[paddr:paddr + text_sizes[i]] = data[text_offsets[i]:text_offsets[i] + text_sizes[i]]

        # Load data sections
        for i in range(11):
            if data_sizes[i] > 0 and data_offsets[i] > 0:
                vaddr = data_addrs[i]
                paddr = vaddr & 0x01FFFFFF
                if paddr + data_sizes[i] <= len(ram):
                    ram[paddr:paddr + data_sizes[i]] = data[data_offsets[i]:data_offsets[i] + data_sizes[i]]

        # Clear BSS
        if bss_size > 0 and bss_addr > 0:
            paddr = bss_addr & 0x01FFFFFF
            end = min(paddr + bss_size, len(ram))
            ram[paddr:end] = b'\x00' * (end - paddr)

        return entry


# ======================================================================
# GCM/ISO Parser
# ======================================================================
class GCMParser:
    @staticmethod
    def parse(path: str) -> Dict[str, Any]:
        info = {"game_name": "Unknown", "game_id": "????", "maker": "??",
                "is_gcm": False, "size": 0, "dol_offset": 0}
        try:
            sz = os.path.getsize(path)
            info["size"] = sz
            with open(path, "rb") as f:
                hdr = f.read(0x460)
                if len(hdr) < 0x460:
                    return info
                # Game ID at 0x00 (6 bytes)
                gid = hdr[0x00:0x06].decode("ascii", errors="replace")
                info["game_id"] = gid
                info["maker"] = hdr[0x04:0x06].decode("ascii", errors="replace")
                # Game name at 0x20 (null-terminated)
                name = hdr[0x20:0x20+0x3E0].split(b"\x00")[0].decode("ascii", errors="replace").strip()
                if name:
                    info["game_name"] = name
                # GCM magic at 0x1C
                magic = struct.unpack_from(">I", hdr, 0x1C)[0]
                if magic == 0xC2339F3D:
                    info["is_gcm"] = True
                # DOL offset at 0x420
                info["dol_offset"] = struct.unpack_from(">I", hdr, 0x420)[0]
        except Exception as e:
            print(f"GCM parse error: {e}")
        return info


# ======================================================================
# Emulator System (ties CPU + HW + RAM together)
# ======================================================================
class GameCubeSystem:
    def __init__(self):
        self.ram = bytearray(RAM_SIZE)
        self.hw = HardwareBus()
        self.cpu: Any = None  # Will be CyGekko or PyGekko
        self.running = False
        self.paused = False
        self.rom_path: Optional[str] = None
        self.game_info: Dict[str, Any] = {}
        self.frame_count = 0
        self.fps = 0.0
        self._fps_time = time.time()
        self._fps_frames = 0
        self._use_cython = False

        # Try Cython first
        cy = _try_compile_cython()
        if cy and hasattr(cy, "CyGekko"):
            self.cpu = cy.CyGekko()
            self.cpu.set_ram(self.ram)
            self.cpu.set_hw_callbacks(self.hw.read32, self.hw.write32)
            self._use_cython = True
            print("[AC'S Dolphin] Cython Gekko core loaded ✓")
        else:
            self.cpu = PyGekko()
            self.cpu.set_ram(self.ram)
            self.cpu.set_hw_callbacks(self.hw.read32, self.hw.write32)
            print("[AC'S Dolphin] Pure Python Gekko core loaded")

    def reset(self):
        self.ram[:] = b"\x00" * RAM_SIZE
        self.hw.reset()
        self.cpu.reset()
        if self._use_cython:
            self.cpu.set_ram(self.ram)
            self.cpu.set_hw_callbacks(self.hw.read32, self.hw.write32)
        else:
            self.cpu._ram = self.ram
        self.running = False
        self.paused = False
        self.frame_count = 0
        self.fps = 0.0

    def load_iso(self, path: str) -> bool:
        self.reset()
        self.game_info = GCMParser.parse(path)
        self.rom_path = path

        try:
            with open(path, "rb") as f:
                # Load boot header into RAM (0x0000-0x0020)
                f.seek(0)
                boot = f.read(0x2000)
                self.ram[:len(boot)] = boot

                # Load DOL if offset is valid
                dol_off = self.game_info.get("dol_offset", 0)
                if dol_off > 0:
                    f.seek(dol_off)
                    dol_data = f.read(8 * 1024 * 1024)  # read up to 8MB for DOL
                    entry = DOLLoader.load(dol_data, self.ram)
                    self.cpu.pc = entry
                    print(f"[AC'S Dolphin] DOL loaded, entry=0x{entry:08X}")
                else:
                    # No DOL found — just set PC to start
                    self.cpu.pc = 0x80003100

            # Setup initial register state (mimics apploader)
            self.cpu.gpr[1] = 0x816FFFF0  # Stack pointer
            self.cpu.gpr[2] = 0x80004000  # SDA2 base (guess)
            self.cpu.gpr[13] = 0x80005000  # SDA base (guess)
            self.cpu.msr = 0x00002032  # IR, DR, FP enabled

            return True
        except Exception as e:
            print(f"[AC'S Dolphin] ISO load error: {e}")
            return False

    def load_dol(self, path: str) -> bool:
        self.reset()
        self.game_info = {"game_name": Path(path).stem, "game_id": "DOL",
                          "is_gcm": False}
        self.rom_path = path
        try:
            with open(path, "rb") as f:
                dol_data = f.read()
            entry = DOLLoader.load(dol_data, self.ram)
            self.cpu.pc = entry
            self.cpu.gpr[1] = 0x816FFFF0
            self.cpu.msr = 0x00002032
            print(f"[AC'S Dolphin] DOL loaded, entry=0x{entry:08X}")
            return True
        except Exception as e:
            print(f"[AC'S Dolphin] DOL load error: {e}")
            return False

    def start(self):
        if self.rom_path:
            self.running = True
            self.paused = False

    def stop(self):
        self.running = False
        self.paused = False

    def pause(self):
        if self.running:
            self.paused = True

    def resume(self):
        if self.running:
            self.paused = False

    def run_frame(self):
        """Execute one frame's worth of CPU cycles."""
        if not self.running or self.paused:
            return

        cycles_target = PY_CYCLES_PER_SLICE
        try:
            self.cpu.run(cycles_target)
        except Exception as e:
            print(f"[AC'S Dolphin] CPU exception at PC=0x{self.cpu.pc:08X}: {e}")
            self.cpu.halted = True

        self.hw.tick_vi()
        self.frame_count += 1
        self._fps_frames += 1
        now = time.time()
        if now - self._fps_time >= 1.0:
            self.fps = self._fps_frames / (now - self._fps_time)
            self._fps_frames = 0
            self._fps_time = now

    def get_xfb_rgb(self, w: int, h: int) -> Optional[bytes]:
        """Read the XFB from RAM and return raw RGB bytes (w*h*3)."""
        xfb = self.hw.vi_xfb_addr
        if xfb == 0:
            return None
        # XFB is YUY2 format on real HW, but homebrew often writes RGB565 or raw
        # We'll treat it as RGB565 for display (2 bytes/pixel)
        size = w * h * 2
        if xfb + size > RAM_SIZE:
            return None
        raw = self.ram[xfb:xfb + size]
        # Convert RGB565 → RGB888
        out = bytearray(w * h * 3)
        for i in range(w * h):
            px = (raw[i*2] << 8) | raw[i*2 + 1]
            r = ((px >> 11) & 0x1F) << 3
            g = ((px >> 5) & 0x3F) << 2
            b = (px & 0x1F) << 3
            out[i*3] = r; out[i*3+1] = g; out[i*3+2] = b
        return bytes(out)


# ======================================================================
# GUI
# ======================================================================
class DolphinGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"AC'S Dolphin emu {VERSION} — GameCube Emulator")
        self.geometry("1100x720")
        self.minsize(800, 600)
        self.configure(bg="#1a1a2e")

        self.sys = GameCubeSystem()
        self._loop_id = None
        self._last_t = time.time()

        self._build_menu()
        self._build_toolbar()
        self._build_main()
        self._build_status()

        self.bind("<Control-o>", lambda e: self.open_rom())
        self.bind("<F5>", lambda e: self.start_emu())
        self.bind("<Escape>", lambda e: self.stop_emu())

        self._schedule()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_menu(self):
        mb = tk.Menu(self)
        self.config(menu=mb)
        fm = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="File", menu=fm)
        fm.add_command(label="Open ISO/GCM...", command=self.open_rom)
        fm.add_command(label="Open DOL...", command=self.open_dol)
        fm.add_separator()
        fm.add_command(label="Exit", command=self._on_close)

        em = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="Emulation", menu=em)
        em.add_command(label="Start", command=self.start_emu)
        em.add_command(label="Pause", command=self.pause_emu)
        em.add_command(label="Stop", command=self.stop_emu)
        em.add_command(label="Reset", command=self.reset_emu)

        hm = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="Help", menu=hm)
        hm.add_command(label="About", command=self._about)

    def _build_toolbar(self):
        tb = ttk.Frame(self)
        tb.pack(side=tk.TOP, fill=tk.X, padx=2, pady=2)
        ttk.Button(tb, text="📂 Open", command=self.open_rom).pack(side=tk.LEFT, padx=2)
        self.btn_start = ttk.Button(tb, text="▶ Start", command=self.start_emu)
        self.btn_start.pack(side=tk.LEFT, padx=2)
        self.btn_pause = ttk.Button(tb, text="⏸ Pause", command=self.pause_emu)
        self.btn_pause.pack(side=tk.LEFT, padx=2)
        self.btn_stop = ttk.Button(tb, text="⏹ Stop", command=self.stop_emu)
        self.btn_stop.pack(side=tk.LEFT, padx=2)
        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        ttk.Button(tb, text="🖥 Fullscreen", command=self._toggle_fs).pack(side=tk.LEFT, padx=2)
        self.lbl_fps = ttk.Label(tb, text="FPS: --")
        self.lbl_fps.pack(side=tk.RIGHT, padx=5)
        core_str = "Cython" if self.sys._use_cython else "Python"
        ttk.Label(tb, text=f"Core: {core_str}").pack(side=tk.RIGHT, padx=5)

    def _build_main(self):
        pw = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        pw.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Left: game list
        lf = ttk.Frame(pw); pw.add(lf, weight=1)
        ttk.Label(lf, text="Game Library", font=("", 10, "bold")).pack(anchor=tk.W, padx=5)
        sf = ttk.Frame(lf); sf.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        sb = ttk.Scrollbar(sf); sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.game_list = tk.Listbox(sf, yscrollcommand=sb.set, bg="#16213e", fg="#e0e0e0",
                                     selectbackground="#3a86ff", font=("Consolas", 9))
        self.game_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.config(command=self.game_list.yview)
        self.game_list.bind("<Double-1>", lambda e: self._load_selected())
        self._game_paths: List[str] = []

        # Right: canvas
        rf = ttk.Frame(pw); pw.add(rf, weight=3)
        self.canvas = tk.Canvas(rf, bg="#0a0a2a", highlightthickness=0)
        self.canvas.pack(expand=True, fill=tk.BOTH, padx=5, pady=5)
        self._info = self.canvas.create_text(320, 240,
            text=f"AC'S Dolphin emu {VERSION}\n\nNo ROM loaded — Open an ISO or DOL",
            fill="#6666aa", font=("Segoe UI", 13), justify=tk.CENTER)

        # Debug text
        self._dbg = self.canvas.create_text(10, 10, anchor=tk.NW,
            text="", fill="#44ff44", font=("Consolas", 8))

    def _build_status(self):
        sf = ttk.Frame(self); sf.pack(side=tk.BOTTOM, fill=tk.X)
        self.lbl_status = ttk.Label(sf, text="Ready", relief=tk.SUNKEN, anchor=tk.W)
        self.lbl_status.pack(side=tk.LEFT, fill=tk.X, expand=True)

    def open_rom(self):
        p = filedialog.askopenfilename(title="Select GameCube ROM",
            filetypes=[("GC Images", "*.iso *.gcm *.gcz"), ("All", "*.*")])
        if p:
            self._load_iso(p)

    def open_dol(self):
        p = filedialog.askopenfilename(title="Select DOL Executable",
            filetypes=[("DOL", "*.dol"), ("All", "*.*")])
        if p:
            ok = self.sys.load_dol(p)
            if ok:
                self.lbl_status.config(text=f"Loaded DOL: {Path(p).name}")
                self.canvas.itemconfig(self._info, text=f"Loaded: {Path(p).stem}\nPress Start")
            else:
                messagebox.showerror("Error", f"Failed to load DOL:\n{p}")

    def _load_iso(self, p: str):
        self.lbl_status.config(text=f"Loading {Path(p).name}...")
        self.update_idletasks()
        ok = self.sys.load_iso(p)
        if ok:
            gn = self.sys.game_info.get("game_name", "Unknown")
            gid = self.sys.game_info.get("game_id", "????")
            self.lbl_status.config(text=f"Loaded: {gn} [{gid}]")
            self.canvas.itemconfig(self._info, text=f"{gn}\n[{gid}]\n\nPress Start")
            # Scan directory for other ROMs
            self._scan_dir(os.path.dirname(p))
        else:
            messagebox.showerror("Error", f"Failed to load:\n{p}")

    def _load_selected(self):
        sel = self.game_list.curselection()
        if sel and sel[0] < len(self._game_paths):
            self._load_iso(self._game_paths[sel[0]])

    def _scan_dir(self, d: str):
        self.game_list.delete(0, tk.END)
        self._game_paths.clear()
        exts = (".iso", ".gcm", ".gcz", ".dol")
        try:
            for f in sorted(os.listdir(d)):
                if f.lower().endswith(exts):
                    fp = os.path.join(d, f)
                    info = GCMParser.parse(fp)
                    label = f"{info['game_name']} [{info['game_id']}]" if info["is_gcm"] else f
                    self.game_list.insert(tk.END, label)
                    self._game_paths.append(fp)
        except OSError:
            pass

    def start_emu(self):
        if not self.sys.rom_path:
            messagebox.showwarning("No ROM", "Load an ISO or DOL first.")
            return
        self.sys.start()
        self.lbl_status.config(text="Running")
        self.canvas.itemconfig(self._info, state=tk.HIDDEN)

    def pause_emu(self):
        if self.sys.running and not self.sys.paused:
            self.sys.pause()
            self.lbl_status.config(text="Paused")
            self.btn_pause.config(text="▶ Resume")
        elif self.sys.paused:
            self.sys.resume()
            self.lbl_status.config(text="Running")
            self.btn_pause.config(text="⏸ Pause")

    def stop_emu(self):
        self.sys.stop()
        self.lbl_status.config(text="Stopped")
        self.canvas.itemconfig(self._info, state=tk.NORMAL)
        self.btn_pause.config(text="⏸ Pause")

    def reset_emu(self):
        if self.sys.rom_path:
            p = self.sys.rom_path
            self.stop_emu()
            if p.lower().endswith(".dol"):
                self.sys.load_dol(p)
            else:
                self.sys.load_iso(p)
            self.start_emu()

    def _toggle_fs(self):
        cur = self.attributes("-fullscreen")
        self.attributes("-fullscreen", not cur)

    def _about(self):
        core = "Cython" if self.sys._use_cython else "Pure Python"
        messagebox.showinfo("About", f"AC'S Dolphin emu {VERSION}\n"
            f"GameCube Emulator\n\n"
            f"CPU Core: PowerPC 750CL (Gekko) — {core}\n"
            f"~90 integer instructions decoded\n"
            f"24 MB RAM | VI/PI/MI/DI/SI/EXI stubs\n"
            f"DOL loader + GCM/ISO parser\n\n"
            f"© A.C Holdings / Team Flames 1999-2026")

    def _schedule(self):
        now = time.time()
        dt = now - self._last_t
        self._last_t = now

        if self.sys.running and not self.sys.paused:
            self.sys.run_frame()
            self._draw_frame()

        # Update FPS display
        if self.sys.running:
            self.lbl_fps.config(text=f"FPS: {self.sys.fps:.1f}")
            # Debug overlay
            cpu = self.sys.cpu
            dbg = (f"PC: 0x{cpu.pc:08X}  LR: 0x{cpu.lr:08X}  "
                   f"CR: 0x{cpu.cr:08X}\n"
                   f"r0={cpu.gpr[0]:08X} r1={cpu.gpr[1]:08X} "
                   f"r2={cpu.gpr[2]:08X} r3={cpu.gpr[3]:08X}\n"
                   f"r4={cpu.gpr[4]:08X} r5={cpu.gpr[5]:08X} "
                   f"r6={cpu.gpr[6]:08X} r7={cpu.gpr[7]:08X}\n"
                   f"Cycles: {cpu.cycles}  Halted: {cpu.halted}")
            self.canvas.itemconfig(self._dbg, text=dbg)
        else:
            self.lbl_fps.config(text="FPS: --")
            self.canvas.itemconfig(self._dbg, text="")

        self._loop_id = self.after(FRAME_TIME_MS, self._schedule)

    def _draw_frame(self):
        """Render the framebuffer (XFB) or debug view."""
        w = max(self.canvas.winfo_width(), 320)
        h = max(self.canvas.winfo_height(), 240)

        # Try to display XFB
        rgb = self.sys.get_xfb_rgb(640, 480)
        if rgb:
            try:
                from PIL import Image, ImageTk
                img = Image.frombytes("RGB", (640, 480), rgb)
                img = img.resize((w, h), Image.NEAREST)
                self._photo = ImageTk.PhotoImage(img)
                self.canvas.delete("frame")
                self.canvas.create_image(w//2, h//2, image=self._photo, tags="frame")
                self.canvas.tag_lower("frame")
                return
            except ImportError:
                pass

        # Fallback: draw memory visualizer
        self.canvas.delete("frame")
        # Show first 256 bytes of RAM at PC as hex
        pc_phys = self.sys.cpu.pc & 0x01FFFFFF
        if pc_phys + 64 < RAM_SIZE:
            snippet = self.sys.ram[pc_phys:pc_phys+64]
            hex_str = " ".join(f"{b:02X}" for b in snippet)
            self.canvas.create_text(w//2, h//2, text=f"RAM @ PC (0x{self.sys.cpu.pc:08X}):\n{hex_str}",
                                     fill="#44aaff", font=("Consolas", 9), justify=tk.CENTER, tags="frame")

    def _on_close(self):
        if self._loop_id:
            self.after_cancel(self._loop_id)
        self.sys.stop()
        self.destroy()


# ======================================================================
# Entry Point
# ======================================================================
if __name__ == "__main__":
    try:
        from PIL import Image, ImageTk
    except ImportError:
        print("[AC'S Dolphin] Pillow not found — install for XFB display: pip install Pillow")
    app = DolphinGUI()
    app.mainloop()
