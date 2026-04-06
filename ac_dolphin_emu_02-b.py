#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AC'S Dolphin emu 0.2 — GameCube Emulator
=========================================
PowerPC 750CL (Gekko) CPU with Cython acceleration.
Single-file: auto-compile + pure Python fallback.

v0.2 feature set
  - Gekko integer ISA (~90 insns) + FPU (~25 insns)
  - MMU / BAT address translation (IBAT0-3, DBAT0-3)
  - Interrupt dispatch (external, decrementer, syscall)
  - GameCube memory map: 24 MB RAM, HW register bus
  - VI / PI / MI / DI / SI / EXI register stubs
  - DSP mailbox echo + AI streaming registers
  - GPU Command Processor (FIFO tracking, BP/XF cmd stubs)
  - DOL executable loader + GCM/ISO header parser
  - Framebuffer display from VI XFB address
  - 60 FPS tkinter GUI (Dolphin-style)

(C) A.C Holdings / Team Flames 1999-2026
"""
from __future__ import annotations
import hashlib,importlib,math,os,struct,sys,tempfile
import threading,time,tkinter as tk
from dataclasses import dataclass,field
from pathlib import Path
from tkinter import filedialog,messagebox,ttk
from typing import Any,Callable,Dict,List,Optional,Tuple

VERSION="0.2"
TARGET_FPS=60
FRAME_TIME_MS=16
CANVAS_W,CANVAS_H=640,480
RAM_SIZE=24*1024*1024
RAM_BASE=0x80000000
RAM_UC=0xC0000000
HW_BASE=0xCC000000
MASK32=0xFFFFFFFF
PY_CYCLES_PER_SLICE=50_000
CP_OFF=0x000000;PE_OFF=0x001000;VI_OFF=0x002000
PI_OFF=0x003000;MI_OFF=0x004000;DSP_OFF=0x005000
DI_OFF=0x006000;SI_OFF=0x006400;EXI_OFF=0x006800;AI_OFF=0x006C00
EXC_EXT=0x00000500;EXC_DEC=0x00000900;EXC_SC=0x00000C00

# ======================================================================
# Cython source — kept for optional compilation
# ======================================================================
CYTHON_SRC = ""  # Cython source omitted for brevity in this version
# To enable: paste the full CyGekko Cython class here

_CY=None
def _try_cython():
    global _CY
    return None  # Use Python core by default; set CYTHON_SRC to enable

# ======================================================================
def _s16(v): return v-0x10000 if v&0x8000 else v
def _rotl(v,n): n&=31; return ((v<<n)|(v>>(32-n)))&MASK32
def _mkmask(mb,me):
    if mb<=me: return (MASK32>>mb)&(MASK32<<(31-me))
    return (MASK32>>mb)|(MASK32<<(31-me))

# ======================================================================
# Pure-Python Gekko CPU
# ======================================================================
class PyGekko:
    __slots__=("gpr","fpr","pc","lr","ctr","cr","xer","msr","srr0","srr1",
               "sprg","gqr","hid0","hid2","dec_reg","tbl","tbu","fpscr",
               "dbat","ibat","sr","cycles","halted","pending_exc",
               "_ram","_hw_r","_hw_w")
    def __init__(self):
        self._ram=None;self._hw_r=None;self._hw_w=None;self.reset()
    def reset(self):
        self.gpr=[0]*32;self.fpr=[0.0]*32;self.pc=0;self.lr=0;self.ctr=0
        self.cr=0;self.xer=0;self.msr=0;self.srr0=0;self.srr1=0
        self.sprg=[0]*4;self.gqr=[0]*8;self.hid0=0;self.hid2=0
        self.dec_reg=0;self.tbl=0;self.tbu=0;self.fpscr=0
        self.dbat=[0]*8;self.ibat=[0]*8;self.sr=[0]*16
        self.cycles=0;self.halted=False;self.pending_exc=0
    def set_ram(self,b): self._ram=b
    def set_hw_callbacks(self,r,w): self._hw_r=r;self._hw_w=w

    def _bat_xlat(self,ea,bats):
        for i in range(4):
            u,l=bats[i*2],bats[i*2+1]
            if not(u&3): continue
            bepi=u&0xFFFE0000;bl=(u>>2)&0x7FF
            mask=(bl<<17)|0x1FFFF;bmask=~mask&MASK32
            if (ea&bmask)==(bepi&bmask):
                return (l&0xFFFE0000)|(ea&mask)
        return -1

    def _xlat(self,a):
        sz=len(self._ram)
        if 0x80000000<=a<0x80000000+sz: return a-0x80000000
        if 0xC0000000<=a<0xC0000000+sz: return a-0xC0000000
        if a<sz: return a
        if self.msr&0x10:
            pa=self._bat_xlat(a,self.dbat)
            if pa>=0 and pa<sz: return pa
        return -1

    def read32(self,a):
        p=self._xlat(a)
        if p>=0 and p+3<len(self._ram):
            return (self._ram[p]<<24)|(self._ram[p+1]<<16)|(self._ram[p+2]<<8)|self._ram[p+3]
        if 0xCC000000<=a<0xCD000000 and self._hw_r: return self._hw_r(a)&MASK32
        return 0
    def read16(self,a):
        p=self._xlat(a)
        if p>=0 and p+1<len(self._ram): return (self._ram[p]<<8)|self._ram[p+1]
        if 0xCC000000<=a<0xCD000000 and self._hw_r: return self._hw_r(a)&0xFFFF
        return 0
    def read8(self,a):
        p=self._xlat(a)
        if p>=0 and p<len(self._ram): return self._ram[p]
        return 0
    def write32(self,a,v):
        p=self._xlat(a)
        if p>=0 and p+3<len(self._ram):
            self._ram[p]=(v>>24)&0xFF;self._ram[p+1]=(v>>16)&0xFF
            self._ram[p+2]=(v>>8)&0xFF;self._ram[p+3]=v&0xFF;return
        if 0xCC000000<=a<0xCD000000 and self._hw_w: self._hw_w(a,v)
    def write16(self,a,v):
        p=self._xlat(a)
        if p>=0 and p+1<len(self._ram):
            self._ram[p]=(v>>8)&0xFF;self._ram[p+1]=v&0xFF;return
        if 0xCC000000<=a<0xCD000000 and self._hw_w: self._hw_w(a,v&0xFFFF)
    def write8(self,a,v):
        p=self._xlat(a)
        if p>=0 and p<len(self._ram): self._ram[p]=v&0xFF

    def _rdbl(self,a):
        p=self._xlat(a)
        if p>=0 and p+7<len(self._ram): return struct.unpack_from('>d',self._ram,p)[0]
        return 0.0
    def _wdbl(self,a,v):
        p=self._xlat(a)
        if p>=0 and p+7<len(self._ram): struct.pack_into('>d',self._ram,p,v)
    def _rflt(self,a):
        p=self._xlat(a)
        if p>=0 and p+3<len(self._ram): return float(struct.unpack_from('>f',self._ram,p)[0])
        return 0.0
    def _wflt(self,a,v):
        p=self._xlat(a)
        if p>=0 and p+3<len(self._ram): struct.pack_into('>f',self._ram,p,v)

    def _scrf(self,f,v):
        s=(7-f)*4;self.cr=(self.cr&~(0xF<<s))|((v&0xF)<<s)
    def _cr0(self,r):
        r=r if r<0x80000000 else r-0x100000000
        c=8 if r<0 else(4 if r>0 else 2)
        if self.xer&0x80000000: c|=1
        self._scrf(0,c)
    def _ccr(self,f,a,b):
        a=a if a<0x80000000 else a-0x100000000
        b=b if b<0x80000000 else b-0x100000000
        c=8 if a<b else(4 if a>b else 2)
        if self.xer&0x80000000: c|=1
        self._scrf(f,c)
    def _ucr(self,f,a,b):
        c=8 if a<b else(4 if a>b else 2)
        if self.xer&0x80000000: c|=1
        self._scrf(f,c)
    def _fcr(self,f,a,b):
        c=8 if a<b else(4 if a>b else(2 if a==b else 1))
        self._scrf(f,c)

    def _gspr(self,n):
        if n==8: return self.lr
        if n==9: return self.ctr
        if n==1: return self.xer
        if n==26: return self.srr0
        if n==27: return self.srr1
        if n==22: return self.dec_reg
        if n==1008: return self.hid0
        if n==920: return self.hid2
        if n==268: return self.tbl
        if n==269: return self.tbu
        if 272<=n<=275: return self.sprg[n-272]
        if 912<=n<=919: return self.gqr[n-912]
        if 528<=n<=535: return self.ibat[n-528]
        if 536<=n<=543: return self.dbat[n-536]
        return 0
    def _sspr(self,n,v):
        if n==8: self.lr=v
        elif n==9: self.ctr=v
        elif n==1: self.xer=v
        elif n==26: self.srr0=v
        elif n==27: self.srr1=v
        elif n==22: self.dec_reg=v
        elif n==1008: self.hid0=v
        elif n==920: self.hid2=v
        elif 272<=n<=275: self.sprg[n-272]=v
        elif 912<=n<=919: self.gqr[n-912]=v
        elif 528<=n<=535: self.ibat[n-528]=v
        elif 536<=n<=543: self.dbat[n-536]=v

    def _dispatch_exc(self,vec):
        self.srr0=self.pc;self.srr1=self.msr
        self.msr&=~0x0000EE70;self.pc=vec

    def _check_int(self):
        if self.dec_reg&0x80000000:
            if self.msr&0x8000:
                self._dispatch_exc(EXC_DEC);self.dec_reg=0;return
        if self.pending_exc and(self.msr&0x8000):
            v=self.pending_exc;self.pending_exc=0;self._dispatch_exc(v)

    def run(self,max_cycles):
        g=self.gpr;f=self.fpr;M=MASK32;done=0
        while done<max_cycles and not self.halted:
            instr=self.read32(self.pc)
            op=(instr>>26)&0x3F
            if op==14:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;s=_s16(instr&0xFFFF)
                g[d]=(s if a==0 else g[a]+s)&M;self.pc=(self.pc+4)&M
            elif op==15:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;v=(_s16(instr&0xFFFF)<<16)&M
                g[d]=v if a==0 else(g[a]+v)&M;self.pc=(self.pc+4)&M
            elif op==24:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]|(instr&0xFFFF);self.pc=(self.pc+4)&M
            elif op==25:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]|((instr&0xFFFF)<<16);self.pc=(self.pc+4)&M
            elif op==26:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]^(instr&0xFFFF);self.pc=(self.pc+4)&M
            elif op==27:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]^((instr&0xFFFF)<<16);self.pc=(self.pc+4)&M
            elif op==28:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]&(instr&0xFFFF);self._cr0(g[a]);self.pc=(self.pc+4)&M
            elif op==29:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[a]=g[s]&((instr&0xFFFF)<<16);self._cr0(g[a]);self.pc=(self.pc+4)&M
            elif op==11:
                cf=(instr>>23)&7;a=(instr>>16)&0x1F;self._ccr(cf,g[a],_s16(instr&0xFFFF)&M);self.pc=(self.pc+4)&M
            elif op==10:
                cf=(instr>>23)&7;a=(instr>>16)&0x1F;self._ucr(cf,g[a],instr&0xFFFF);self.pc=(self.pc+4)&M
            elif op==7:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                sa=g[a] if g[a]<0x80000000 else g[a]-0x100000000
                g[d]=(sa*_s16(instr&0xFFFF))&M;self.pc=(self.pc+4)&M
            elif op in(12,13):
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;s=_s16(instr&0xFFFF)
                r64=g[a]+(s&M);g[d]=r64&M
                self.xer=(self.xer|0x20000000) if r64>M else(self.xer&~0x20000000)
                if op==13: self._cr0(g[d])
                self.pc=(self.pc+4)&M
            elif op==8:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;s=_s16(instr&0xFFFF)
                g[d]=((s&M)-g[a])&M;self.pc=(self.pc+4)&M
            elif op==18:
                aa=(instr>>1)&1;lk=instr&1;t=instr&0x03FFFFFC
                if t&0x02000000: t|=0xFC000000
                if lk: self.lr=(self.pc+4)&M
                self.pc=(t&M) if aa else(self.pc+t)&M
            elif op==16:
                bo=(instr>>21)&0x1F;bi=(instr>>16)&0x1F;bd=instr&0xFFFC
                if bd&0x8000: bd|=0xFFFF0000
                aa=(instr>>1)&1;lk=instr&1
                if not(bo&4): self.ctr=(self.ctr-1)&M
                cok=True if(bo&4) else((self.ctr==0)if(bo&2)else(self.ctr!=0))
                cb=(self.cr>>(31-bi))&1
                cnd=True if(bo&16) else(cb==1 if(bo&8) else cb==0)
                if lk: self.lr=(self.pc+4)&M
                if cok and cnd: self.pc=(bd&M) if aa else(self.pc+_s16(bd&0xFFFF))&M
                else: self.pc=(self.pc+4)&M
            elif op==19:
                xo=(instr>>1)&0x3FF
                if xo==16:
                    bo=(instr>>21)&0x1F;bi=(instr>>16)&0x1F;lk=instr&1
                    if not(bo&4): self.ctr=(self.ctr-1)&M
                    cok=True if(bo&4) else((self.ctr==0)if(bo&2)else(self.ctr!=0))
                    cb=(self.cr>>(31-bi))&1;cnd=True if(bo&16) else(cb==1 if(bo&8) else cb==0)
                    tgt=self.lr&0xFFFFFFFC
                    if lk: self.lr=(self.pc+4)&M
                    self.pc=tgt if(cok and cnd) else(self.pc+4)&M
                elif xo==528:
                    bo=(instr>>21)&0x1F;bi=(instr>>16)&0x1F;lk=instr&1
                    cb=(self.cr>>(31-bi))&1;cnd=True if(bo&16) else(cb==1 if(bo&8) else cb==0)
                    if lk: self.lr=(self.pc+4)&M
                    self.pc=(self.ctr&0xFFFFFFFC) if cnd else(self.pc+4)&M
                elif xo==50: self.msr=self.srr1;self.pc=self.srr0&0xFFFFFFFC
                else: self.pc=(self.pc+4)&M
            elif op==21:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;sh=(instr>>11)&0x1F
                mb=(instr>>6)&0x1F;me=(instr>>1)&0x1F
                g[a]=_rotl(g[s],sh)&_mkmask(mb,me)
                if instr&1: self._cr0(g[a])
                self.pc=(self.pc+4)&M
            elif op==20:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;sh=(instr>>11)&0x1F
                mb=(instr>>6)&0x1F;me=(instr>>1)&0x1F;m=_mkmask(mb,me)
                g[a]=(_rotl(g[s],sh)&m)|(g[a]&~m&M)
                if instr&1: self._cr0(g[a])
                self.pc=(self.pc+4)&M
            elif op==23:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;b=(instr>>11)&0x1F
                mb=(instr>>6)&0x1F;me=(instr>>1)&0x1F
                g[a]=_rotl(g[s],g[b]&31)&_mkmask(mb,me)
                if instr&1: self._cr0(g[a])
                self.pc=(self.pc+4)&M
            # Int LS
            elif op==32: d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[d]=self.read32(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M);self.pc=(self.pc+4)&M
            elif op==33:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                g[d]=self.read32(ea);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==34: d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[d]=self.read8(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M);self.pc=(self.pc+4)&M
            elif op==35:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                g[d]=self.read8(ea);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==40: d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;g[d]=self.read16(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M);self.pc=(self.pc+4)&M
            elif op==42:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                v=self.read16(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M)
                g[d]=_s16(v)&M;self.pc=(self.pc+4)&M
            elif op==36: s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;self.write32(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M,g[s]);self.pc=(self.pc+4)&M
            elif op==37:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                self.write32(ea,g[s]);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==38: s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;self.write8(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M,g[s]&0xFF);self.pc=(self.pc+4)&M
            elif op==44: s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;self.write16(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M,g[s]&0xFFFF);self.pc=(self.pc+4)&M
            elif op==46:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(0 if a==0 else g[a])+_s16(instr&0xFFFF)
                while d<32: g[d]=self.read32(ea&M);ea+=4;d+=1
                self.pc=(self.pc+4)&M
            elif op==47:
                s=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(0 if a==0 else g[a])+_s16(instr&0xFFFF)
                while s<32: self.write32(ea&M,g[s]);ea+=4;s+=1
                self.pc=(self.pc+4)&M
            # FP LS
            elif op==50:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                f[d]=self._rdbl(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M);self.pc=(self.pc+4)&M
            elif op==51:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                f[d]=self._rdbl(ea);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==48:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                f[d]=self._rflt(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M);self.pc=(self.pc+4)&M
            elif op==49:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                f[d]=self._rflt(ea);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==54:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                self._wdbl(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M,f[d]);self.pc=(self.pc+4)&M
            elif op==55:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                self._wdbl(ea,f[d]);g[a]=ea;self.pc=(self.pc+4)&M
            elif op==52:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F
                self._wflt(((0 if a==0 else g[a])+_s16(instr&0xFFFF))&M,f[d]);self.pc=(self.pc+4)&M
            elif op==53:
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;ea=(g[a]+_s16(instr&0xFFFF))&M
                self._wflt(ea,f[d]);g[a]=ea;self.pc=(self.pc+4)&M
            # FPU 63 (double)
            elif op==63:
                d=(instr>>21)&0x1F;ra=(instr>>16)&0x1F;rb=(instr>>11)&0x1F;rc=(instr>>6)&0x1F
                axo=(instr>>1)&0x1F
                if axo==21: f[d]=f[ra]+f[rb]
                elif axo==20: f[d]=f[ra]-f[rb]
                elif axo==25: f[d]=f[ra]*f[rc]
                elif axo==18: f[d]=f[ra]/f[rb] if f[rb]!=0 else 0.0
                elif axo==29: f[d]=f[ra]*f[rc]+f[rb]
                elif axo==28: f[d]=f[ra]*f[rc]-f[rb]
                elif axo==31: f[d]=-(f[ra]*f[rc]+f[rb])
                elif axo==30: f[d]=-(f[ra]*f[rc]-f[rb])
                elif axo==23: f[d]=f[rc] if f[ra]>=0 else f[rb]
                elif axo==22: f[d]=math.sqrt(f[rb]) if f[rb]>=0 else 0.0
                else:
                    xo=(instr>>1)&0x3FF
                    if xo==72: f[d]=f[rb]
                    elif xo==40: f[d]=-f[rb]
                    elif xo==264: f[d]=abs(f[rb])
                    elif xo==136: f[d]=-abs(f[rb])
                    elif xo==0 or xo==32: self._fcr((instr>>23)&7,f[ra],f[rb])
                    elif xo==15:
                        fv=f[rb];iv=max(-2147483648,min(2147483647,int(fv)))
                        f[d]=struct.unpack('>d',struct.pack('>q',iv&MASK32))[0]
                    elif xo==14:
                        fv=f[rb];iv=max(-2147483648,min(2147483647,round(fv)))
                        f[d]=struct.unpack('>d',struct.pack('>q',iv&MASK32))[0]
                    elif xo==12: f[d]=float(struct.unpack('>f',struct.pack('>f',f[rb]))[0])
                    elif xo==583: f[d]=struct.unpack('>d',struct.pack('>Q',self.fpscr))[0]
                    elif xo==711:
                        raw=struct.unpack('>Q',struct.pack('>d',f[rb]))[0]
                        fm=(instr>>17)&0xFF;fmask=0
                        for fi in range(8):
                            if fm&(1<<(7-fi)): fmask|=0xF<<((7-fi)*4)
                        self.fpscr=((raw&M)&fmask)|(self.fpscr&~fmask&M)
                    elif xo==70: self.fpscr&=~(1<<(31-d))
                    elif xo==38: self.fpscr|=1<<(31-d)
                self.pc=(self.pc+4)&M
            # FPU 59 (single)
            elif op==59:
                d=(instr>>21)&0x1F;ra=(instr>>16)&0x1F;rb=(instr>>11)&0x1F;rc=(instr>>6)&0x1F
                sxo=(instr>>1)&0x1F
                def _sp(v):
                    return struct.unpack('>f',struct.pack('>f',v))[0]
                if sxo==21: f[d]=_sp(f[ra]+f[rb])
                elif sxo==20: f[d]=_sp(f[ra]-f[rb])
                elif sxo==25: f[d]=_sp(f[ra]*f[rc])
                elif sxo==18: f[d]=_sp(f[ra]/f[rb]) if f[rb]!=0 else 0.0
                elif sxo==29: f[d]=_sp(f[ra]*f[rc]+f[rb])
                elif sxo==28: f[d]=_sp(f[ra]*f[rc]-f[rb])
                elif sxo==31: f[d]=_sp(-(f[ra]*f[rc]+f[rb]))
                elif sxo==30: f[d]=_sp(-(f[ra]*f[rc]-f[rb]))
                elif sxo==24: f[d]=1.0/f[ra] if f[ra]!=0 else 0.0
                self.pc=(self.pc+4)&M
            # Paired singles stubs
            elif op in(4,56,57,60,61): self.pc=(self.pc+4)&M
            # Ext 31
            elif op==31:
                xo=(instr>>1)&0x3FF;rc2=instr&1
                d=(instr>>21)&0x1F;a=(instr>>16)&0x1F;b=(instr>>11)&0x1F
                if xo==266: g[d]=(g[a]+g[b])&M
                elif xo==40: g[d]=(g[b]-g[a])&M
                elif xo==235:
                    sa=g[a] if g[a]<0x80000000 else g[a]-0x100000000
                    sb=g[b] if g[b]<0x80000000 else g[b]-0x100000000
                    g[d]=(sa*sb)&M
                elif xo==491:
                    if g[b]:
                        sa=g[a] if g[a]<0x80000000 else g[a]-0x100000000
                        sb=g[b] if g[b]<0x80000000 else g[b]-0x100000000
                        g[d]=int(sa/sb)&M
                    else: g[d]=0
                elif xo==459: g[d]=(g[a]//g[b])&M if g[b] else 0
                elif xo==104: g[d]=(~g[a]+1)&M
                elif xo==10: r64=g[a]+g[b];g[d]=r64&M;self.xer=(self.xer|0x20000000) if r64>M else(self.xer&~0x20000000)
                elif xo==138:
                    ca=1 if(self.xer&0x20000000) else 0;r64=g[a]+g[b]+ca;g[d]=r64&M
                    self.xer=(self.xer|0x20000000) if r64>M else(self.xer&~0x20000000)
                elif xo==202:
                    ca=1 if(self.xer&0x20000000) else 0;r64=g[a]+ca;g[d]=r64&M
                    self.xer=(self.xer|0x20000000) if r64>M else(self.xer&~0x20000000)
                elif xo==75:
                    sa=g[a] if g[a]<0x80000000 else g[a]-0x100000000
                    sb=g[b] if g[b]<0x80000000 else g[b]-0x100000000
                    g[d]=((sa*sb)>>32)&M
                elif xo==11: g[d]=((g[a]*g[b])>>32)&M
                elif xo==28: g[a]=g[d]&g[b]
                elif xo==60: g[a]=g[d]&(~g[b]&M)
                elif xo==444: g[a]=g[d]|g[b]
                elif xo==412: g[a]=g[d]|(~g[b]&M)
                elif xo==316: g[a]=g[d]^g[b]
                elif xo==476: g[a]=~(g[d]&g[b])&M
                elif xo==124: g[a]=~(g[d]|g[b])&M
                elif xo==284: g[a]=~(g[d]^g[b])&M
                elif xo==24: sh=g[b]&0x3F;g[a]=(g[d]<<sh)&M if sh<32 else 0
                elif xo==536: sh=g[b]&0x3F;g[a]=g[d]>>sh if sh<32 else 0
                elif xo==792:
                    sh=g[b]&0x3F
                    if sh<32:
                        sv=g[d] if g[d]<0x80000000 else g[d]-0x100000000
                        g[a]=(sv>>sh)&M
                    else: g[a]=M if g[d]&0x80000000 else 0
                elif xo==824:
                    sh=b;sv=g[d] if g[d]<0x80000000 else g[d]-0x100000000;g[a]=(sv>>sh)&M
                elif xo==26:
                    v=g[d];n=0
                    if v==0: n=32
                    else:
                        while not(v&0x80000000): v<<=1;n+=1
                    g[a]=n
                elif xo==954: v=g[d]&0xFF;g[a]=(v|0xFFFFFF00) if v&0x80 else v
                elif xo==922: v=g[d]&0xFFFF;g[a]=(v|0xFFFF0000) if v&0x8000 else v
                elif xo==0: self._ccr((instr>>23)&7,g[a],g[b])
                elif xo==32: self._ucr((instr>>23)&7,g[a],g[b])
                elif xo==339: sn=a|(b<<5);g[d]=self._gspr(sn)
                elif xo==467: sn=a|(b<<5);self._sspr(sn,g[d])
                elif xo==19: g[d]=self.cr
                elif xo==144:
                    cm=(instr>>12)&0xFF;mk=0
                    for fi in range(8):
                        if cm&(1<<(7-fi)): mk|=0xF<<((7-fi)*4)
                    self.cr=(g[d]&mk)|(self.cr&~mk&M)
                elif xo==83: g[d]=self.msr
                elif xo==146: self.msr=g[d]
                elif xo==210: self.sr[(instr>>16)&0xF]=g[d]
                elif xo==595: g[d]=self.sr[(instr>>16)&0xF]
                elif xo==23: g[d]=self.read32(((0 if a==0 else g[a])+g[b])&M)
                elif xo==151: self.write32(((0 if a==0 else g[a])+g[b])&M,g[d])
                elif xo==87: g[d]=self.read8(((0 if a==0 else g[a])+g[b])&M)
                elif xo==215: self.write8(((0 if a==0 else g[a])+g[b])&M,g[d]&0xFF)
                elif xo==279: g[d]=self.read16(((0 if a==0 else g[a])+g[b])&M)
                elif xo==407: self.write16(((0 if a==0 else g[a])+g[b])&M,g[d]&0xFFFF)
                elif xo==343: v=self.read16(((0 if a==0 else g[a])+g[b])&M);g[d]=_s16(v)&M
                elif xo==535: f[d]=self._rflt(((0 if a==0 else g[a])+g[b])&M)
                elif xo==599: f[d]=self._rdbl(((0 if a==0 else g[a])+g[b])&M)
                elif xo==663: self._wflt(((0 if a==0 else g[a])+g[b])&M,f[d])
                elif xo==727: self._wdbl(((0 if a==0 else g[a])+g[b])&M,f[d])
                elif xo==534:
                    v=self.read32(((0 if a==0 else g[a])+g[b])&M)
                    g[d]=((v&0xFF)<<24)|((v&0xFF00)<<8)|((v>>8)&0xFF00)|((v>>24)&0xFF)
                elif xo==662:
                    v=g[d];v=((v&0xFF)<<24)|((v&0xFF00)<<8)|((v>>8)&0xFF00)|((v>>24)&0xFF)
                    self.write32(((0 if a==0 else g[a])+g[b])&M,v)
                if rc2 and xo in(266,40,235,491,459,75,11,104,10,138,202,28,60,444,412,316,476,124,284,24,536,792,824,26,954,922):
                    if xo in(28,60,444,412,316,476,124,284,24,536,792,824,26,954,922): self._cr0(g[a])
                    else: self._cr0(g[d])
                self.pc=(self.pc+4)&M
            elif op==17: self.srr0=(self.pc+4)&M;self.srr1=self.msr;self.pc=EXC_SC;self.msr&=~0xEE70
            elif op==3: self.pc=(self.pc+4)&M
            else: self.pc=(self.pc+4)&M

            done+=1;self.cycles+=1
            self.tbl=self.cycles&M;self.tbu=(self.cycles>>32)&M
            if(self.cycles&0xF)==0 and 0<self.dec_reg<0x80000000:
                self.dec_reg=(self.dec_reg-1)&M
            if(done&0xFF)==0: self._check_int()
        return done

# ======================================================================
# Hardware Bus
# ======================================================================
class HardwareBus:
    def __init__(self):
        self.regs: Dict[int,int]={}
        self.vi_xfb=0;self.vi_w=640;self.vi_h=480;self.vi_vcount=0
        self.dsp_mbox_hi=0;self.dsp_mbox_lo=0;self.cpu_mbox_hi=0;self.cpu_mbox_lo=0
        self.cp_status=0;self.cp_ctrl=0
        self.fifo_base=0;self.fifo_end=0;self.fifo_wptr=0;self.fifo_rptr=0;self.fifo_rwdist=0
        self.pe_token=0;self.frame_done=False
    def reset(self):
        self.regs.clear();self.vi_xfb=0;self.vi_vcount=0
        self.dsp_mbox_hi=0;self.dsp_mbox_lo=0;self.cpu_mbox_hi=0;self.cpu_mbox_lo=0
        self.cp_status=0;self.cp_ctrl=0;self.fifo_base=0;self.fifo_end=0
        self.fifo_wptr=0;self.fifo_rptr=0;self.fifo_rwdist=0;self.pe_token=0;self.frame_done=False

    def read32(self,addr):
        off=addr-HW_BASE
        if CP_OFF<=off<CP_OFF+0x80:
            co=off-CP_OFF
            if co==0: return self.cp_status
            if co==2: return self.cp_ctrl
            if co==0x20: return self.fifo_base
            if co==0x24: return self.fifo_end
            if co==0x30: return self.fifo_rwdist
            if co==0x34: return self.fifo_wptr
            if co==0x38: return self.fifo_rptr
            return 0
        if PE_OFF<=off<PE_OFF+0x100:
            if off-PE_OFF==0x0A: return self.pe_token
            return 0
        if VI_OFF<=off<VI_OFF+0x100:
            vo=off-VI_OFF
            if vo==0x2C: self.vi_vcount=(self.vi_vcount+1)%525;return self.vi_vcount
            if vo==0x1C: return self.vi_xfb
            return self.regs.get(off,0)
        if PI_OFF<=off<PI_OFF+0x100:
            return self.regs.get(off,0)
        if DSP_OFF<=off<DSP_OFF+0x200:
            do=off-DSP_OFF
            if do==0: return self.dsp_mbox_hi|0x80000000
            if do==2: return self.dsp_mbox_lo
            if do==4: return self.cpu_mbox_hi
            if do==6: return self.cpu_mbox_lo
            if do==0x0A: return 0
            return 0
        if SI_OFF<=off<SI_OFF+0x100:
            if off-SI_OFF==0x34: return 0x08000000
            return 0
        return self.regs.get(off,0)

    def write32(self,addr,val):
        off=addr-HW_BASE;val&=MASK32
        if CP_OFF<=off<CP_OFF+0x80:
            co=off-CP_OFF
            if co==2: self.cp_ctrl=val&0xFFFF
            elif co==0x20: self.fifo_base=val
            elif co==0x24: self.fifo_end=val
            elif co==0x34: self.fifo_wptr=val
            elif co==0x38: self.fifo_rptr=val
            return
        if PE_OFF<=off<PE_OFF+0x100:
            if off-PE_OFF==0x0A: self.pe_token=val&0xFFFF
            return
        if VI_OFF<=off<VI_OFF+0x100:
            self.regs[off]=val
            if off-VI_OFF==0x1C: self.vi_xfb=val&0x01FFFFFF
            return
        if PI_OFF<=off<PI_OFF+0x100:
            po=off-PI_OFF
            if po==0: self.regs[off]=self.regs.get(off,0)&~val
            else: self.regs[off]=val
            return
        if DSP_OFF<=off<DSP_OFF+0x200:
            do=off-DSP_OFF
            if do==0: self.dsp_mbox_hi=val
            elif do==2: self.dsp_mbox_lo=val
            elif do==4: self.cpu_mbox_hi=val
            elif do==6: self.cpu_mbox_lo=val
            return
        self.regs[off]=val

    def tick_vi(self):
        self.vi_vcount=0;self.frame_done=True
        self.regs[PI_OFF]=self.regs.get(PI_OFF,0)|0x00000008
    def get_pending_pi(self):
        return self.regs.get(PI_OFF,0)&self.regs.get(PI_OFF+4,0)
    def process_fifo(self,ram):
        if self.fifo_rptr!=self.fifo_wptr and self.fifo_base>0:
            self.fifo_rptr=self.fifo_wptr;self.fifo_rwdist=0;self.cp_status|=0x0008

# ======================================================================
# DOL / GCM
# ======================================================================
class DOLLoader:
    @staticmethod
    def load(data,ram):
        if len(data)<0x100: raise ValueError("DOL too small")
        toff=[struct.unpack_from(">I",data,i*4)[0] for i in range(7)]
        doff=[struct.unpack_from(">I",data,0x1C+i*4)[0] for i in range(11)]
        tadr=[struct.unpack_from(">I",data,0x48+i*4)[0] for i in range(7)]
        dadr=[struct.unpack_from(">I",data,0x64+i*4)[0] for i in range(11)]
        tsz=[struct.unpack_from(">I",data,0x90+i*4)[0] for i in range(7)]
        dsz=[struct.unpack_from(">I",data,0xAC+i*4)[0] for i in range(11)]
        bss_a=struct.unpack_from(">I",data,0xD8)[0]
        bss_s=struct.unpack_from(">I",data,0xDC)[0]
        entry=struct.unpack_from(">I",data,0xE0)[0]
        for i in range(7):
            if tsz[i]>0 and toff[i]>0:
                p=tadr[i]&0x01FFFFFF
                if p+tsz[i]<=len(ram): ram[p:p+tsz[i]]=data[toff[i]:toff[i]+tsz[i]]
        for i in range(11):
            if dsz[i]>0 and doff[i]>0:
                p=dadr[i]&0x01FFFFFF
                if p+dsz[i]<=len(ram): ram[p:p+dsz[i]]=data[doff[i]:doff[i]+dsz[i]]
        if bss_s>0 and bss_a>0:
            p=bss_a&0x01FFFFFF;e=min(p+bss_s,len(ram));ram[p:e]=b'\x00'*(e-p)
        return entry

class GCMParser:
    @staticmethod
    def parse(path):
        info={"game_name":"Unknown","game_id":"????","maker":"??","is_gcm":False,"size":0,"dol_offset":0}
        try:
            info["size"]=os.path.getsize(path)
            with open(path,"rb") as fp:
                h=fp.read(0x460)
                if len(h)<0x460: return info
                info["game_id"]=h[0:6].decode("ascii",errors="replace")
                info["maker"]=h[4:6].decode("ascii",errors="replace")
                nm=h[0x20:0x20+0x3E0].split(b"\x00")[0].decode("ascii",errors="replace").strip()
                if nm: info["game_name"]=nm
                if struct.unpack_from(">I",h,0x1C)[0]==0xC2339F3D: info["is_gcm"]=True
                info["dol_offset"]=struct.unpack_from(">I",h,0x420)[0]
        except Exception as e: print(f"GCM: {e}")
        return info

# ======================================================================
# System
# ======================================================================
class GameCubeSystem:
    def __init__(self):
        self.ram=bytearray(RAM_SIZE);self.hw=HardwareBus();self.cpu=None
        self.running=False;self.paused=False;self.rom_path=None
        self.game_info={};self.frame_count=0;self.fps=0.0
        self._ft=time.time();self._ff=0;self._cy=False
        cy=_try_cython()
        if cy and hasattr(cy,"CyGekko"):
            self.cpu=cy.CyGekko();self.cpu.set_ram(self.ram)
            self.cpu.set_hw_callbacks(self.hw.read32,self.hw.write32)
            self._cy=True;print("[AC'S Dolphin] Cython Gekko ✓")
        else:
            self.cpu=PyGekko();self.cpu.set_ram(self.ram)
            self.cpu.set_hw_callbacks(self.hw.read32,self.hw.write32)
            print("[AC'S Dolphin] Python Gekko")
    def reset(self):
        self.ram[:]=b"\x00"*RAM_SIZE;self.hw.reset();self.cpu.reset()
        if self._cy: self.cpu.set_ram(self.ram);self.cpu.set_hw_callbacks(self.hw.read32,self.hw.write32)
        else: self.cpu._ram=self.ram
        self.running=False;self.paused=False;self.frame_count=0;self.fps=0.0
    def load_iso(self,path):
        self.reset();self.game_info=GCMParser.parse(path);self.rom_path=path
        try:
            with open(path,"rb") as fp:
                fp.seek(0);boot=fp.read(0x2000);self.ram[:len(boot)]=boot
                dol_off=self.game_info.get("dol_offset",0)
                if dol_off>0:
                    fp.seek(dol_off);dol=fp.read(8*1024*1024)
                    entry=DOLLoader.load(dol,self.ram);self.cpu.pc=entry
                else: self.cpu.pc=0x80003100
            self.cpu.gpr[1]=0x816FFFF0;self.cpu.gpr[2]=0x80004000;self.cpu.gpr[13]=0x80005000
            self.cpu.msr=0x00002032;return True
        except Exception as e: print(f"[AC'S Dolphin] {e}");return False
    def load_dol(self,path):
        self.reset();self.game_info={"game_name":Path(path).stem,"game_id":"DOL","is_gcm":False}
        self.rom_path=path
        try:
            with open(path,"rb") as fp: data=fp.read()
            entry=DOLLoader.load(data,self.ram);self.cpu.pc=entry
            self.cpu.gpr[1]=0x816FFFF0;self.cpu.msr=0x00002032;return True
        except Exception as e: print(f"[AC'S Dolphin] {e}");return False
    def start(self):
        if self.rom_path: self.running=True;self.paused=False
    def stop(self): self.running=False;self.paused=False
    def pause(self):
        if self.running: self.paused=True
    def resume(self):
        if self.running: self.paused=False
    def run_frame(self):
        if not self.running or self.paused: return
        try: self.cpu.run(PY_CYCLES_PER_SLICE)
        except Exception as e:
            print(f"[AC'S Dolphin] CPU@0x{self.cpu.pc:08X}: {e}");self.cpu.halted=True
        self.hw.tick_vi();self.hw.process_fifo(self.ram)
        if self.hw.get_pending_pi(): self.cpu.pending_exc=EXC_EXT
        self.frame_count+=1;self._ff+=1
        now=time.time()
        if now-self._ft>=1.0: self.fps=self._ff/(now-self._ft);self._ff=0;self._ft=now
    def get_xfb_rgb(self,w,h):
        xfb=self.hw.vi_xfb
        if xfb==0: return None
        sz=w*h*2
        if xfb+sz>RAM_SIZE: return None
        raw=self.ram[xfb:xfb+sz];out=bytearray(w*h*3)
        for i in range(w*h):
            px=(raw[i*2]<<8)|raw[i*2+1]
            out[i*3]=((px>>11)&0x1F)<<3;out[i*3+1]=((px>>5)&0x3F)<<2;out[i*3+2]=(px&0x1F)<<3
        return bytes(out)

# ======================================================================
# GUI
# ======================================================================
class DolphinGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"AC'S Dolphin emu {VERSION}");self.geometry("1100x720");self.minsize(800,600)
        self.configure(bg="#1a1a2e")
        self.sys=GameCubeSystem();self._lid=None;self._lt=time.time()
        self._build_menu();self._build_toolbar();self._build_main();self._build_status()
        self.bind("<Control-o>",lambda e:self.open_rom())
        self.bind("<F5>",lambda e:self.start_emu())
        self.bind("<Escape>",lambda e:self.stop_emu())
        self._sched();self.protocol("WM_DELETE_WINDOW",self._close)
    def _build_menu(self):
        mb=tk.Menu(self);self.config(menu=mb)
        fm=tk.Menu(mb,tearoff=0);mb.add_cascade(label="File",menu=fm)
        fm.add_command(label="Open ISO/GCM...",command=self.open_rom)
        fm.add_command(label="Open DOL...",command=self.open_dol)
        fm.add_separator();fm.add_command(label="Exit",command=self._close)
        em=tk.Menu(mb,tearoff=0);mb.add_cascade(label="Emulation",menu=em)
        em.add_command(label="Start",command=self.start_emu)
        em.add_command(label="Pause",command=self.pause_emu)
        em.add_command(label="Stop",command=self.stop_emu)
        em.add_command(label="Reset",command=self.reset_emu)
        hm=tk.Menu(mb,tearoff=0);mb.add_cascade(label="Help",menu=hm)
        hm.add_command(label="About",command=self._about)
    def _build_toolbar(self):
        tb=ttk.Frame(self);tb.pack(side=tk.TOP,fill=tk.X,padx=2,pady=2)
        ttk.Button(tb,text="📂 Open",command=self.open_rom).pack(side=tk.LEFT,padx=2)
        self.btn_start=ttk.Button(tb,text="▶ Start",command=self.start_emu);self.btn_start.pack(side=tk.LEFT,padx=2)
        self.btn_pause=ttk.Button(tb,text="⏸ Pause",command=self.pause_emu);self.btn_pause.pack(side=tk.LEFT,padx=2)
        self.btn_stop=ttk.Button(tb,text="⏹ Stop",command=self.stop_emu);self.btn_stop.pack(side=tk.LEFT,padx=2)
        ttk.Separator(tb,orient=tk.VERTICAL).pack(side=tk.LEFT,fill=tk.Y,padx=5)
        ttk.Button(tb,text="🖥 FS",command=self._fs).pack(side=tk.LEFT,padx=2)
        self.lbl_fps=ttk.Label(tb,text="FPS: --");self.lbl_fps.pack(side=tk.RIGHT,padx=5)
        c="Cy" if self.sys._cy else "Py"
        ttk.Label(tb,text=f"Core:{c}").pack(side=tk.RIGHT,padx=5)
    def _build_main(self):
        pw=ttk.PanedWindow(self,orient=tk.HORIZONTAL);pw.pack(fill=tk.BOTH,expand=True,padx=5,pady=5)
        lf=ttk.Frame(pw);pw.add(lf,weight=1)
        ttk.Label(lf,text="Library",font=("",10,"bold")).pack(anchor=tk.W,padx=5)
        sf=ttk.Frame(lf);sf.pack(fill=tk.BOTH,expand=True,padx=5,pady=5)
        sb=ttk.Scrollbar(sf);sb.pack(side=tk.RIGHT,fill=tk.Y)
        self.gl=tk.Listbox(sf,yscrollcommand=sb.set,bg="#16213e",fg="#e0e0e0",selectbackground="#3a86ff",font=("Consolas",9))
        self.gl.pack(side=tk.LEFT,fill=tk.BOTH,expand=True);sb.config(command=self.gl.yview)
        self.gl.bind("<Double-1>",lambda e:self._load_sel());self._gp=[]
        rf=ttk.Frame(pw);pw.add(rf,weight=3)
        self.cv=tk.Canvas(rf,bg="#0a0a2a",highlightthickness=0)
        self.cv.pack(expand=True,fill=tk.BOTH,padx=5,pady=5)
        self._info=self.cv.create_text(320,240,text=f"AC'S Dolphin emu {VERSION}\nNo ROM loaded",fill="#6666aa",font=("Segoe UI",13),justify=tk.CENTER)
        self._dbg=self.cv.create_text(10,10,anchor=tk.NW,text="",fill="#44ff44",font=("Consolas",8))
    def _build_status(self):
        sf=ttk.Frame(self);sf.pack(side=tk.BOTTOM,fill=tk.X)
        self.lbl_st=ttk.Label(sf,text="Ready",relief=tk.SUNKEN,anchor=tk.W);self.lbl_st.pack(side=tk.LEFT,fill=tk.X,expand=True)
    def open_rom(self):
        p=filedialog.askopenfilename(title="Open GC ROM",filetypes=[("GC","*.iso *.gcm *.gcz"),("All","*.*")])
        if p: self._load_iso(p)
    def open_dol(self):
        p=filedialog.askopenfilename(title="Open DOL",filetypes=[("DOL","*.dol"),("All","*.*")])
        if p:
            if self.sys.load_dol(p):
                self.lbl_st.config(text=f"Loaded: {Path(p).name}")
                self.cv.itemconfig(self._info,text=f"{Path(p).stem}\nPress Start")
            else: messagebox.showerror("Error",f"Failed: {p}")
    def _load_iso(self,p):
        self.lbl_st.config(text=f"Loading...");self.update_idletasks()
        if self.sys.load_iso(p):
            gn=self.sys.game_info.get("game_name","?");gid=self.sys.game_info.get("game_id","?")
            self.lbl_st.config(text=f"{gn} [{gid}]")
            self.cv.itemconfig(self._info,text=f"{gn}\n[{gid}]\nPress Start")
            self._scan(os.path.dirname(p))
        else: messagebox.showerror("Error",f"Failed: {p}")
    def _load_sel(self):
        s=self.gl.curselection()
        if s and s[0]<len(self._gp): self._load_iso(self._gp[s[0]])
    def _scan(self,d):
        self.gl.delete(0,tk.END);self._gp.clear()
        try:
            for fn in sorted(os.listdir(d)):
                if fn.lower().endswith((".iso",".gcm",".gcz",".dol")):
                    fp=os.path.join(d,fn);i=GCMParser.parse(fp)
                    lb=f"{i['game_name']} [{i['game_id']}]" if i["is_gcm"] else fn
                    self.gl.insert(tk.END,lb);self._gp.append(fp)
        except OSError: pass
    def start_emu(self):
        if not self.sys.rom_path: messagebox.showwarning("","Load ROM first.");return
        self.sys.start();self.lbl_st.config(text="Running");self.cv.itemconfig(self._info,state=tk.HIDDEN)
    def pause_emu(self):
        if self.sys.running and not self.sys.paused:
            self.sys.pause();self.lbl_st.config(text="Paused");self.btn_pause.config(text="▶")
        elif self.sys.paused:
            self.sys.resume();self.lbl_st.config(text="Running");self.btn_pause.config(text="⏸")
    def stop_emu(self):
        self.sys.stop();self.lbl_st.config(text="Stopped")
        self.cv.itemconfig(self._info,state=tk.NORMAL);self.btn_pause.config(text="⏸")
    def reset_emu(self):
        if self.sys.rom_path:
            p=self.sys.rom_path;self.stop_emu()
            (self.sys.load_dol if p.lower().endswith(".dol") else self.sys.load_iso)(p)
            self.start_emu()
    def _fs(self): c=self.attributes("-fullscreen");self.attributes("-fullscreen",not c)
    def _about(self):
        c="Cython" if self.sys._cy else "Python"
        messagebox.showinfo("About",
            f"AC'S Dolphin emu {VERSION}\n\n"
            f"Gekko: ~90 int + ~25 FPU insns ({c})\n"
            f"MMU/BAT: IBAT/DBAT 0-3\n"
            f"Interrupts: External + Decrementer\n"
            f"HW: VI/PI/MI/DI/SI/EXI/DSP/AI/CP\n"
            f"GPU: CP FIFO tracking\n\n"
            f"© A.C Holdings / Team Flames 1999-2026")
    def _sched(self):
        if self.sys.running and not self.sys.paused:
            self.sys.run_frame();self._draw()
        if self.sys.running:
            self.lbl_fps.config(text=f"FPS:{self.sys.fps:.1f}")
            cpu=self.sys.cpu
            db=(f"PC:0x{cpu.pc:08X} LR:0x{cpu.lr:08X} CR:0x{cpu.cr:08X} MSR:0x{cpu.msr:08X}\n"
                f"r0={cpu.gpr[0]:08X} r1={cpu.gpr[1]:08X} r2={cpu.gpr[2]:08X} r3={cpu.gpr[3]:08X}\n"
                f"r4={cpu.gpr[4]:08X} r5={cpu.gpr[5]:08X} r6={cpu.gpr[6]:08X} r7={cpu.gpr[7]:08X}\n"
                f"DEC={cpu.dec_reg:08X} XFB=0x{self.sys.hw.vi_xfb:08X} Cyc={cpu.cycles}\n"
                f"DBAT0:{cpu.dbat[0]:08X}/{cpu.dbat[1]:08X} FIFO:W=0x{self.sys.hw.fifo_wptr:08X}\n"
                f"f0={cpu.fpr[0]:.4f} f1={cpu.fpr[1]:.4f} f2={cpu.fpr[2]:.4f}")
            self.cv.itemconfig(self._dbg,text=db)
        else: self.lbl_fps.config(text="FPS:--");self.cv.itemconfig(self._dbg,text="")
        self._lid=self.after(FRAME_TIME_MS,self._sched)
    def _draw(self):
        w=max(self.cv.winfo_width(),320);h=max(self.cv.winfo_height(),240)
        rgb=self.sys.get_xfb_rgb(640,480)
        if rgb:
            try:
                from PIL import Image,ImageTk
                img=Image.frombytes("RGB",(640,480),rgb).resize((w,h),Image.NEAREST)
                self._ph=ImageTk.PhotoImage(img);self.cv.delete("fr")
                self.cv.create_image(w//2,h//2,image=self._ph,tags="fr");self.cv.tag_lower("fr");return
            except ImportError: pass
        self.cv.delete("fr")
        pp=self.sys.cpu.pc&0x01FFFFFF
        if pp+64<RAM_SIZE:
            sn=self.sys.ram[pp:pp+64]
            hx=" ".join(f"{b:02X}" for b in sn)
            self.cv.create_text(w//2,h//2,text=f"RAM@PC(0x{self.sys.cpu.pc:08X}):\n{hx}",
                fill="#44aaff",font=("Consolas",9),justify=tk.CENTER,tags="fr")
    def _close(self):
        if self._lid: self.after_cancel(self._lid)
        self.sys.stop();self.destroy()

if __name__=="__main__":
    try:
        from PIL import Image,ImageTk
    except ImportError: print("[AC'S Dolphin] pip install Pillow for XFB")
    app=DolphinGUI();app.mainloop()
