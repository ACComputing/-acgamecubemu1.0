#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AC'S Dolphin emu 0.1 - GameCube Emulator Frontend
-------------------------------------------------
A high-level GameCube emulator interface built with tkinter.
This application provides a full-featured GUI similar to Dolphin,
including ROM loading, a 60 FPS emulation loop, and a modular core.

NOTE: This is a demonstration skeleton with a functional fake emulation core
      (rotating 3D cube demo). For real GameCube emulation, replace the
      EmulatorCore class with bindings to a real emulator (e.g., via Cython,
      ctypes, or subprocess). The architecture is designed to be easily
      extensible.

Author: AI Assistant
Version: 0.1
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os
import threading
import time
import random
import struct
import math
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, List, Tuple, Dict, Any

# ----------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------
TARGET_FPS = 60
FRAME_TIME_MS = int(1000 / TARGET_FPS)  # ~16.67 ms
CANVAS_WIDTH = 640
CANVAS_HEIGHT = 480
GAMECUBE_ASPECT = CANVAS_WIDTH / CANVAS_HEIGHT  # 4:3

# ----------------------------------------------------------------------
# GameCube ISO Header Parser (basic)
# ----------------------------------------------------------------------
class GCISOParser:
    """Parse basic information from a GameCube ISO image."""
    
    @staticmethod
    def parse_iso_header(file_path: str) -> Dict[str, Any]:
        """
        Extract metadata from the GameCube disc header.
        Returns a dictionary with game name, ID, and other info.
        """
        info = {
            "game_name": "Unknown Game",
            "game_id": "????",
            "maker_code": "??",
            "is_valid": False,
            "file_size": 0
        }
        
        try:
            with open(file_path, 'rb') as f:
                # GameCube disc header is at offset 0x00000000
                header = f.read(0x20)
                if len(header) < 0x20:
                    return info
                
                # Check for GameCube magic: "GCM" or "CUBE" at various offsets
                magic = header[0x1C:0x1F]
                if magic == b'GCM' or magic == b'CUBE' or header[0:4] == b'CUBE':
                    info["is_valid"] = True
                
                # Game name is at offset 0x00, 0x20 bytes (ASCII, null-padded)
                f.seek(0x00)
                raw_name = f.read(0x20).split(b'\x00')[0].decode('ascii', errors='ignore')
                if raw_name.strip():
                    info["game_name"] = raw_name.strip()
                
                # Game ID: offset 0x00, 6 bytes (e.g., "GALE01")
                f.seek(0x00)
                game_id_raw = f.read(6).decode('ascii', errors='ignore')
                if game_id_raw and len(game_id_raw) >= 4:
                    info["game_id"] = game_id_raw[:6]
                
                # Maker code: offset 0x06, 2 bytes
                f.seek(0x06)
                maker = f.read(2).decode('ascii', errors='ignore')
                if maker:
                    info["maker_code"] = maker
                
                # File size
                info["file_size"] = os.path.getsize(file_path)
                
        except Exception as e:
            print(f"Error parsing ISO: {e}")
        
        return info


# ----------------------------------------------------------------------
# Fake Emulator Core (Replace with real emulation)
# ----------------------------------------------------------------------
@dataclass
class CubeVertex:
    x: float
    y: float
    z: float

class EmulatorCore:
    """
    Core emulation engine. This is a FAKE implementation that simulates
    a GameCube-like environment by rendering a rotating 3D cube.
    
    To integrate a real emulator:
        - Replace the update() method with actual CPU/GPU emulation.
        - Use Cython or ctypes to call Dolphin's core functions.
        - Maintain proper memory, registers, and framebuffer.
    """
    
    def __init__(self):
        # Emulation state
        self.running = False
        self.paused = False
        self.rom_path: Optional[str] = None
        self.game_info: Dict[str, Any] = {}
        self.frame_count = 0
        self.last_time = time.time()
        self.fps = 0.0
        
        # Fake "CPU" registers and memory
        self.pc = 0x80000000  # Program counter
        self.registers = [0] * 32
        self.memory = bytearray(24 * 1024 * 1024)  # 24 MB fake RAM
        
        # 3D cube state for demo rendering
        self.cube_vertices = [
            CubeVertex(-1, -1, -1), CubeVertex( 1, -1, -1),
            CubeVertex( 1, -1,  1), CubeVertex(-1, -1,  1),  # bottom face
            CubeVertex(-1,  1, -1), CubeVertex( 1,  1, -1),
            CubeVertex( 1,  1,  1), CubeVertex(-1,  1,  1)   # top face
        ]
        self.edges = [
            (0,1), (1,2), (2,3), (3,0),  # bottom
            (4,5), (5,6), (6,7), (7,4),  # top
            (0,4), (1,5), (2,6), (3,7)   # vertical
        ]
        self.angle_x = 0.0
        self.angle_y = 0.0
        self.angle_z = 0.0
        
        # Background color and effects
        self.bg_color = "#0a0a2a"
        self.cube_color = "#3a86ff"
        self.glow = False
        
    def load_rom(self, path: str) -> bool:
        """Load a GameCube ROM (ISO/GCM) into the emulator."""
        try:
            if not os.path.exists(path):
                return False
            
            # Parse ISO header
            self.game_info = GCISOParser.parse_iso_header(path)
            if not self.game_info["is_valid"]:
                # Still allow loading but show warning
                print("Warning: File does not appear to be a valid GameCube ISO")
            
            self.rom_path = path
            # Simulate loading game data into memory
            with open(path, 'rb') as f:
                # Only read first few MB for demo (real emulator would load entire disc)
                data = f.read(8 * 1024 * 1024)  # 8 MB
                self.memory[:len(data)] = data
            
            # Reset CPU state
            self.pc = 0x80000000
            self.registers = [0] * 32
            self.frame_count = 0
            return True
            
        except Exception as e:
            print(f"ROM loading error: {e}")
            return False
    
    def start(self):
        """Start or resume emulation."""
        if self.rom_path:
            self.running = True
            self.paused = False
        else:
            raise RuntimeError("No ROM loaded")
    
    def stop(self):
        """Stop emulation."""
        self.running = False
        self.paused = False
    
    def pause(self):
        """Pause emulation."""
        if self.running:
            self.paused = True
    
    def resume(self):
        """Resume emulation."""
        if self.running and self.paused:
            self.paused = False
    
    def update(self, delta_time: float):
        """
        Update emulation state for one frame.
        This is where actual CPU/GPU emulation would happen.
        For demonstration, we update the cube rotation angles.
        """
        if not self.running or self.paused:
            return
        
        # Fake CPU instruction execution (just increment PC and simulate work)
        self.pc += 4  # Simulate fetching one instruction
        if self.pc > 0x80010000:
            self.pc = 0x80000000  # wrap around
        
        # Update fake registers for demo
        for i in range(4):
            self.registers[i] = (self.registers[i] + 1) & 0xFFFFFFFF
        
        # Update cube rotation (smooth 60 FPS rotation)
        rotation_speed = 1.5  # radians per second
        self.angle_x += rotation_speed * delta_time
        self.angle_y += rotation_speed * 0.7 * delta_time
        self.angle_z += rotation_speed * 0.3 * delta_time
        
        # Keep angles in range
        self.angle_x %= 2 * math.pi
        self.angle_y %= 2 * math.pi
        self.angle_z %= 2 * math.pi
        
        # Update FPS counter
        self.frame_count += 1
        current_time = time.time()
        if current_time - self.last_time >= 1.0:
            self.fps = self.frame_count
            self.frame_count = 0
            self.last_time = current_time
    
    def get_frame_surface(self, width: int, height: int) -> List[Tuple[int, int, int]]:
        """
        Render the current emulated frame into a list of RGB tuples.
        This simulates the framebuffer output.
        Returns a flat list of (R,G,B) for each pixel.
        """
        if not self.running:
            # Return black screen when not running
            return [(0,0,0)] * (width * height)
        
        # Create a simple software renderer for the cube
        # In a real emulator, this would be the GPU output.
        pixels = []
        
        # Projection parameters
        fov = math.pi / 3
        viewer_distance = 4.0
        scale = min(width, height) / 3.5
        
        # Precompute rotation matrices
        cos_x = math.cos(self.angle_x)
        sin_x = math.sin(self.angle_x)
        cos_y = math.cos(self.angle_y)
        sin_y = math.sin(self.angle_y)
        cos_z = math.cos(self.angle_z)
        sin_z = math.sin(self.angle_z)
        
        # Project vertices to 2D
        projected = []
        for v in self.cube_vertices:
            # Rotate around X
            y1 = v.y * cos_x - v.z * sin_x
            z1 = v.y * sin_x + v.z * cos_x
            # Rotate around Y
            x2 = v.x * cos_y + z1 * sin_y
            z2 = -v.x * sin_y + z1 * cos_y
            # Rotate around Z
            x3 = x2 * cos_z - y1 * sin_z
            y3 = x2 * sin_z + y1 * cos_z
            z3 = z2
            
            # Perspective projection
            factor = viewer_distance / (viewer_distance + z3)
            x_proj = x3 * factor * scale + width / 2
            y_proj = -y3 * factor * scale + height / 2
            projected.append((int(x_proj), int(y_proj), z3))
        
        # Create framebuffer as a list of RGB tuples (initialize with background)
        bg_r, bg_g, bg_b = 10, 10, 42  # dark blue background
        framebuffer = [(bg_r, bg_g, bg_b)] * (width * height)
        
        # Helper to set pixel (with bounds check)
        def set_pixel(x, y, color):
            if 0 <= x < width and 0 <= y < height:
                idx = y * width + x
                framebuffer[idx] = color
        
        # Draw edges (simple line drawing using Bresenham)
        for edge in self.edges:
            p1 = projected[edge[0]]
            p2 = projected[edge[1]]
            x1, y1, z1 = p1
            x2, y2, z2 = p2
            
            # Color based on depth
            depth = (z1 + z2) / 2
            intensity = max(0, min(255, int(100 - depth * 30)))
            r = min(255, 58 + intensity)
            g = min(255, 134 + intensity)
            b = min(255, 255)
            color = (r, g, b)
            
            # Draw line
            dx = abs(x2 - x1)
            dy = abs(y2 - y1)
            sx = 1 if x1 < x2 else -1
            sy = 1 if y1 < y2 else -1
            err = dx - dy
            x, y = x1, y1
            while True:
                set_pixel(x, y, color)
                if x == x2 and y == y2:
                    break
                e2 = 2 * err
                if e2 > -dy:
                    err -= dy
                    x += sx
                if e2 < dx:
                    err += dx
                    y += sy
        
        # Draw a simple "GAMECUBE" text overlay using character mapping (simulated)
        text = "AC'S DOLPHIN"
        font_width = 8
        start_x = width - len(text) * font_width - 10
        start_y = height - 20
        # Simple pixel text simulation (just a few dots)
        for i, ch in enumerate(text):
            x = start_x + i * font_width
            for dy in range(0, 8, 2):
                if y + dy < height:
                    set_pixel(x, start_y + dy, (200, 200, 200))
        
        return framebuffer
    
    def get_status_string(self) -> str:
        """Return a status string for the GUI status bar."""
        if not self.running:
            return "Emulation Stopped"
        if self.paused:
            return "Emulation Paused"
        game = self.game_info.get("game_name", "No ROM")
        fps_str = f"{self.fps:.1f} FPS"
        pc_str = f"PC: 0x{self.pc:08X}"
        return f"{game} | {fps_str} | {pc_str}"


# ----------------------------------------------------------------------
# Main GUI Application (Dolphin-style)
# ----------------------------------------------------------------------
class DolphinEmulatorGUI(tk.Tk):
    """Main window of the emulator, styled after Dolphin."""
    
    def __init__(self):
        super().__init__()
        
        self.title("AC'S Dolphin emu 0.1")
        self.geometry("1100x700")
        self.minsize(800, 600)
        
        # Emulator core instance
        self.core = EmulatorCore()
        self.emulation_loop_id = None
        self.last_frame_time = time.time()
        
        # Setup UI
        self._create_menu()
        self._create_toolbar()
        self._create_main_panes()
        self._create_statusbar()
        
        # Bind keyboard shortcuts
        self.bind("<Control-o>", lambda e: self.open_rom())
        self.bind("<Control-s>", lambda e: self.start_emulation())
        self.bind("<Control-p>", lambda e: self.pause_emulation())
        self.bind("<Control-t>", lambda e: self.stop_emulation())
        self.bind("<F5>", lambda e: self.start_emulation())
        self.bind("<Escape>", lambda e: self.stop_emulation())
        
        # Initial scan for ROMs in current directory
        self.scan_roms()
        
        # Start the emulation drawing loop (but core not running until ROM loaded)
        self._schedule_frame_update()
        
        # Handle window close
        self.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def _create_menu(self):
        """Create the menu bar."""
        menubar = tk.Menu(self)
        self.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Open ROM...", command=self.open_rom, accelerator="Ctrl+O")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_closing)
        
        # Emulation menu
        emu_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Emulation", menu=emu_menu)
        emu_menu.add_command(label="Start", command=self.start_emulation, accelerator="F5")
        emu_menu.add_command(label="Pause", command=self.pause_emulation, accelerator="Ctrl+P")
        emu_menu.add_command(label="Stop", command=self.stop_emulation, accelerator="Esc")
        emu_menu.add_separator()
        emu_menu.add_command(label="Reset", command=self.reset_emulation)
        
        # Graphics menu (placeholder)
        graphics_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Graphics", menu=graphics_menu)
        graphics_menu.add_command(label="Settings...", command=self.show_graphics_settings)
        graphics_menu.add_command(label="Toggle Fullscreen", command=self.toggle_fullscreen)
        
        # Tools menu
        tools_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Scan for ROMs", command=self.scan_roms)
        tools_menu.add_command(label="Memory Card Manager...", command=self.memory_card_manager)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="About", command=self.show_about)
    
    def _create_toolbar(self):
        """Create a toolbar with action buttons."""
        toolbar = ttk.Frame(self)
        toolbar.pack(side=tk.TOP, fill=tk.X, padx=2, pady=2)
        
        # Buttons with emoji/text icons
        self.btn_open = ttk.Button(toolbar, text="📂 Open", command=self.open_rom)
        self.btn_open.pack(side=tk.LEFT, padx=2)
        
        self.btn_start = ttk.Button(toolbar, text="▶ Start", command=self.start_emulation)
        self.btn_start.pack(side=tk.LEFT, padx=2)
        
        self.btn_pause = ttk.Button(toolbar, text="⏸ Pause", command=self.pause_emulation)
        self.btn_pause.pack(side=tk.LEFT, padx=2)
        
        self.btn_stop = ttk.Button(toolbar, text="⏹ Stop", command=self.stop_emulation)
        self.btn_stop.pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        self.btn_fullscreen = ttk.Button(toolbar, text="🖥 Fullscreen", command=self.toggle_fullscreen)
        self.btn_fullscreen.pack(side=tk.LEFT, padx=2)
        
        self.btn_settings = ttk.Button(toolbar, text="⚙ Settings", command=self.show_graphics_settings)
        self.btn_settings.pack(side=tk.LEFT, padx=2)
        
        # Spacer
        ttk.Label(toolbar, text="").pack(side=tk.LEFT, expand=True, fill=tk.X)
        
        # FPS/Speed label in toolbar
        self.toolbar_fps_label = ttk.Label(toolbar, text="FPS: -- | Speed: --%")
        self.toolbar_fps_label.pack(side=tk.RIGHT, padx=5)
    
    def _create_main_panes(self):
        """Create the main content area with game list and display."""
        main_paned = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel: Game list
        left_frame = ttk.Frame(main_paned)
        main_paned.add(left_frame, weight=1)
        
        ttk.Label(left_frame, text="Game Library", font=("Segoe UI", 10, "bold")).pack(anchor=tk.W, padx=5, pady=2)
        
        # Listbox with scrollbar
        list_frame = ttk.Frame(left_frame)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.game_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, bg="#1e1e2e", fg="#ffffff", selectbackground="#3a86ff")
        self.game_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.game_listbox.yview)
        
        self.game_listbox.bind("<Double-Button-1>", lambda e: self.load_selected_rom())
        
        # Right panel: Display area
        right_frame = ttk.Frame(main_paned)
        main_paned.add(right_frame, weight=3)
        
        # Canvas for emulation output
        self.canvas = tk.Canvas(right_frame, bg="#0a0a2a", width=CANVAS_WIDTH, height=CANVAS_HEIGHT, highlightthickness=0)
        self.canvas.pack(expand=True, fill=tk.BOTH, padx=5, pady=5)
        
        # Info label on canvas
        self.info_text = self.canvas.create_text(CANVAS_WIDTH//2, CANVAS_HEIGHT//2, text="No ROM Loaded\nClick 'Open' to select a GameCube ISO",
                                                 fill="#8888cc", font=("Segoe UI", 12), justify=tk.CENTER)
    
    def _create_statusbar(self):
        """Create status bar at the bottom."""
        self.statusbar = ttk.Frame(self)
        self.statusbar.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.status_label = ttk.Label(self.statusbar, text="Ready", relief=tk.SUNKEN, anchor=tk.W)
        self.status_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        self.speed_label = ttk.Label(self.statusbar, text="Target: 60 FPS", relief=tk.SUNKEN, anchor=tk.W, width=15)
        self.speed_label.pack(side=tk.RIGHT)
    
    def scan_roms(self, directory: str = None):
        """Scan for GameCube ROMs in the given directory (default: current working dir)."""
        if directory is None:
            directory = os.getcwd()
        
        self.game_listbox.delete(0, tk.END)
        extensions = ('.iso', '.gcm', '.gcz', '.ciso')
        found = 0
        
        try:
            for file in os.listdir(directory):
                if file.lower().endswith(extensions):
                    full_path = os.path.join(directory, file)
                    # Try to get game name from header
                    info = GCISOParser.parse_iso_header(full_path)
                    display_name = info.get("game_name", file)
                    self.game_listbox.insert(tk.END, f"{display_name} [{file}]")
                    # Store full path in listbox item
                    idx = self.game_listbox.size() - 1
                    self.game_listbox.itemconfig(idx, fg="#aaffaa" if info["is_valid"] else "#ffaa88")
                    # Bind path as attribute
                    if not hasattr(self.game_listbox, "game_paths"):
                        self.game_listbox.game_paths = []
                    self.game_listbox.game_paths.append(full_path)
                    found += 1
            
            if found == 0:
                self.game_listbox.insert(tk.END, "No ROMs found in current directory.")
                self.game_listbox.game_paths = []
            else:
                self.status_label.config(text=f"Found {found} ROM(s) in {directory}")
        except Exception as e:
            self.status_label.config(text=f"Error scanning: {e}")
    
    def load_selected_rom(self):
        """Load the ROM selected in the game list."""
        selection = self.game_listbox.curselection()
        if selection and hasattr(self.game_listbox, "game_paths") and len(self.game_listbox.game_paths) > selection[0]:
            path = self.game_listbox.game_paths[selection[0]]
            self._load_rom(path)
    
    def open_rom(self):
        """Open file dialog to select a ROM."""
        file_path = filedialog.askopenfilename(
            title="Select GameCube ROM",
            filetypes=[("GameCube ISOs", "*.iso *.gcm *.gcz *.ciso"), ("All files", "*.*")]
        )
        if file_path:
            self._load_rom(file_path)
            # Also add to game list if not already there
            self.scan_roms(os.path.dirname(file_path))
    
    def _load_rom(self, path: str):
        """Internal method to load a ROM into the emulator core."""
        self.status_label.config(text=f"Loading {os.path.basename(path)}...")
        self.update_idletasks()
        
        success = self.core.load_rom(path)
        if success:
            game_name = self.core.game_info.get("game_name", "Unknown")
            self.status_label.config(text=f"Loaded: {game_name}")
            # Update canvas info text
            self.canvas.itemconfig(self.info_text, text=f"Loaded: {game_name}\nPress Start to begin emulation")
            # Enable start button visually
            self.btn_start.config(state=tk.NORMAL)
        else:
            messagebox.showerror("Load Error", f"Failed to load ROM:\n{path}\nFile may be corrupted or not a valid GameCube image.")
            self.status_label.config(text="Failed to load ROM")
    
    def start_emulation(self):
        """Start the emulation core."""
        if self.core.rom_path is None:
            messagebox.showwarning("No ROM", "Please load a GameCube ROM first.")
            return
        if not self.core.running:
            try:
                self.core.start()
                self.status_label.config(text="Emulation running")
                self.canvas.itemconfig(self.info_text, text="Emulation Active\n60 FPS Mode")
                # Disable start button while running
                self.btn_start.config(state=tk.DISABLED)
                self.btn_pause.config(state=tk.NORMAL)
                self.btn_stop.config(state=tk.NORMAL)
            except Exception as e:
                messagebox.showerror("Start Error", str(e))
        elif self.core.paused:
            self.core.resume()
            self.status_label.config(text="Emulation resumed")
            self.btn_pause.config(text="⏸ Pause")
    
    def pause_emulation(self):
        """Pause the emulation."""
        if self.core.running and not self.core.paused:
            self.core.pause()
            self.status_label.config(text="Emulation paused")
            self.btn_pause.config(text="▶ Resume")
    
    def stop_emulation(self):
        """Stop the emulation."""
        if self.core.running:
            self.core.stop()
            self.status_label.config(text="Emulation stopped")
            self.canvas.itemconfig(self.info_text, text="Stopped\nLoad ROM and press Start")
            self.btn_start.config(state=tk.NORMAL)
            self.btn_pause.config(state=tk.DISABLED, text="⏸ Pause")
            self.btn_stop.config(state=tk.DISABLED)
    
    def reset_emulation(self):
        """Reset the emulation state."""
        if self.core.rom_path:
            self.stop_emulation()
            self._load_rom(self.core.rom_path)
            self.start_emulation()
    
    def show_graphics_settings(self):
        """Placeholder for graphics settings dialog."""
        messagebox.showinfo("Graphics Settings", "Graphics configuration will be available in future versions.\nCurrently using software rendering.")
    
    def toggle_fullscreen(self):
        """Toggle fullscreen mode."""
        current = self.attributes("-fullscreen")
        self.attributes("-fullscreen", not current)
        if not current:
            self.btn_fullscreen.config(text="🖥 Windowed")
        else:
            self.btn_fullscreen.config(text="🖥 Fullscreen")
    
    def memory_card_manager(self):
        """Placeholder for memory card manager."""
        messagebox.showinfo("Memory Card Manager", "Memory card emulation will be added in a future update.")
    
    def show_about(self):
        """Show about dialog."""
        about_text = """AC'S Dolphin emu 0.1
GameCube Emulator Frontend

A high-performance emulator GUI with 60 FPS target.
This is a demonstration build with a fake 3D cube renderer.

For real GameCube emulation:
- Replace EmulatorCore with actual CPU/GPU emulation
- Integrate with Dolphin's core via Cython or ctypes

Written in Python using tkinter.
© 2025"""
        messagebox.showinfo("About AC'S Dolphin emu", about_text)
    
    def _schedule_frame_update(self):
        """Schedule the next frame update using tkinter's after."""
        now = time.time()
        delta = now - self.last_frame_time
        self.last_frame_time = now
        
        # Update emulation core with delta time
        self.core.update(delta)
        
        # Render current frame to canvas
        self._draw_frame()
        
        # Update status bar FPS and speed info
        if self.core.running and not self.core.paused:
            fps = self.core.fps
            speed_percent = (fps / TARGET_FPS) * 100 if fps > 0 else 0
            self.toolbar_fps_label.config(text=f"FPS: {fps:.1f} | Speed: {speed_percent:.0f}%")
            self.speed_label.config(text=f"{speed_percent:.0f}% Speed")
        else:
            self.toolbar_fps_label.config(text="FPS: -- | Speed: --%")
            self.speed_label.config(text="Stopped")
        
        # Update status string
        self.status_label.config(text=self.core.get_status_string())
        
        # Schedule next frame
        self.emulation_loop_id = self.after(FRAME_TIME_MS, self._schedule_frame_update)
    
    def _draw_frame(self):
        """Render the emulated framebuffer onto the canvas."""
        # Get framebuffer from core
        width = self.canvas.winfo_width() if self.canvas.winfo_width() > 10 else CANVAS_WIDTH
        height = self.canvas.winfo_height() if self.canvas.winfo_height() > 10 else CANVAS_HEIGHT
        
        # Keep aspect ratio? We'll just scale to fit canvas
        if self.core.running:
            frame = self.core.get_frame_surface(width, height)
            # Convert to PhotoImage for display
            img_data = bytearray()
            for r, g, b in frame:
                img_data.extend([r, g, b])
            
            try:
                from PIL import Image, ImageTk
                # Use PIL for smooth scaling if available
                img = Image.frombytes("RGB", (width, height), bytes(img_data))
                self.photo = ImageTk.PhotoImage(img)
                self.canvas.delete("frame_img")
                self.canvas.create_image(width//2, height//2, image=self.photo, tags="frame_img")
                self.canvas.tag_lower("frame_img")
                # Hide info text if emulation is running
                self.canvas.itemconfig(self.info_text, state=tk.HIDDEN)
            except ImportError:
                # Fallback: draw pixel by pixel (slow but works without PIL)
                self.canvas.delete("frame_img")
                # Simple rectangle placeholder
                self.canvas.create_rectangle(0, 0, width, height, fill="#0a0a2a", outline="", tags="frame_img")
                self.canvas.create_text(width//2, height//2, text="Install Pillow for better rendering", fill="white", tags="frame_img")
        else:
            # Show info text
            self.canvas.itemconfig(self.info_text, state=tk.NORMAL)
            self.canvas.delete("frame_img")
    
    def on_closing(self):
        """Handle window close event."""
        if self.emulation_loop_id:
            self.after_cancel(self.emulation_loop_id)
        self.core.stop()
        self.destroy()


# ----------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------
if __name__ == "__main__":
    # Check for required libraries (PIL is optional but recommended)
    try:
        from PIL import Image, ImageTk
    except ImportError:
        print("Warning: Pillow (PIL) not installed. Install for better rendering: pip install Pillow")
    
    app = DolphinEmulatorGUI()
    app.mainloop()
