"""
Smart Parking Management System — Professional Edition v2
Redesigned UI: premium dark theme, scrollable exit panel, large bill actions
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import cv2
from PIL import Image, ImageTk
import numpy as np
from datetime import datetime
import json, os, re
from threading import Thread
import time

# ─────────────────────────────────────────────────────────────────────────────
# Colour palette
# ─────────────────────────────────────────────────────────────────────────────
C = {
    'bg0':     '#050c1a',   # deepest background
    'bg1':     '#0b1528',   # panels / cards
    'bg2':     '#112038',   # slightly lighter card interior
    'bg3':     '#172948',   # input fields, lists
    'border':  '#1d3050',
    'border2': '#254070',
    'blue':    '#3b82f6',
    'blue_dk': '#1d4ed8',
    'cyan':    '#06b6d4',
    'green':   '#10b981',
    'green_dk':'#059669',
    'red':     '#ef4444',
    'red_dk':  '#b91c1c',
    'yellow':  '#f59e0b',
    'orange':  '#f97316',
    'purple':  '#8b5cf6',
    'txt0':    '#e2e8f0',   # primary text
    'txt1':    '#7a95b8',   # secondary text
    'txt2':    '#3a5070',   # muted / disabled
    'white':   '#ffffff',
}

FONT_TITLE  = ('Consolas', 22, 'bold')
FONT_HEAD   = ('Consolas', 12, 'bold')
FONT_BODY   = ('Segoe UI', 10)
FONT_BODY_B = ('Segoe UI', 10, 'bold')
FONT_SMALL  = ('Segoe UI', 9)
FONT_PLATE  = ('Consolas', 20, 'bold')
FONT_NUM    = ('Consolas', 28, 'bold')
FONT_MONO   = ('Consolas', 10)


def card(parent, **kw):
    """Rounded-ish card frame."""
    return tk.Frame(parent, bg=C['bg1'], relief='flat', bd=0, **kw)


def label(parent, text, font=FONT_BODY, fg=C['txt0'], bg=None, **kw):
    bg = bg or parent.cget('bg')
    return tk.Label(parent, text=text, font=font, fg=fg, bg=bg, **kw)


def sep(parent, color=C['border'], height=1, pady=8):
    f = tk.Frame(parent, bg=color, height=height)
    f.pack(fill='x', pady=pady)
    return f


class IconButton(tk.Frame):
    """Custom flat button with hover effect."""
    def __init__(self, parent, text, command=None,
                 bg=C['bg2'], hover=C['border2'],
                 fg=C['txt0'], font=FONT_BODY_B,
                 padx=16, pady=8, **kw):
        super().__init__(parent, bg=bg, cursor='hand2', **kw)
        self._bg = bg
        self._hover = hover
        self._cmd = command
        self._lbl = tk.Label(self, text=text, font=font,
                             fg=fg, bg=bg, padx=padx, pady=pady)
        self._lbl.pack(fill='both', expand=True)
        for w in (self, self._lbl):
            w.bind('<Enter>', self._on_enter)
            w.bind('<Leave>', self._on_leave)
            w.bind('<Button-1>', self._on_click)

    def _on_enter(self, _=None):
        self.configure(bg=self._hover)
        self._lbl.configure(bg=self._hover)

    def _on_leave(self, _=None):
        self.configure(bg=self._bg)
        self._lbl.configure(bg=self._bg)

    def _on_click(self, _=None):
        if self._cmd:
            self._cmd()

    def configure_colors(self, bg, hover):
        self._bg, self._hover = bg, hover
        self.configure(bg=bg)
        self._lbl.configure(bg=bg)


class BigButton(tk.Frame):
    """Large action button with coloured background + glow border."""
    def __init__(self, parent, text, command=None,
                 bg=C['green'], hover=C['green_dk'],
                 fg=C['white'], font=FONT_HEAD,
                 height=52, **kw):
        super().__init__(parent, bg=bg, cursor='hand2',
                         height=height, **kw)
        self.pack_propagate(False)
        self._bg = bg
        self._hover = hover
        self._cmd = command
        self._lbl = tk.Label(self, text=text, font=font,
                             fg=fg, bg=bg)
        self._lbl.pack(fill='both', expand=True)
        for w in (self, self._lbl):
            w.bind('<Enter>', self._on_enter)
            w.bind('<Leave>', self._on_leave)
            w.bind('<Button-1>', self._on_click)

    def _on_enter(self, _=None):
        self.configure(bg=self._hover)
        self._lbl.configure(bg=self._hover)

    def _on_leave(self, _=None):
        self.configure(bg=self._bg)
        self._lbl.configure(bg=self._bg)

    def _on_click(self, _=None):
        if self._cmd:
            self._cmd()


class ModernParkingSystem:

    def __init__(self, root):
        self.root = root
        self.root.title("Smart Parking Management System")
        self.root.geometry("1440x900")
        self.root.configure(bg=C['bg0'])
        self.root.minsize(1200, 760)

        self.current_frame_entry  = None
        self.current_frame_exit   = None
        self.video_capture_entry  = None
        self.video_capture_exit   = None
        self.camera_running_entry = False
        self.camera_running_exit  = False

        # ── Video / auto-detect state ────────────────────────────────────────
        self._frame_count   = {'entry': 0, 'exit': 0}   # frames since last detect
        self._detecting     = {'entry': False, 'exit': False}  # thread guard
        self._detect_every  = 20   # auto-detect every N frames (~0.6 s at 30 fps)
        #   ↑ Tune: lower = more frequent (more CPU), higher = less frequent

        # ── Multi-vote system ─────────────────────────────────────────────────
        # A plate must be detected VOTE_THRESHOLD times consistently within
        # VOTE_WINDOW seconds before auto-registration fires.
        self._VOTE_THRESHOLD = 3
        self._VOTE_WINDOW    = 20.0   # seconds — votes older than this are dropped
        self._vote_log:  dict = {'entry': [], 'exit': []}   # [(timestamp, plate), …]
        self._vote_label: dict = {'entry': None, 'exit': None}  # UI label refs

        # ── Cooldown: prevent the same plate firing twice within N seconds ────
        self._last_registered: dict = {}   # key: f"{mode}:{plate_clean}"
        self._register_cooldown = 10.0     # seconds

        # ── Exit bill state: store pending exit data until payment confirmed ──
        self._pending_exit: dict = {}      # plate → exit data while dialog open

        self.registered_vehicles  = {}
        self.settings  = self.load_settings()
        self.update_timers = True

        self.load_models()
        self.setup_styles()
        self.setup_ui()
        self.load_vehicles()
        self.start_timer_updates()

    # ── Persistence ───────────────────────────────────────────────────────────

    def load_settings(self):
        defaults = {'2w_capacity': 50, '4w_capacity': 30,
                    '2w_rate': 20,     '4w_rate': 50,
                    '2w_occupied': 0,  '4w_occupied': 0}
        if os.path.exists('parking_settings.json'):
            try:
                with open('parking_settings.json') as f:
                    content = f.read().strip()
                    if content:
                        defaults.update(json.loads(content))
            except Exception:
                pass
        return defaults

    def save_settings(self):
        with open('parking_settings.json', 'w') as f:
            json.dump(self.settings, f, indent=4)

    def save_vehicles(self):
        with open('registered_vehicles.json', 'w') as f:
            json.dump(self.registered_vehicles, f, indent=4)

    def load_vehicles(self):
        if os.path.exists('registered_vehicles.json'):
            try:
                with open('registered_vehicles.json') as f:
                    content = f.read().strip()
                    if content:
                        self.registered_vehicles = json.loads(content)
            except Exception:
                self.registered_vehicles = {}
        self.update_dashboard()

    # ── Model loading ─────────────────────────────────────────────────────────

    def load_models(self):
        try:
            from ultralytics import YOLO
            self.plate_detection_model = YOLO('models/detect_plate.pt')
            self.text_extraction_model = YOLO('models/robo_best.pt')
            self.models_loaded = True
            print("✓ Both models loaded")
        except Exception as e:
            print(f"⚠ Models not loaded: {e}")
            self.plate_detection_model = None
            self.text_extraction_model = None
            self.models_loaded = False

    # ── TTK Styles ────────────────────────────────────────────────────────────

    def setup_styles(self):
        s = ttk.Style()
        s.theme_use('clam')

        s.configure('.', background=C['bg0'], foreground=C['txt0'],
                    borderwidth=0, focuscolor='none')

        s.configure('TNotebook', background=C['bg0'], borderwidth=0,
                    tabmargins=[0, 0, 0, 0])
        s.configure('TNotebook.Tab',
                    background=C['bg1'], foreground=C['txt1'],
                    padding=[24, 13], borderwidth=0,
                    font=('Segoe UI', 10, 'bold'))
        s.map('TNotebook.Tab',
              background=[('selected', C['bg2'])],
              foreground=[('selected', C['blue'])],
              expand=[('selected', [0, 0, 0, 0])])

        s.configure('TFrame', background=C['bg0'])
        s.configure('TLabel', background=C['bg1'], foreground=C['txt0'],
                    font=FONT_BODY)
        s.configure('TLabelframe', background=C['bg1'], borderwidth=1,
                    relief='solid', bordercolor=C['border'])
        s.configure('TLabelframe.Label', background=C['bg1'],
                    foreground=C['txt0'], font=FONT_BODY_B)
        s.configure('TEntry', fieldbackground=C['bg3'], foreground=C['txt0'],
                    borderwidth=1, insertcolor=C['txt0'])
        s.configure('TRadiobutton', background=C['bg1'],
                    foreground=C['txt0'], font=FONT_BODY)
        s.configure('Vertical.TScrollbar', background=C['bg3'],
                    troughcolor=C['bg1'], arrowcolor=C['txt1'],
                    borderwidth=0)

    # ── Top-level UI ──────────────────────────────────────────────────────────

    def setup_ui(self):
        self._build_header()

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill='both', expand=True)

        self.entry_tab     = ttk.Frame(self.notebook)
        self.exit_tab      = ttk.Frame(self.notebook)
        self.dashboard_tab = ttk.Frame(self.notebook)
        self.settings_tab  = ttk.Frame(self.notebook)

        self.notebook.add(self.entry_tab,     text='  🚘  ENTRY  ')
        self.notebook.add(self.exit_tab,      text='  🚪  EXIT  ')
        self.notebook.add(self.dashboard_tab, text='  📊  DASHBOARD  ')
        self.notebook.add(self.settings_tab,  text='  ⚙  SETTINGS  ')

        self.setup_entry_tab()
        self.setup_exit_tab()
        self.setup_dashboard_tab()
        self.setup_settings_tab()
        self._build_statusbar()

    # ── Header ────────────────────────────────────────────────────────────────

    def _build_header(self):
        hdr = tk.Frame(self.root, bg=C['bg1'], height=72)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)

        # Left — logo + title
        left = tk.Frame(hdr, bg=C['bg1'])
        left.pack(side='left', padx=24, pady=0, fill='y')

        # Coloured accent bar
        accent = tk.Frame(left, bg=C['blue'], width=4)
        accent.pack(side='left', fill='y', pady=12)

        txt = tk.Frame(left, bg=C['bg1'])
        txt.pack(side='left', padx=(12, 0), pady=12)

        tk.Label(txt, text="SMART PARKING", font=('Consolas', 20, 'bold'),
                 bg=C['bg1'], fg=C['txt0']).pack(anchor='w')
        tk.Label(txt, text="Management System  —  Professional Edition",
                 font=('Segoe UI', 9), bg=C['bg1'], fg=C['txt1']).pack(anchor='w')

        # Right — status chips + clock
        right = tk.Frame(hdr, bg=C['bg1'])
        right.pack(side='right', padx=28, fill='y')

        # Clock
        self.time_label = tk.Label(right, text="",
                                   font=('Consolas', 11, 'bold'),
                                   bg=C['bg1'], fg=C['txt0'])
        self.time_label.pack(anchor='e')

        # Status chip
        chip = tk.Frame(right, bg=C['bg0'], bd=0)
        chip.pack(anchor='e', pady=(4, 0))
        tk.Label(chip, text="●", font=('Segoe UI', 8), fg=C['green'],
                 bg=C['bg0']).pack(side='left', padx=(6, 2))
        tk.Label(chip, text="SYSTEM ONLINE", font=('Segoe UI', 8, 'bold'),
                 fg=C['green'], bg=C['bg0']).pack(side='left', padx=(0, 6))

        # Thin bottom border
        tk.Frame(self.root, bg=C['border'], height=1).pack(fill='x')

        self._update_clock()

    def _update_clock(self):
        self.time_label.config(text=datetime.now().strftime("%a %d %b %Y   %H:%M:%S"))
        self.root.after(1000, self._update_clock)

    # ── Status bar ────────────────────────────────────────────────────────────

    def _build_statusbar(self):
        bar = tk.Frame(self.root, bg=C['bg1'], height=28)
        bar.pack(fill='x', side='bottom')
        bar.pack_propagate(False)
        tk.Frame(self.root, bg=C['border'], height=1).pack(
            fill='x', side='bottom')

        self.status_label = tk.Label(
            bar, text="●  Ready", anchor='w', padx=16,
            bg=C['bg1'], fg=C['txt1'], font=('Segoe UI', 9))
        self.status_label.pack(side='left', fill='y')

        # Right side — version tag
        tk.Label(bar, text="v2.0  |  AI-Powered ANPR",
                 bg=C['bg1'], fg=C['txt2'], font=('Segoe UI', 8),
                 anchor='e', padx=16).pack(side='right', fill='y')

    def _set_status(self, text, color=C['txt1']):
        self.status_label.config(text=f"●  {text}", fg=color)

    # ─────────────────────────────────────────────────────────────────────────
    # ENTRY TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_entry_tab(self):
        root_f = tk.Frame(self.entry_tab, bg=C['bg0'])
        root_f.pack(fill='both', expand=True, padx=16, pady=16)

        # ── Left: camera card ────────────────────────────────────────────────
        cam_card = card(root_f)
        cam_card.pack(side='left', fill='both', expand=True, padx=(0, 10))

        # Camera card header
        ch = tk.Frame(cam_card, bg=C['bg2'], height=44)
        ch.pack(fill='x')
        ch.pack_propagate(False)
        tk.Label(ch, text="📹  CAMERA FEED", font=FONT_HEAD,
                 bg=C['bg2'], fg=C['txt0']).pack(side='left', padx=16, pady=10)

        # Toolbar
        tb = tk.Frame(cam_card, bg=C['bg1'], height=48)
        tb.pack(fill='x')
        tb.pack_propagate(False)
        for txt, cmd, bg, hv in [
            ("📁  Image",  lambda: self.select_image('entry'), C['bg2'],    C['border2']),
            ("🎥  Video",  lambda: self.select_video('entry'), C['bg2'],    C['border2']),
            ("📷  Camera", lambda: self.start_camera('entry'), C['blue'],   C['blue_dk']),
            ("⏹  Stop",   lambda: self.stop_camera('entry'),  C['red'],    C['red_dk']),
        ]:
            IconButton(tb, txt, command=cmd, bg=bg, hover=hv,
                       fg=C['white'], padx=18, pady=8).pack(
                side='left', padx=(8, 0), pady=8)

        # Video display
        self.video_label_entry = tk.Label(cam_card, bg='#000', text="No feed",
                                          fg=C['txt2'], font=FONT_BODY)
        self.video_label_entry.pack(fill='both', expand=True, padx=2, pady=(0, 2))

        # ── Right: registration card ─────────────────────────────────────────
        reg_card = card(root_f)
        reg_card.pack(side='right', fill='y', padx=(10, 0))
        reg_card.configure(width=390)
        reg_card.pack_propagate(False)

        # Header bar
        rh = tk.Frame(reg_card, bg=C['bg2'], height=44)
        rh.pack(fill='x')
        rh.pack_propagate(False)
        tk.Label(rh, text="🎯  VEHICLE REGISTRATION", font=FONT_HEAD,
                 bg=C['bg2'], fg=C['txt0']).pack(side='left', padx=16, pady=10)

        # Scrollable inner content
        inner = tk.Frame(reg_card, bg=C['bg1'])
        inner.pack(fill='both', expand=True, padx=16, pady=12)

        # Vehicle type
        self._section_label(inner, "VEHICLE TYPE")
        self.vehicle_type_entry = tk.StringVar(value="2W")
        vt_row = tk.Frame(inner, bg=C['bg1'])
        vt_row.pack(fill='x', pady=(4, 12))
        for lbl, val in [("🏍️  2-Wheeler", "2W"), ("🚗  4-Wheeler", "4W")]:
            ttk.Radiobutton(vt_row, text=lbl,
                            variable=self.vehicle_type_entry,
                            value=val).pack(side='left', padx=8)

        # Detect button
        BigButton(inner, "🔍   DETECT NUMBER PLATE",
                  command=lambda: self.detect_vehicle('entry'),
                  bg=C['blue'], hover=C['blue_dk'],
                  height=46).pack(fill='x', pady=(0, 14))

        # Plate input
        self._section_label(inner, "NUMBER PLATE")
        self.number_plate_entry = tk.Entry(
            inner, font=FONT_PLATE,
            bg=C['bg3'], fg=C['cyan'],
            insertbackground=C['txt0'],
            relief='flat', bd=0, justify='center')
        self.number_plate_entry.pack(fill='x', ipady=12, pady=(4, 4))
        tk.Frame(inner, bg=C['cyan'], height=2).pack(fill='x')

        self.detection_info_entry = tk.Label(
            inner, text="", font=FONT_SMALL,
            bg=C['bg1'], fg=C['txt1'], wraplength=340)
        self.detection_info_entry.pack(pady=(4, 4))

        # ── Vote progress indicator ───────────────────────────────────────────
        self._vote_label['entry'] = tk.Label(
            inner, text="", font=('Consolas', 9, 'bold'),
            bg=C['bg1'], fg=C['yellow'], wraplength=340)
        self._vote_label['entry'].pack(pady=(0, 8))

        sep(inner, pady=10)

        # Entry info box
        self._section_label(inner, "ENTRY DETAILS")
        info_box = tk.Frame(inner, bg=C['bg2'], bd=0)
        info_box.pack(fill='x', pady=(6, 0))

        self.entry_time_label = self._info_row(info_box, "⏱  Entry Time", "—")
        self.entry_rate_label = self._info_row(info_box, "💰  Tariff",    "—")

        # Spacer then big register button
        tk.Frame(inner, bg=C['bg1'], height=16).pack()
        BigButton(inner, "✅   REGISTER VEHICLE ENTRY",
                  command=self.register_entry,
                  bg=C['green'], hover=C['green_dk'],
                  height=52).pack(fill='x', pady=(0, 6))

    # ─────────────────────────────────────────────────────────────────────────
    # EXIT TAB  (fully scrollable right panel + large bill button)
    # ─────────────────────────────────────────────────────────────────────────

    def setup_exit_tab(self):
        root_f = tk.Frame(self.exit_tab, bg=C['bg0'])
        root_f.pack(fill='both', expand=True, padx=16, pady=16)

        # ── Left: camera card ────────────────────────────────────────────────
        cam_card = card(root_f)
        cam_card.pack(side='left', fill='both', expand=True, padx=(0, 10))

        ch = tk.Frame(cam_card, bg=C['bg2'], height=44)
        ch.pack(fill='x')
        ch.pack_propagate(False)
        tk.Label(ch, text="📹  CAMERA FEED", font=FONT_HEAD,
                 bg=C['bg2'], fg=C['txt0']).pack(side='left', padx=16, pady=10)

        tb = tk.Frame(cam_card, bg=C['bg1'], height=48)
        tb.pack(fill='x')
        tb.pack_propagate(False)
        for txt, cmd, bg, hv in [
            ("📁  Image",  lambda: self.select_image('exit'), C['bg2'],  C['border2']),
            ("🎥  Video",  lambda: self.select_video('exit'), C['bg2'],  C['border2']),
            ("📷  Camera", lambda: self.start_camera('exit'), C['blue'], C['blue_dk']),
            ("⏹  Stop",   lambda: self.stop_camera('exit'),  C['red'],  C['red_dk']),
        ]:
            IconButton(tb, txt, command=cmd, bg=bg, hover=hv,
                       fg=C['white'], padx=18, pady=8).pack(
                side='left', padx=(8, 0), pady=8)

        self.video_label_exit = tk.Label(cam_card, bg='#000', text="No feed",
                                         fg=C['txt2'], font=FONT_BODY)
        self.video_label_exit.pack(fill='both', expand=True, padx=2, pady=(0, 2))

        # ── Right: exit panel (scrollable) ───────────────────────────────────
        exit_card = card(root_f)
        exit_card.pack(side='right', fill='y', padx=(10, 0))
        exit_card.configure(width=420)
        exit_card.pack_propagate(False)

        # Header
        eh = tk.Frame(exit_card, bg=C['red_dk'], height=44)
        eh.pack(fill='x')
        eh.pack_propagate(False)
        tk.Label(eh, text="🚪  VEHICLE EXIT & BILLING", font=FONT_HEAD,
                 bg=C['red_dk'], fg=C['white']).pack(side='left', padx=16, pady=10)

        # ── Scrollable canvas wrapper ─────────────────────────────────────────
        scroll_container = tk.Frame(exit_card, bg=C['bg1'])
        scroll_container.pack(fill='both', expand=True)

        canvas = tk.Canvas(scroll_container, bg=C['bg1'],
                           highlightthickness=0, bd=0)
        scrollbar = ttk.Scrollbar(scroll_container, orient='vertical',
                                  command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)

        scrollbar.pack(side='right', fill='y')
        canvas.pack(side='left', fill='both', expand=True)

        # Scrollable frame inside canvas
        scroll_frame = tk.Frame(canvas, bg=C['bg1'])
        canvas_window = canvas.create_window((0, 0), window=scroll_frame,
                                              anchor='nw')

        def _on_frame_configure(_):
            canvas.configure(scrollregion=canvas.bbox('all'))

        def _on_canvas_configure(e):
            canvas.itemconfig(canvas_window, width=e.width)

        scroll_frame.bind('<Configure>', _on_frame_configure)
        canvas.bind('<Configure>', _on_canvas_configure)

        # Mouse-wheel scrolling
        def _on_mousewheel(e):
            canvas.yview_scroll(int(-1 * (e.delta / 120)), 'units')

        canvas.bind_all('<MouseWheel>', _on_mousewheel)

        # Scroll arrow hint at top-right
        hint = tk.Frame(exit_card, bg=C['bg0'], height=22)
        hint.pack(fill='x', after=eh)
        tk.Label(hint, text="↕  scroll panel", font=('Segoe UI', 8),
                 bg=C['bg0'], fg=C['txt2']).pack(anchor='e', padx=8)

        # ── Content inside scroll_frame ───────────────────────────────────────
        pad = tk.Frame(scroll_frame, bg=C['bg1'])
        pad.pack(fill='x', padx=16, pady=12)

        # Vehicle type
        self._section_label(pad, "VEHICLE TYPE")
        self.vehicle_type_exit = tk.StringVar(value="2W")
        vt_row = tk.Frame(pad, bg=C['bg1'])
        vt_row.pack(fill='x', pady=(4, 12))
        for lbl, val in [("🏍️  2-Wheeler", "2W"), ("🚗  4-Wheeler", "4W")]:
            ttk.Radiobutton(vt_row, text=lbl,
                            variable=self.vehicle_type_exit,
                            value=val).pack(side='left', padx=8)

        # Detect
        BigButton(pad, "🔍   DETECT NUMBER PLATE",
                  command=lambda: self.detect_vehicle('exit'),
                  bg=C['blue'], hover=C['blue_dk'],
                  height=46).pack(fill='x', pady=(0, 14))

        # Plate entry
        self._section_label(pad, "NUMBER PLATE")
        self.number_plate_exit = tk.Entry(
            pad, font=FONT_PLATE,
            bg=C['bg3'], fg=C['cyan'],
            insertbackground=C['txt0'],
            relief='flat', bd=0, justify='center')
        self.number_plate_exit.pack(fill='x', ipady=12, pady=(4, 4))
        tk.Frame(pad, bg=C['cyan'], height=2).pack(fill='x')

        self.detection_info_exit = tk.Label(
            pad, text="", font=FONT_SMALL,
            bg=C['bg1'], fg=C['txt1'], wraplength=360)
        self.detection_info_exit.pack(pady=(4, 4))

        # ── Vote progress indicator ───────────────────────────────────────────
        self._vote_label['exit'] = tk.Label(
            pad, text="", font=('Consolas', 9, 'bold'),
            bg=C['bg1'], fg=C['yellow'], wraplength=360)
        self._vote_label['exit'].pack(pady=(0, 8))

        sep(pad, pady=10)

        # ── Bill Preview ──────────────────────────────────────────────────────
        self._section_label(pad, "BILL PREVIEW")
        bill_card = tk.Frame(pad, bg=C['bg0'], bd=0)
        bill_card.pack(fill='x', pady=(6, 0))

        # Coloured header stripe
        bh = tk.Frame(bill_card, bg=C['yellow'], height=32)
        bh.pack(fill='x')
        tk.Label(bh, text="🧾  PARKING RECEIPT",
                 font=('Consolas', 10, 'bold'),
                 bg=C['yellow'], fg=C['bg0']).pack(side='left', padx=12, pady=6)

        # Bill rows container
        self.bill_rows_frame = tk.Frame(bill_card, bg=C['bg0'])
        self.bill_rows_frame.pack(fill='x', padx=0)

        self._build_bill_placeholder()

        sep(pad, color=C['border2'], pady=14)

        # ── BIG GENERATE BILL BUTTON ──────────────────────────────────────────
        BigButton(pad, "🚪   PROCESS EXIT  &  GENERATE BILL",
                  command=self.process_exit,
                  bg=C['green'], hover=C['green_dk'],
                  fg=C['white'], font=('Consolas', 13, 'bold'),
                  height=62).pack(fill='x', pady=(0, 8))

        # Quick clear button
        IconButton(pad, "✕  Clear Fields",
                   command=self._clear_exit_fields,
                   bg=C['bg2'], hover=C['border'],
                   fg=C['txt1'], font=FONT_SMALL).pack(fill='x', pady=(0, 16))

    def _build_bill_placeholder(self):
        """Show placeholder rows when no bill is loaded."""
        for w in self.bill_rows_frame.winfo_children():
            w.destroy()
        rows = [("Vehicle", "—"), ("Type", "—"), ("Entry", "—"),
                ("Exit", "—"), ("Duration", "—"), ("Rate", "—"),
                ("Subtotal", "—"), ("TOTAL", "—")]
        for i, (k, v) in enumerate(rows):
            bg = C['bg1'] if i % 2 == 0 else C['bg0']
            row = tk.Frame(self.bill_rows_frame, bg=bg)
            row.pack(fill='x')
            bold = i == len(rows) - 1
            fg_k = C['txt1']
            fg_v = C['yellow'] if bold else C['txt0']
            fnt  = ('Consolas', 11, 'bold') if bold else FONT_MONO
            tk.Label(row, text=f"  {k}", font=fnt, fg=fg_k,
                     bg=bg, width=14, anchor='w').pack(side='left', pady=5)
            tk.Label(row, text=v, font=fnt, fg=fg_v,
                     bg=bg, anchor='e').pack(side='right', padx=12, pady=5)

    def _populate_bill(self, plate, data, entry, exit_t, duration,
                       rate, raw, final):
        """Fill bill rows with real data."""
        for w in self.bill_rows_frame.winfo_children():
            w.destroy()
        rows = [
            ("Vehicle",  plate),
            ("Type",     data['type']),
            ("Entry",    entry.strftime('%d %b  %H:%M:%S')),
            ("Exit",     exit_t.strftime('%d %b  %H:%M:%S')),
            ("Duration", f"{duration:.2f} hrs"),
            ("Rate",     f"Rs. {rate}/hr"),
            ("Subtotal", f"Rs. {raw:.2f}"),
            ("TOTAL",    f"Rs. {final}"),
        ]
        for i, (k, v) in enumerate(rows):
            bg   = C['bg1'] if i % 2 == 0 else C['bg0']
            bold = i == len(rows) - 1
            row  = tk.Frame(self.bill_rows_frame, bg=bg)
            row.pack(fill='x')
            fg_k = C['txt1']
            fg_v = C['yellow'] if bold else C['txt0']
            fnt  = ('Consolas', 12, 'bold') if bold else FONT_MONO
            if bold:
                tk.Frame(self.bill_rows_frame, bg=C['yellow'],
                         height=1).pack(fill='x', before=row)
            tk.Label(row, text=f"  {k}", font=fnt, fg=fg_k,
                     bg=bg, width=14, anchor='w').pack(side='left', pady=6)
            tk.Label(row, text=v, font=fnt, fg=fg_v,
                     bg=bg, anchor='e').pack(side='right', padx=12, pady=6)

    def _clear_exit_fields(self):
        self.number_plate_exit.delete(0, tk.END)
        self.detection_info_exit.config(text="")
        self._build_bill_placeholder()

    # ─────────────────────────────────────────────────────────────────────────
    # DASHBOARD TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_dashboard_tab(self):
        root_f = tk.Frame(self.dashboard_tab, bg=C['bg0'])
        root_f.pack(fill='both', expand=True, padx=16, pady=16)

        # ── Top KPI row ───────────────────────────────────────────────────────
        kpi_row = tk.Frame(root_f, bg=C['bg0'])
        kpi_row.pack(fill='x', pady=(0, 14))

        self._kpi_card(kpi_row, "2-Wheeler", "🏍",  "2w")
        self._kpi_card(kpi_row, "4-Wheeler", "🚗", "4w")
        self._revenue_kpi(kpi_row)

        # ── Vehicle lists ─────────────────────────────────────────────────────
        list_row = tk.Frame(root_f, bg=C['bg0'])
        list_row.pack(fill='both', expand=True)

        self._vehicle_list_panel(list_row, "2W", side='left')
        self._vehicle_list_panel(list_row, "4W", side='right')

        # Refresh
        btn_row = tk.Frame(root_f, bg=C['bg0'])
        btn_row.pack(fill='x', pady=(12, 0))
        BigButton(btn_row, "🔄   REFRESH DASHBOARD",
                  command=self.update_dashboard,
                  bg=C['blue'], hover=C['blue_dk'],
                  height=40, font=FONT_BODY_B).pack(side='left')

    def _kpi_card(self, parent, title, icon, vtype):
        card_f = tk.Frame(parent, bg=C['bg1'], bd=0)
        card_f.pack(side='left', fill='both', expand=True, padx=(0, 10))

        # Accent top stripe
        stripe_color = C['blue'] if vtype == '2w' else C['purple']
        tk.Frame(card_f, bg=stripe_color, height=4).pack(fill='x')

        inner = tk.Frame(card_f, bg=C['bg1'])
        inner.pack(fill='both', padx=18, pady=14)

        head = tk.Frame(inner, bg=C['bg1'])
        head.pack(fill='x')
        tk.Label(head, text=icon, font=('Segoe UI', 22),
                 bg=C['bg1'], fg=stripe_color).pack(side='left')
        tk.Label(head, text=title, font=FONT_BODY_B,
                 bg=C['bg1'], fg=C['txt1']).pack(side='left', padx=8)

        # Big occupancy number
        lbl_name = f"{vtype}_occupied_label"
        lbl = tk.Label(inner, text="0 / 0", font=('Consolas', 32, 'bold'),
                       bg=C['bg1'], fg=stripe_color)
        lbl.pack(anchor='w', pady=(8, 2))
        setattr(self, lbl_name, lbl)

        tk.Label(inner, text="Occupied  /  Capacity",
                 font=FONT_SMALL, bg=C['bg1'], fg=C['txt2']).pack(anchor='w')

        # Progress bar
        bar_bg = tk.Frame(inner, bg=C['bg3'], height=6)
        bar_bg.pack(fill='x', pady=(10, 0))
        bar_fill_name = f"{vtype}_bar_fill"
        bar_fill = tk.Frame(bar_bg, bg=stripe_color, height=6, width=0)
        bar_fill.place(x=0, y=0, relheight=1.0, relwidth=0.0)
        setattr(self, bar_fill_name, bar_fill)
        setattr(self, f"{vtype}_progress_bg", bar_bg)

    def _revenue_kpi(self, parent):
        card_f = tk.Frame(parent, bg=C['bg1'])
        card_f.pack(side='left', fill='both', expand=True, padx=(0, 0))
        tk.Frame(card_f, bg=C['yellow'], height=4).pack(fill='x')
        inner = tk.Frame(card_f, bg=C['bg1'])
        inner.pack(fill='both', padx=18, pady=14)
        head = tk.Frame(inner, bg=C['bg1'])
        head.pack(fill='x')
        tk.Label(head, text="💰", font=('Segoe UI', 22),
                 bg=C['bg1'], fg=C['yellow']).pack(side='left')
        tk.Label(head, text="Live Revenue",
                 font=FONT_BODY_B, bg=C['bg1'], fg=C['txt1']).pack(
                     side='left', padx=8)
        self.revenue_label = tk.Label(inner, text="Rs. 0",
                                      font=('Consolas', 32, 'bold'),
                                      bg=C['bg1'], fg=C['yellow'])
        self.revenue_label.pack(anchor='w', pady=(8, 2))
        tk.Label(inner, text="Accrued from active vehicles",
                 font=FONT_SMALL, bg=C['bg1'], fg=C['txt2']).pack(anchor='w')

    def _vehicle_list_panel(self, parent, vtype, side):
        pf = tk.Frame(parent, bg=C['bg0'])
        pf.pack(side=side, fill='both', expand=True,
                padx=(0, 8) if side == 'left' else (8, 0))

        # Header
        hdr = tk.Frame(pf, bg=C['bg1'], height=40)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)
        icon = "🏍" if vtype == "2W" else "🚗"
        tk.Label(hdr, text=f"{icon}  {vtype} Parked Vehicles",
                 font=FONT_HEAD, bg=C['bg1'], fg=C['txt0']).pack(
                     side='left', padx=14, pady=8)

        # Column headers
        col_hdr = tk.Frame(pf, bg=C['bg2'])
        col_hdr.pack(fill='x')
        for col, w in [("Plate No.", 18), ("Duration", 14), ("Bill (Rs.)", 12)]:
            tk.Label(col_hdr, text=col, font=FONT_SMALL,
                     bg=C['bg2'], fg=C['txt1'],
                     width=w, anchor='w').pack(side='left', padx=6, pady=6)

        # Scrollable list
        canvas = tk.Canvas(pf, bg=C['bg1'], highlightthickness=0)
        vsb = ttk.Scrollbar(pf, orient='vertical', command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side='right', fill='y')
        canvas.pack(fill='both', expand=True)

        sf = tk.Frame(canvas, bg=C['bg1'])
        cw = canvas.create_window((0, 0), window=sf, anchor='nw')

        sf.bind('<Configure>',
                lambda e: canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.bind('<Configure>',
                    lambda e: canvas.itemconfig(cw, width=e.width))

        setattr(self, f"{vtype.lower()}_list_frame", sf)
        setattr(self, f"{vtype.lower()}_list_canvas", canvas)

    # ─────────────────────────────────────────────────────────────────────────
    # SETTINGS TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_settings_tab(self):
        outer = tk.Frame(self.settings_tab, bg=C['bg0'])
        outer.pack(fill='both', expand=True, padx=60, pady=40)

        tk.Label(outer, text="⚙  PARKING CONFIGURATION",
                 font=('Consolas', 18, 'bold'),
                 bg=C['bg0'], fg=C['txt0']).pack(anchor='w', pady=(0, 24))

        settings_card = tk.Frame(outer, bg=C['bg1'])
        settings_card.pack(fill='x')

        self._settings_section(settings_card, "2W", "🏍️  2-Wheeler Settings",
                               C['blue'],   0)
        tk.Frame(settings_card, bg=C['border'], height=1).pack(
            fill='x', padx=32, pady=8)
        self._settings_section(settings_card, "4W", "🚗  4-Wheeler Settings",
                               C['purple'], 1)

        BigButton(outer, "💾   SAVE CONFIGURATION",
                  command=self.save_settings_ui,
                  bg=C['green'], hover=C['green_dk'],
                  height=50, font=FONT_HEAD).pack(
                      anchor='w', pady=(28, 0), ipadx=20)

    def _settings_section(self, parent, vtype, title, color, idx):
        sec = tk.Frame(parent, bg=C['bg1'])
        sec.pack(fill='x', padx=32, pady=(24 if idx == 0 else 8, 8))

        # Title with coloured bar
        trow = tk.Frame(sec, bg=C['bg1'])
        trow.pack(fill='x', pady=(0, 16))
        tk.Frame(trow, bg=color, width=4, height=24).pack(side='left')
        tk.Label(trow, text=title, font=('Segoe UI', 13, 'bold'),
                 bg=C['bg1'], fg=C['txt0']).pack(side='left', padx=10)

        for field_label, var_name, key in [
            ("Total Capacity (spaces)", f"_{vtype.lower()}_capacity_var",
             f"{vtype.lower()}_capacity"),
            ("Hourly Rate (Rs.)",       f"_{vtype.lower()}_rate_var",
             f"{vtype.lower()}_rate"),
        ]:
            row = tk.Frame(sec, bg=C['bg1'])
            row.pack(fill='x', pady=6)
            tk.Label(row, text=field_label, font=FONT_BODY,
                     bg=C['bg1'], fg=C['txt1'],
                     width=26, anchor='w').pack(side='left')
            var = tk.IntVar(value=self.settings[key])
            setattr(self, var_name, var)
            e = tk.Entry(row, textvariable=var, font=FONT_BODY,
                         bg=C['bg3'], fg=C['txt0'],
                         insertbackground=C['txt0'],
                         relief='flat', bd=0, width=12)
            e.pack(side='left', ipady=6, padx=(8, 0))
            tk.Frame(row, bg=color, height=2, width=120).pack(
                side='left', padx=0, pady=0)

    # ─────────────────────────────────────────────────────────────────────────
    # Shared UI helpers
    # ─────────────────────────────────────────────────────────────────────────

    def _section_label(self, parent, text):
        tk.Label(parent, text=text, font=('Consolas', 8, 'bold'),
                 fg=C['txt2'], bg=parent.cget('bg'),
                 anchor='w').pack(fill='x', pady=(6, 0))

    def _info_row(self, parent, key, val):
        row = tk.Frame(parent, bg=parent.cget('bg'))
        row.pack(fill='x', padx=12, pady=3)
        tk.Label(row, text=key, font=FONT_SMALL,
                 fg=C['txt1'], bg=parent.cget('bg'),
                 width=20, anchor='w').pack(side='left')
        lbl = tk.Label(row, text=val, font=('Consolas', 10, 'bold'),
                       fg=C['txt0'], bg=parent.cget('bg'), anchor='e')
        lbl.pack(side='right', padx=4)
        return lbl

    # ─────────────────────────────────────────────────────────────────────────
    # Camera / Video
    # ─────────────────────────────────────────────────────────────────────────

    def select_image(self, mode):
        fp = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.bmp *.webp")])
        if fp:
            self.stop_camera(mode)
            img = cv2.imread(fp)
            if img is None:
                messagebox.showerror("Error", f"Could not read image:\n{fp}")
                return
            if mode == 'entry':
                self.current_frame_entry = img
                self.display_frame(img, 'entry')
            else:
                self.current_frame_exit = img
                self.display_frame(img, 'exit')
            self._set_status(f"Image loaded: {os.path.basename(fp)}", C['cyan'])
            # Auto-run detection immediately on image load
            self._auto_detect_from_frame(img.copy(), mode, source="image")

    def select_video(self, mode):
        fp = filedialog.askopenfilename(
            filetypes=[("Video files", "*.mp4 *.avi *.mov *.mkv *.wmv")])
        if fp:
            self.stop_camera(mode)
            self._frame_count[mode] = 0
            self._vote_log[mode].clear()
            if self._vote_label[mode]:
                self._vote_label[mode].config(text="", fg=C['yellow'])
            cap = cv2.VideoCapture(fp)
            if not cap.isOpened():
                messagebox.showerror("Error", f"Could not open video:\n{fp}")
                return
            if mode == 'entry':
                self.video_capture_entry  = cap
                self.camera_running_entry = True
                self.update_video('entry')
            else:
                self.video_capture_exit  = cap
                self.camera_running_exit = True
                self.update_video('exit')
            self._set_status(f"Video: {os.path.basename(fp)}", C['cyan'])

    def start_camera(self, mode):
        self.stop_camera(mode)
        self._frame_count[mode] = 0
        self._vote_log[mode].clear()
        if self._vote_label[mode]:
            self._vote_label[mode].config(text="", fg=C['yellow'])

        # Try camera index 0, fall back to 1 if not available
        cap = None
        for idx in (0, 1):
            c = cv2.VideoCapture(idx)
            if c.isOpened():
                cap = c
                break
            c.release()

        if cap is None:
            messagebox.showerror("Error",
                "No webcam found. Check camera connection and permissions.")
            return

        # Prefer 720p for better plate resolution
        cap.set(cv2.CAP_PROP_FRAME_WIDTH,  1280)
        cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 720)

        if mode == 'entry':
            self.video_capture_entry  = cap
            self.camera_running_entry = True
            self.update_video('entry')
            self._set_status("🎥 Live webcam active — ENTRY  (auto-detecting)", C['green'])
        else:
            self.video_capture_exit  = cap
            self.camera_running_exit = True
            self.update_video('exit')
            self._set_status("🎥 Live webcam active — EXIT  (auto-detecting)", C['green'])

    def stop_camera(self, mode):
        if mode == 'entry':
            self.camera_running_entry = False
            if self.video_capture_entry:
                self.video_capture_entry.release()
                self.video_capture_entry = None
        else:
            self.camera_running_exit = False
            if self.video_capture_exit:
                self.video_capture_exit.release()
                self.video_capture_exit = None

    def update_video(self, mode):
        running = (self.camera_running_entry if mode == 'entry'
                   else self.camera_running_exit)
        cap     = (self.video_capture_entry  if mode == 'entry'
                   else self.video_capture_exit)

        if not running or cap is None:
            return

        ret, frame = cap.read()
        if not ret:
            # Video file ended — stop; webcam glitch — retry once
            if cap.get(cv2.CAP_PROP_POS_FRAMES) > 0:
                self.stop_camera(mode)
                self._set_status(f"Video finished ({mode.upper()})", C['txt1'])
            return

        # Store latest frame and display it
        if mode == 'entry':
            self.current_frame_entry = frame
        else:
            self.current_frame_exit = frame
        self.display_frame(frame, mode)

        # ── Auto-detect every N frames in a background thread ────────────────
        # Guard: skip if a detection thread is already running for this mode
        self._frame_count[mode] += 1
        if (self._frame_count[mode] % self._detect_every == 0
                and not self._detecting[mode]
                and self.models_loaded):
            self._auto_detect_from_frame(frame.copy(), mode, source="video")

        # Schedule next frame read (~30 fps)
        self.root.after(33, lambda: self.update_video(mode))

    def display_frame(self, frame, mode):
        if frame is not None:
            frame = cv2.resize(frame, (640, 480))
            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            img   = Image.fromarray(frame)
            imgtk = ImageTk.PhotoImage(image=img)
            lbl   = (self.video_label_entry if mode == 'entry'
                     else self.video_label_exit)
            lbl.imgtk = imgtk
            lbl.configure(image=imgtk)

    def _auto_detect_from_frame(self, frame, mode, source="video"):
        """
        Run plate detection in a background thread.

        source="image"  → immediate single detection (manual button or image load)
                          → just populates the field, no auto-register
        source="video"  → multi-vote: plate must appear VOTE_THRESHOLD times
                          within VOTE_WINDOW seconds → then auto-register/exit
        """
        self._detecting[mode] = True

        def _run():
            try:
                plate = self.detect_number_plate(frame)
                is_good = plate and not plate.startswith('⚠')

                def _update_ui():
                    info_lbl    = (self.detection_info_entry if mode == 'entry'
                                   else self.detection_info_exit)
                    plate_entry = (self.number_plate_entry if mode == 'entry'
                                   else self.number_plate_exit)
                    vote_lbl    = self._vote_label[mode]

                    if is_good:
                        new_clean = plate.replace(' ', '')

                        # Always show the detected plate in the field
                        current   = plate_entry.get().strip()
                        curr_clean = current.replace(' ', '')
                        if source == 'image' or not current or \
                                len(new_clean) >= len(curr_clean):
                            plate_entry.delete(0, tk.END)
                            plate_entry.insert(0, plate)
                            if mode == 'entry':
                                vt   = self.vehicle_type_entry.get()
                                rate = (self.settings['2w_rate'] if vt == '2W'
                                        else self.settings['4w_rate'])
                                self.entry_time_label.config(
                                    text=datetime.now().strftime('%H:%M:%S'))
                                self.entry_rate_label.config(
                                    text=f"Rs. {rate} / hour")

                        icon = "📷" if source == "image" else "🎥"
                        info_lbl.config(
                            text=f"{icon} Detected: {plate}", fg=C['green'])
                        self._set_status(
                            f"{icon} Plate detected: {plate}  ({mode.upper()})",
                            C['green'])

                        # ── IMAGE source: just populate, no auto-action ───────
                        if source == 'image':
                            if vote_lbl:
                                vote_lbl.config(text="", fg=C['yellow'])
                            return

                        # ── VIDEO source: multi-vote accumulation ─────────────
                        now_ts = time.time()
                        log    = self._vote_log[mode]

                        # Drop votes outside the time window
                        log[:] = [(ts, p) for ts, p in log
                                  if (now_ts - ts) <= self._VOTE_WINDOW]

                        # If a different plate is now winning, reset the log
                        if log and log[-1][1] != new_clean:
                            log.clear()
                            if vote_lbl:
                                vote_lbl.config(text="", fg=C['yellow'])

                        log.append((now_ts, new_clean))
                        vote_count = sum(1 for _, p in log if p == new_clean)

                        # Live dots progress  ●●○  2/3
                        dots    = "●" * vote_count + "○" * max(0, self._VOTE_THRESHOLD - vote_count)
                        v_color = C['green'] if vote_count >= self._VOTE_THRESHOLD else C['yellow']
                        if vote_lbl:
                            vote_lbl.config(
                                text=f"🗳  {dots}  {vote_count}/{self._VOTE_THRESHOLD} votes — {plate}",
                                fg=v_color)

                        if vote_count >= self._VOTE_THRESHOLD:
                            # ── Confirmed — fire auto-action ──────────────────
                            log.clear()
                            if vote_lbl:
                                vote_lbl.config(
                                    text=f"✅ {self._VOTE_THRESHOLD}/{self._VOTE_THRESHOLD} confirmed!",
                                    fg=C['green'])

                            # Cooldown: skip if same plate just acted recently
                            cooldown_key = f"{mode}:{new_clean}"
                            last_ts = self._last_registered.get(cooldown_key, 0.0)
                            if (now_ts - last_ts) < self._register_cooldown:
                                return
                            self._last_registered[cooldown_key] = now_ts

                            if mode == 'entry':
                                self._auto_register_entry(plate)
                            else:
                                self._auto_process_exit(plate)

                    else:
                        if source == 'image':
                            info_lbl = (self.detection_info_entry if mode == 'entry'
                                        else self.detection_info_exit)
                            info_lbl.config(
                                text="⚠  No plate found in image", fg=C['yellow'])
                            self._set_status(
                                "No plate detected — try adjust angle/lighting",
                                C['yellow'])

                self.root.after(0, _update_ui)

            except Exception as exc:
                print(f"[detect-{mode}] {exc}")
            finally:
                self._detecting[mode] = False

        Thread(target=_run, daemon=True).start()

    # ── Auto-action helpers ───────────────────────────────────────────────────

    def _auto_register_entry(self, plate: str):
        """Auto-register a vehicle at entry after vote threshold is reached."""
        vtype   = self.vehicle_type_entry.get()
        cap_key = '2w_capacity' if vtype == '2W' else '4w_capacity'
        occ_key = '2w_occupied' if vtype == '2W' else '4w_occupied'

        if self.settings[occ_key] >= self.settings[cap_key]:
            self._set_status(f"🚫 Parking FULL ({vtype}) — {plate} not registered",
                             C['red'])
            return

        if plate in self.registered_vehicles:
            # Already parked — silently skip
            if self._vote_label['entry']:
                self._vote_label['entry'].config(
                    text=f"ℹ  {plate} already parked", fg=C['txt2'])
            return

        rate       = self.settings['2w_rate' if vtype == '2W' else '4w_rate']
        entry_time = datetime.now()
        self.settings[occ_key] += 1
        self.registered_vehicles[plate] = {
            'type':          vtype,
            'display_plate': plate,
            'entry_time':    entry_time.isoformat(),
            'rate':          rate,
            'comment':       'Auto-registered via camera',
        }
        self.save_vehicles()
        self.save_settings()
        self.update_dashboard()
        self._set_status(f"✅ Auto-registered: {plate}  ({vtype})", C['green'])
        self.detection_info_entry.config(
            text=f"✅ Auto-registered at {entry_time.strftime('%H:%M:%S')}",
            fg=C['green'])
        if self._vote_label['entry']:
            self._vote_label['entry'].config(
                text=f"✅ Registered — {plate}  ({vtype})", fg=C['green'])

    def _auto_process_exit(self, plate: str):
        """
        Auto-exit after vote threshold reached.
        Shows bill + QR dialog FIRST; vehicle is removed ONLY after
        the operator closes/confirms the payment window.
        """
        if plate not in self.registered_vehicles:
            self._set_status(
                f"⚠  {plate} not found — may not be registered", C['yellow'])
            if self._vote_label['exit']:
                self._vote_label['exit'].config(
                    text=f"⚠  {plate} not in system", fg=C['yellow'])
            return

        # Guard: if a payment dialog is already open for this plate, skip
        if plate in self._pending_exit:
            return

        data     = self.registered_vehicles[plate]
        entry_t  = datetime.fromisoformat(data['entry_time'])
        exit_t   = datetime.now()
        duration = (exit_t - entry_t).total_seconds() / 3600
        rate     = data['rate']
        raw_bill = duration * rate
        final    = self.round_bill(raw_bill)
        display  = data.get('display_plate', plate)

        # Mark as pending so we don't open a second dialog
        self._pending_exit[plate] = True

        # Populate the bill preview panel
        self._populate_bill(display, data, entry_t, exit_t,
                            duration, rate, raw_bill, final)
        self.detection_info_exit.config(
            text=f"🚪 Exit: {display}  —  Rs. {final}", fg=C['orange'])
        self._set_status(f"🚪 Exit detected: {display}  —  Rs. {final}", C['green'])
        if self._vote_label['exit']:
            self._vote_label['exit'].config(
                text=f"✅ Confirmed — processing exit…", fg=C['green'])

        def _on_payment_closed():
            """Remove vehicle from system after payment window is dismissed."""
            self._pending_exit.pop(plate, None)
            if plate in self.registered_vehicles:
                occ_key = '2w_occupied' if data['type'] == '2W' else '4w_occupied'
                self.settings[occ_key] = max(0, self.settings[occ_key] - 1)
                del self.registered_vehicles[plate]
                self.save_vehicles()
                self.save_settings()
                self.update_dashboard()
                self._set_status(
                    f"✅ Exit complete: {display}  —  Rs. {final}", C['green'])
                if self._vote_label['exit']:
                    self._vote_label['exit'].config(
                        text=f"✅ Exit done — {display}", fg=C['green'])

        self._show_payment_dialog(display, final, on_close=_on_payment_closed)

    # ─────────────────────────────────────────────────────────────────────────
    # Detection
    # ─────────────────────────────────────────────────────────────────────────

    def detect_vehicle(self, mode):
        """Manual detect button — runs on current frame (image / paused video / webcam)."""
        frame = (self.current_frame_entry if mode == 'entry'
                 else self.current_frame_exit)
        if frame is None:
            messagebox.showwarning(
                "No Feed",
                "Load an image, start a video, or turn on the webcam first.\n\n"
                "• 📁 Image  — load a single photo\n"
                "• 🎥 Video  — load a video file (auto-detects while playing)\n"
                "• 📷 Camera — live webcam (auto-detects continuously)")
            return

        info_lbl = (self.detection_info_entry if mode == 'entry'
                    else self.detection_info_exit)

        # Show spinner and block re-entry while running
        if self._detecting[mode]:
            info_lbl.config(text="⏳  Detection already running…", fg=C['yellow'])
            return

        info_lbl.config(text="⏳  Detecting…", fg=C['yellow'])
        self.root.update_idletasks()
        # source="image" forces the field to always be overwritten
        self._auto_detect_from_frame(frame.copy(), mode, source="image")

    # ── Detection helpers ─────────────────────────────────────────────────────

    def _upscale_if_needed(self, img, min_w=200, min_h=60):
        """Upscale small crops so characters are large enough to detect."""
        h, w = img.shape[:2]
        scale = max(min_w / max(w, 1), min_h / max(h, 1), 1.0)
        if scale > 1.0:
            img = cv2.resize(img, None, fx=scale, fy=scale,
                             interpolation=cv2.INTER_CUBIC)
        return img

    def _deskew_plate(self, gray):
        """
        Correct slight rotation/tilt using Hough line angle estimation.
        Only applies corrections in the range [-15°, +15°] to avoid
        over-rotating non-tilted plates.
        """
        edges = cv2.Canny(gray, 50, 150, apertureSize=3)
        lines = cv2.HoughLinesP(edges, 1, np.pi/180, 60,
                                 minLineLength=gray.shape[1]//4,
                                 maxLineGap=10)
        if lines is None:
            return gray
        angles = []
        for line in lines:
            x1, y1, x2, y2 = line[0]
            if x2 != x1:
                angles.append(np.degrees(np.arctan2(y2-y1, x2-x1)))
        if not angles:
            return gray
        median_angle = float(np.median(angles))
        if abs(median_angle) > 15:
            return gray      # skip extreme rotations
        h, w = gray.shape[:2]
        M = cv2.getRotationMatrix2D((w/2, h/2), median_angle, 1.0)
        return cv2.warpAffine(gray, M, (w, h),
                              flags=cv2.INTER_CUBIC,
                              borderMode=cv2.BORDER_REPLICATE)

    def _enhance_contrast(self, gray):
        """CLAHE local contrast enhancement — handles dark/washed-out plates."""
        clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(4, 4))
        return clahe.apply(gray)

    def crop_plate_region(self, frame):
        """
        Run Model 1 at two resolutions; return the crop with highest confidence.
        Trying at the original size AND a resized version improves recall on
        small/distant plates that the model may miss at full resolution.
        """
        h, w = frame.shape[:2]
        best_crop, best_conf = None, 0.0

        for scale in [1.0, 1.5, 0.75]:
            if scale != 1.0:
                fw = int(w * scale); fh = int(h * scale)
                probe = cv2.resize(frame, (fw, fh), interpolation=cv2.INTER_LINEAR)
            else:
                probe = frame
                fw, fh = w, h

            res = self.plate_detection_model(probe, verbose=False)
            if not res or len(res[0].boxes) == 0:
                continue

            for box in res[0].boxes:
                conf = float(box.conf[0])
                if conf <= best_conf:
                    continue
                # Map coordinates back to original frame
                x1, y1, x2, y2 = map(int, box.xyxy[0])
                x1 = int(x1 / scale); y1 = int(y1 / scale)
                x2 = int(x2 / scale); y2 = int(y2 / scale)
                pad = 12
                x1 = max(0, x1 - pad); y1 = max(0, y1 - pad)
                x2 = min(w, x2 + pad); y2 = min(h, y2 + pad)
                crop = frame[y1:y2, x1:x2]
                if crop.size > 0:
                    best_crop, best_conf = crop, conf

        return best_crop, best_conf

    def preprocess_plate(self, plate_bgr):
        """
        Multi-stage pre-processing pipeline optimised for Nepali plates:

        1. Upscale to ensure minimum resolution (200×60 px)
        2. Convert to grayscale
        3. Deskew (correct tilt up to ±15°)
        4. CLAHE contrast enhancement (handles red/dark plates)
        5. 2× upscale with cubic interpolation
        6. Bilateral filter — noise reduction while keeping edges sharp
        7. Sharpen with an unsharp-mask kernel
        8. Convert back to 3-channel BGR for YOLO Model 2

        Also returns a binarised (Otsu) variant so both can be tried.
        """
        # Step 1: ensure minimum size
        plate_bgr = self._upscale_if_needed(plate_bgr, min_w=200, min_h=60)

        # Step 2: grayscale
        gray = cv2.cvtColor(plate_bgr, cv2.COLOR_BGR2GRAY)

        # Step 3: deskew
        gray = self._deskew_plate(gray)

        # Step 4: CLAHE contrast boost
        gray = self._enhance_contrast(gray)

        # Step 5: 2× upscale
        gray = cv2.resize(gray, None, fx=2, fy=2,
                          interpolation=cv2.INTER_CUBIC)

        # Step 6: bilateral filter
        gray = cv2.bilateralFilter(gray, 9, 75, 75)

        # Step 7: unsharp mask (sharpen edges)
        blurred = cv2.GaussianBlur(gray, (0, 0), 3)
        gray    = cv2.addWeighted(gray, 1.8, blurred, -0.8, 0)
        gray    = np.clip(gray, 0, 255).astype(np.uint8)

        # Step 8: back to 3-channel
        return cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)

    def _preprocess_binarised(self, plate_bgr):
        """Alternative preprocessing using Otsu binarisation — better for faded plates."""
        plate_bgr = self._upscale_if_needed(plate_bgr, min_w=200, min_h=60)
        gray      = cv2.cvtColor(plate_bgr, cv2.COLOR_BGR2GRAY)
        gray      = self._deskew_plate(gray)
        gray      = self._enhance_contrast(gray)
        gray      = cv2.resize(gray, None, fx=2, fy=2,
                               interpolation=cv2.INTER_CUBIC)
        gray      = cv2.bilateralFilter(gray, 9, 75, 75)
        _, binary = cv2.threshold(gray, 0, 255,
                                  cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        return cv2.cvtColor(binary, cv2.COLOR_GRAY2BGR)

    def _preprocess_red_plate(self, plate_bgr):
        """
        Specialised preprocessing for RED-background Nepali plates.
        Nepali plates use a red background with white characters.

        Strategy: invert the red channel dominance so white text becomes
        dark on light background — the format Model 2 was trained on.

        Pipeline:
          1. Upscale to minimum resolution
          2. Convert BGR → HSV, extract saturation + value channels
          3. Use red-channel suppression: subtract red from gray to
             enhance white-text contrast on red backgrounds
          4. CLAHE → 2× upscale → bilateral → sharpen
          5. Return 3-channel BGR
        """
        plate_bgr = self._upscale_if_needed(plate_bgr, min_w=240, min_h=70)

        # Split channels
        b, g, r = cv2.split(plate_bgr)

        # White text on red: white has high R+G+B, red bg has high R only
        # Suppress red background: gray = (G*1.4 + B*1.4 - R*0.8) clamped
        gray = np.clip(g.astype(np.int32)*140//100
                       + b.astype(np.int32)*140//100
                       - r.astype(np.int32)*80//100,
                       0, 255).astype(np.uint8)

        gray = self._deskew_plate(gray)
        gray = self._enhance_contrast(gray)
        gray = cv2.resize(gray, None, fx=2, fy=2,
                          interpolation=cv2.INTER_CUBIC)
        gray = cv2.bilateralFilter(gray, 9, 75, 75)
        blurred = cv2.GaussianBlur(gray, (0, 0), 3)
        gray    = cv2.addWeighted(gray, 1.9, blurred, -0.9, 0)
        gray    = np.clip(gray, 0, 255).astype(np.uint8)
        return cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)

    def _detect_plate_color(self, plate_bgr):
        """
        Detect if a plate has a red background (Nepali standard) or other.
        Returns 'red', 'white', or 'unknown'.
        """
        hsv   = cv2.cvtColor(plate_bgr, cv2.COLOR_BGR2HSV)
        # Red hue wraps around 0/180 in HSV
        mask1 = cv2.inRange(hsv, np.array([0,  100, 80]),
                                  np.array([10, 255, 255]))
        mask2 = cv2.inRange(hsv, np.array([160, 100, 80]),
                                  np.array([180, 255, 255]))
        red_pixels   = cv2.countNonZero(mask1 | mask2)
        total_pixels = plate_bgr.shape[0] * plate_bgr.shape[1]
        if red_pixels / max(total_pixels, 1) > 0.15:
            return 'red'
        white_mask   = cv2.inRange(hsv, np.array([0, 0, 180]),
                                       np.array([180, 60, 255]))
        white_pixels = cv2.countNonZero(white_mask)
        if white_pixels / max(total_pixels, 1) > 0.30:
            return 'white'
        return 'unknown'

    def extract_plate_text(self, preprocessed_img):
        """
        Run Model 2 and reconstruct the plate string using vertical-overlap
        row grouping (size-agnostic — handles mixed small/large character rows).
        """
        res = self.text_extraction_model(preprocessed_img, verbose=False)
        if not res or len(res[0].boxes) == 0:
            return ""
        r = res[0]
        chars = []
        for box in r.boxes:
            x1, y1, x2, y2 = box.xyxy[0].tolist()
            chars.append({
                "x": (x1+x2)/2, "y": (y1+y2)/2,
                "y1": y1, "y2": y2, "h": y2-y1,
                "label": r.names[int(box.cls[0])],
                "conf":  float(box.conf[0]),
            })
        if not chars:
            return ""

        # Filter very low confidence detections (< 18 %)
        # Lower than before to catch faint characters on red plates
        chars = [c for c in chars if c["conf"] >= 0.18]
        if not chars:
            return ""

        # ── Non-maximum suppression: remove duplicate detections ──────────────
        # If two boxes overlap heavily (IoU > 60 %) keep the higher-confidence one
        def _iou(a, b):
            ix1 = max(a['x'] - a['h']*0.5, b['x'] - b['h']*0.5)
            ix2 = min(a['x'] + a['h']*0.5, b['x'] + b['h']*0.5)
            iy1 = max(a['y1'], b['y1'])
            iy2 = min(a['y2'], b['y2'])
            inter = max(0, ix2-ix1) * max(0, iy2-iy1)
            area_a = a['h'] * a['h']
            area_b = b['h'] * b['h']
            union  = area_a + area_b - inter
            return inter / union if union > 0 else 0.0

        chars.sort(key=lambda c: c['conf'], reverse=True)
        kept = []
        for c in chars:
            if all(_iou(c, k) < 0.6 for k in kept):
                kept.append(c)
        chars = kept

        chars.sort(key=lambda c: c["y"])

        def overlap(c, row):
            ry1 = min(rc["y1"] for rc in row)
            ry2 = max(rc["y2"] for rc in row)
            ov  = max(0.0, min(c["y2"], ry2) - max(c["y1"], ry1))
            sh  = min(c["h"], ry2 - ry1)
            return ov / sh if sh > 0 else 0.0

        rows = []
        for ch in chars:
            best_r, best_v = None, 0.0
            for row in rows:
                v = overlap(ch, row)
                if v > best_v:
                    best_v, best_r = v, row
            if best_r and best_v >= 0.35:   # slightly looser threshold
                best_r.append(ch)
            else:
                rows.append([ch])

        rows.sort(key=lambda row: np.mean([c["y"] for c in row]))
        text = ""
        for row in rows:
            row.sort(key=lambda c: c["x"])
            text += "".join(c["label"] for c in row)
        return text

    def detect_number_plate(self, frame):
        """
        5-Strategy detection pipeline — tries every preprocessing approach
        and picks the best result by scoring how complete the plate is.

        Strategy A  standard enhanced preprocessing
        Strategy B  Otsu binarisation (faded / low-contrast plates)
        Strategy C  Red-channel suppression (red-background Nepali plates)
        Strategy D  Inverted binary (dark text on light plates)
        Strategy E  Full-frame fallback (when Model 1 finds no plate region)

        Scoring: more distinct plate tokens (district / series / zone / number)
        wins; ties broken by total character count then detection confidence.
        """
        try:
            if not self.models_loaded:
                return "⚠  Models not loaded"

            candidates = []

            # ── Strategies A–D: run on Model-1 crop ───────────────────────────
            crop, conf = self.crop_plate_region(frame)
            if crop is not None:
                plate_color = self._detect_plate_color(crop)

                # Build ordered list of preprocessors; put red-plate first
                # when a red plate is detected so its result is preferred
                preprocessors = [
                    (self.preprocess_plate,       "enhanced",  1.0),
                    (self._preprocess_binarised,  "binary",    1.0),
                    (self._preprocess_red_plate,  "red_ch",
                     1.2 if plate_color == 'red' else 0.8),
                ]

                # Strategy D: invert binary (works when bg is light not dark)
                def _invert_binary(p):
                    img = self._preprocess_binarised(p)
                    return cv2.bitwise_not(img)

                preprocessors.append((_invert_binary, "inv_binary", 0.9))

                for fn, label, weight in preprocessors:
                    try:
                        pre  = fn(crop)
                        text = self.extract_plate_text(pre)
                        if text:
                            candidates.append((text, conf * weight, label))
                    except Exception:
                        pass

            # ── Strategy E: full-frame OCR fallback ───────────────────────────
            fh, fw = frame.shape[:2]
            scale  = min(1.0, 1280.0 / max(fw, 1))
            probe  = (cv2.resize(frame,
                                  (int(fw*scale), int(fh*scale)),
                                  interpolation=cv2.INTER_LINEAR)
                      if scale < 1.0 else frame)
            for fn, label, w in [
                (self.preprocess_plate,      "full_std",   0.5),
                (self._preprocess_red_plate, "full_red",   0.5),
            ]:
                try:
                    text = self.extract_plate_text(fn(probe))
                    if text:
                        candidates.append((text, 0.3 * w, label))
                except Exception:
                    pass

            if not candidates:
                return "⚠  No plate detected"

            # ── Score & pick best candidate ────────────────────────────────────
            def _plate_score(text):
                """
                Score = number of valid Nepali plate tokens found.
                Tokens: 2-letter district, digit series, alpha zone, digit number.
                Higher is better; 4 = perfect full plate.
                """
                tokens = re.findall(r'[A-Z]+|\d+', text.upper())
                score  = 0
                for i, t in enumerate(tokens[:4]):
                    if i == 0 and t.isalpha() and len(t) == 2:   score += 2
                    elif i == 1 and t.isdigit():                  score += 2
                    elif i == 2 and t.isalpha():                  score += 2
                    elif i == 3 and t.isdigit() and len(t) >= 2:  score += 3
                    else:                                          score += 1
                return score

            candidates.sort(
                key=lambda c: (_plate_score(c[0]), len(c[0]), c[1]),
                reverse=True
            )
            best_text = candidates[0][0]
            return self.format_nepali_plate(best_text) if best_text else "⚠  No text found"

        except Exception as e:
            return f"⚠  {e}"

    def format_nepali_plate(self, text):
        # ── Nepali Unicode digit → ASCII digit ────────────────────────────────
        # Model 2 may output Devanagari/Nepali numerals if trained that way
        NEPALI_DIGITS = str.maketrans('०१२३४५६७८९', '0123456789')

        # ── OCR confusion corrections (common YOLO misreads) ─────────────────
        # Applied after upper-casing; key = wrong, value = correct
        OCR_FIXES = {
            'O': '0',   # letter-O misread as digit zero (in digit context)
            'I': '1',   # letter-I misread as digit one
            'S': '5',   # S → 5 (in digit-only runs)
            'Z': '2',   # Z → 2
            'Q': '0',   # Q → 0
            'B': '8',   # B → 8 (in digit context)
        }

        SINGLE_TO_ZONE = {
            "K": "KA",   "KH": "KHA",
            "G": "GA",   "GH": "GHA",
            "C": "CHA",  "CH": "CHA",
            "J": "JA",   "JH": "JHA",
            "T": "TA",   "TH": "THA",
            "D": "DA",   "DH": "DHA",
            "N": "NA",
            "P": "PA",   "PH": "PHA",
            "BH": "BHA",
            "M": "MA",   "Y": "YA",
            "R": "RA",   "L": "LA",
            "W": "WA",   "V": "WA",
            "S": "SA",   "SH": "SHA",
            "H": "HA",
            "KA": "KA",  "KHA": "KHA", "GA": "GA",  "GHA": "GHA",
            "CHA": "CHA","JA": "JA",   "JHA": "JHA","TA": "TA",
            "THA": "THA","DA": "DA",   "DHA": "DHA","NA": "NA",
            "PA": "PA",  "PHA": "PHA", "BHA": "BHA","MA": "MA",
            "YA": "YA",  "RA": "RA",   "LA": "LA",  "WA": "WA",
            "SA": "SA",  "SHA": "SHA", "HA": "HA",
        }
        # Step 1: Normalise Nepali/Devanagari digits to ASCII
        text  = text.translate(NEPALI_DIGITS)
        clean = text.replace(" ", "").upper()

        # Step 2: tokenise into pure-alpha and pure-digit runs
        tokens = re.findall(r'[A-Z]+|\d+', clean)
        if not tokens:
            return clean

        # Step 3: apply OCR confusion fixes with digit-context awareness
        # Substitute letter→digit only when the character is adjacent to a digit
        # This correctly handles "0I37" → "0137" but leaves zone "SHA" untouched
        def _apply_ocr_fixes(s):
            r = list(s)
            for i, ch in enumerate(r):
                if ch in OCR_FIXES:
                    left_d  = (i > 0 and r[i-1].isdigit())
                    right_d = (i < len(r)-1 and r[i+1].isdigit())
                    if left_d or right_d:
                        r[i] = OCR_FIXES[ch]
            return ''.join(r)

        clean  = _apply_ocr_fixes(clean)
        tokens = re.findall(r'[A-Z]+|\d+', clean)   # re-tokenise after fixes

        # Step 4: assign structural roles left→right
        district = series = zone = None
        pending  = []
        for tok in tokens:
            if district is None:
                district = tok                                  # 2-letter district
            elif series is None and tok.isdigit():
                series = tok                                    # 1–2 digit series
            elif zone is None and tok.isalpha():
                zone = SINGLE_TO_ZONE.get(tok, tok)            # zone label
            elif tok.isdigit():
                pending.append(tok)                             # plate number

        number = "".join(pending) if pending else None
        parts  = [p for p in [district, series, zone, number] if p]

        if len(parts) >= 3:
            return " ".join(parts)

        # Fallback: positional slicing for unstructured reads
        if len(clean) >= 9:
            return f"{clean[:2]} {clean[2:3]} {clean[3:6]} {clean[6:]}"
        if len(clean) >= 7:
            return f"{clean[:2]} {clean[2:3]} {clean[3:5]} {clean[5:]}"
        return clean

    # ─────────────────────────────────────────────────────────────────────────
    # Entry / Exit logic
    # ─────────────────────────────────────────────────────────────────────────

    def register_entry(self):
        vtype = self.vehicle_type_entry.get()
        plate = self.number_plate_entry.get().strip()
        if not plate:
            messagebox.showwarning("Missing", "Detect or enter the number plate first.")
            return
        cap_key = '2w_capacity' if vtype == '2W' else '4w_capacity'
        occ_key = '2w_occupied' if vtype == '2W' else '4w_occupied'
        if self.settings[occ_key] >= self.settings[cap_key]:
            messagebox.showerror("Parking Full", f"{vtype} parking is at capacity!")
            return

        # ── Duplicate plate handling ───────────────────────────────────────────
        # If the same plate is already parked, generate a unique storage key by
        # appending a counter suffix (#2, #3 …) so both records coexist.
        # The displayed plate stored in 'display_plate' remains the real number.
        storage_key = plate
        comment     = ""
        if plate in self.registered_vehicles:
            suffix = 2
            while f"{plate}#{suffix}" in self.registered_vehicles:
                suffix += 1
            storage_key = f"{plate}#{suffix}"
            comment     = (f"⚠ Duplicate entry — same plate already parked. "
                           f"This record stored as '{storage_key}'.")
            messagebox.showwarning(
                "⚠  Duplicate Plate Detected",
                f"Plate '{plate}' is already registered in the system.\n\n"
                f"Both vehicles will be tracked separately.\n"
                f"This entry is stored as:  {storage_key}\n\n"
                f"Use  '{storage_key}'  at exit to select this vehicle.")

        self.settings[occ_key] += 1
        entry_time = datetime.now()
        self.registered_vehicles[storage_key] = {
            'type':          vtype,
            'display_plate': plate,          # real plate number for display
            'entry_time':    entry_time.isoformat(),
            'rate':          self.settings['2w_rate' if vtype == '2W' else '4w_rate'],
            'comment':       comment,
        }
        self.save_vehicles()
        self.save_settings()
        self._set_status(f"Registered: {storage_key}", C['green'])
        self.update_dashboard()
        messagebox.showinfo("✅  Registered",
                            f"Vehicle Registered\n\n"
                            f"  Plate      :  {plate}\n"
                            f"  Record key :  {storage_key}\n"
                            f"  Type       :  {vtype}\n"
                            f"  Time       :  {entry_time.strftime('%H:%M:%S')}")
        self.number_plate_entry.delete(0, tk.END)
        self.detection_info_entry.config(text="")

    def process_exit(self):
        plate = self.number_plate_exit.get().strip()
        if not plate:
            messagebox.showwarning("Missing", "Enter or detect number plate.")
            return
        if plate not in self.registered_vehicles:
            messagebox.showerror("Not Found",
                                 f"'{plate}' is not registered in the system.")
            return

        data      = self.registered_vehicles[plate]
        entry_t   = datetime.fromisoformat(data['entry_time'])
        exit_t    = datetime.now()
        duration  = (exit_t - entry_t).total_seconds() / 3600
        rate      = data['rate']
        raw_bill  = duration * rate
        final     = self.round_bill(raw_bill)
        display   = data.get('display_plate', plate)

        # Populate the bill preview panel in the UI
        self._populate_bill(display, data, entry_t, exit_t,
                            duration, rate, raw_bill, final)
        self._set_status(f"Exit: {display}  —  Rs. {final}", C['green'])

        # Show text receipt first
        comment_line = f"  Note     :  {data['comment']}\n" if data.get('comment') else ""
        msg = (
            f"{'─'*44}\n"
            f"  PARKING RECEIPT\n"
            f"{'─'*44}\n"
            f"  Vehicle  :  {display}\n"
            f"  Record   :  {plate}\n"
            f"  Type     :  {data['type']}\n"
            f"{comment_line}"
            f"  Entry    :  {entry_t.strftime('%d %b %Y  %H:%M:%S')}\n"
            f"  Exit     :  {exit_t.strftime('%d %b %Y  %H:%M:%S')}\n"
            f"  Duration :  {duration:.2f} hours\n"
            f"  Rate     :  Rs. {rate}/hour\n"
            f"  Subtotal :  Rs. {raw_bill:.2f}\n"
            f"{'─'*44}\n"
            f"  TOTAL    :  Rs. {final}\n"
            f"{'─'*44}\n"
            f"  Thank you for parking with us!"
        )
        messagebox.showinfo("Bill Generated", msg)

        # Show QR/payment dialog — vehicle is removed ONLY after this closes
        def _on_payment_closed():
            if plate in self.registered_vehicles:
                occ_key = '2w_occupied' if data['type'] == '2W' else '4w_occupied'
                self.settings[occ_key] = max(0, self.settings[occ_key] - 1)
                del self.registered_vehicles[plate]
                self.save_vehicles()
                self.save_settings()
                self._set_status(
                    f"✅ Exit complete: {display}  —  Rs. {final}", C['green'])
                self.update_dashboard()

        self._show_payment_dialog(display, final, on_close=_on_payment_closed)

    def _show_payment_dialog(self, plate, amount, on_close=None):
        """
        Show QR / digital-payment dialog.
        on_close: optional callable fired when window is dismissed —
                  used to remove the vehicle AFTER the operator sees the bill.
        """
        win = tk.Toplevel(self.root)
        win.title("Payment")
        win.geometry("480x540")
        win.configure(bg=C['bg0'])
        win.resizable(False, False)
        win.grab_set()   # modal

        def _close():
            win.destroy()
            if on_close:
                on_close()

        win.protocol("WM_DELETE_WINDOW", _close)

        # ── Header ────────────────────────────────────────────────────────────
        hdr = tk.Frame(win, bg=C['green_dk'], height=52)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)
        tk.Label(hdr, text="💳  DIGITAL PAYMENT",
                 font=('Consolas', 14, 'bold'),
                 bg=C['green_dk'], fg=C['white']).pack(side='left', padx=18, pady=14)
        tk.Label(hdr, text=f"Rs. {amount}",
                 font=('Consolas', 14, 'bold'),
                 bg=C['green_dk'], fg=C['yellow']).pack(side='right', padx=18)

        body = tk.Frame(win, bg=C['bg0'])
        body.pack(fill='both', expand=True, padx=24, pady=18)

        # Amount chip
        amt_frame = tk.Frame(body, bg=C['bg2'])
        amt_frame.pack(fill='x', pady=(0, 16))
        tk.Label(amt_frame, text="Amount Due",
                 font=FONT_SMALL, bg=C['bg2'], fg=C['txt1']).pack(pady=(8, 0))
        tk.Label(amt_frame, text=f"Rs. {amount}",
                 font=('Consolas', 30, 'bold'),
                 bg=C['bg2'], fg=C['yellow']).pack(pady=(0, 8))

        # QR box — ASCII art placeholder
        qr_outer = tk.Frame(body, bg=C['bg1'], bd=2, relief='solid')
        qr_outer.pack(pady=(0, 16))

        qr_box = tk.Frame(qr_outer, bg='white', width=160, height=160)
        qr_box.pack(padx=12, pady=12)
        qr_box.pack_propagate(False)

        # Draw a simple visual QR placeholder on a canvas
        qr_canvas = tk.Canvas(qr_box, width=156, height=156,
                               bg='white', highlightthickness=0)
        qr_canvas.pack()
        # Corner squares
        for x, y in [(4,4),(116,4),(4,116)]:
            qr_canvas.create_rectangle(x, y, x+36, y+36, fill='black', outline='')
            qr_canvas.create_rectangle(x+6, y+6, x+30, y+30, fill='white', outline='')
            qr_canvas.create_rectangle(x+12, y+12, x+24, y+24, fill='black', outline='')
        # Data dots pattern
        import random; random.seed(amount)
        for _ in range(90):
            px = random.randint(48, 148); py = random.randint(4, 148)
            if not (4<=px<=40 and 4<=py<=40) and not (116<=px<=152 and 4<=py<=40) and not (4<=px<=40 and 116<=py<=152):
                sz = random.choice([4, 6, 8])
                qr_canvas.create_rectangle(px, py, px+sz, py+sz, fill='black', outline='')
        tk.Label(body, text="Scan QR to Pay",
                 font=('Segoe UI', 9, 'italic'),
                 bg=C['bg0'], fg=C['txt2']).pack(pady=(0, 12))

        # Bank details card
        det = tk.Frame(body, bg=C['bg2'])
        det.pack(fill='x', pady=(0, 16))
        tk.Label(det, text="─── Bank Transfer Details ───",
                 font=('Consolas', 9), bg=C['bg2'], fg=C['txt2']).pack(pady=(10, 6))

        for lbl, val, color in [
            ("Account Name",   "Smart Parking",  C['txt0']),
            ("Account Number", "123424211",       C['cyan']),
            ("Vehicle Plate",  plate,             C['cyan']),
            ("Amount",         f"Rs. {amount}",   C['yellow']),
        ]:
            row = tk.Frame(det, bg=C['bg2'])
            row.pack(fill='x', padx=16, pady=3)
            tk.Label(row, text=lbl, font=FONT_SMALL,
                     fg=C['txt1'], bg=C['bg2'],
                     width=18, anchor='w').pack(side='left')
            tk.Label(row, text=val,
                     font=('Consolas', 10, 'bold'),
                     fg=color, bg=C['bg2'], anchor='e').pack(side='right')
        tk.Frame(det, bg=C['border'], height=1).pack(fill='x', padx=16, pady=8)
        tk.Label(det, text="Please include the vehicle plate in remarks.",
                 font=('Segoe UI', 8), bg=C['bg2'],
                 fg=C['txt2']).pack(pady=(0, 10))

        # Buttons
        btn_row = tk.Frame(body, bg=C['bg0'])
        btn_row.pack(fill='x', pady=(4, 0))
        BigButton(btn_row, "✅  Payment Confirmed — Close",
                  command=_close,
                  bg=C['green'], hover=C['green_dk'],
                  height=44, font=FONT_BODY_B).pack(fill='x')

    def round_bill(self, amount):
        last = int(amount) % 10
        if last < 3:   return int(amount) - last
        elif last < 8: return int(amount) - last + 5
        else:          return int(amount) - last + 10

    # ─────────────────────────────────────────────────────────────────────────
    # Dashboard update
    # ─────────────────────────────────────────────────────────────────────────

    def update_dashboard(self):
        # ── Occupancy bars ─────────────────────────────────────────────────────
        for vtype in ['2w', '4w']:
            occ = self.settings[f'{vtype}_occupied']
            cap = self.settings[f'{vtype}_capacity']
            pct = (occ / cap) if cap > 0 else 0
            lbl = getattr(self, f'{vtype}_occupied_label')
            lbl.config(text=f"{occ}  /  {cap}")
            bar_fill = getattr(self, f'{vtype}_bar_fill')
            color = (C['red'] if pct > 0.8
                     else C['yellow'] if pct > 0.5
                     else (C['blue'] if vtype == '2w' else C['purple']))
            bar_fill.configure(bg=color)
            bar_fill.place_configure(relwidth=min(pct, 1.0))

        # ── Live Revenue: sum ALL vehicles (2W + 4W) ───────────────────────────
        # FIX: total_revenue initialised OUTSIDE the vtype loop — previously it
        # was reset to 0.0 inside the loop so only the last vehicle type counted.
        total_revenue = 0.0
        for _plate, data in self.registered_vehicles.items():
            try:
                entry_t = datetime.fromisoformat(data['entry_time'])
                hrs     = (datetime.now() - entry_t).total_seconds() / 3600
                total_revenue += hrs * data['rate']
            except Exception:
                pass

        self.revenue_label.config(text=f"Rs. {total_revenue:.0f}")
        self._update_vehicle_lists()

    def _update_vehicle_lists(self):
        for vtype in ['2W', '4W']:
            frame = getattr(self, f'{vtype.lower()}_list_frame')
            for w in frame.winfo_children():
                w.destroy()

            vehicles = {p: d for p, d in self.registered_vehicles.items()
                        if d['type'] == vtype}

            if not vehicles:
                tk.Label(frame, text="No vehicles parked",
                         font=FONT_SMALL, bg=C['bg1'], fg=C['txt2']).pack(
                             pady=20)
                continue

            for i, (plate, data) in enumerate(vehicles.items()):
                bg  = C['bg1'] if i % 2 == 0 else C['bg0']
                row = tk.Frame(frame, bg=bg, cursor='hand2')
                row.pack(fill='x')

                entry_t = datetime.fromisoformat(data['entry_time'])
                hrs     = (datetime.now() - entry_t).total_seconds() / 3600
                bill    = hrs * data['rate']

                display_p = data.get('display_plate', plate)
                # Show duplicate badge if storage key differs from display plate
                dup_tag = "  ⊕ DUP" if '#' in plate else ""
                tk.Label(row, text=f"{display_p}{dup_tag}",
                         font=('Consolas', 10, 'bold'),
                         fg=C['orange'] if dup_tag else C['cyan'], bg=bg,
                         width=18, anchor='w').pack(side='left', padx=8, pady=7)
                tk.Label(row,
                         text=f"{int(hrs)}h {int((hrs%1)*60)}m",
                         font=FONT_SMALL, fg=C['txt1'], bg=bg,
                         width=14, anchor='w').pack(side='left')
                tk.Label(row, text=f"Rs. {bill:.0f}",
                         font=('Consolas', 10, 'bold'),
                         fg=C['green'], bg=bg,
                         width=12, anchor='e').pack(side='right', padx=10)

    # ─────────────────────────────────────────────────────────────────────────
    # Settings save
    # ─────────────────────────────────────────────────────────────────────────

    def save_settings_ui(self):
        self.settings['2w_capacity'] = self._2w_capacity_var.get()
        self.settings['4w_capacity'] = self._4w_capacity_var.get()
        self.settings['2w_rate']     = self._2w_rate_var.get()
        self.settings['4w_rate']     = self._4w_rate_var.get()
        self.save_settings()
        messagebox.showinfo("Saved", "✅  Configuration saved successfully.")
        self.update_dashboard()

    # ─────────────────────────────────────────────────────────────────────────
    # Timer background thread
    # ─────────────────────────────────────────────────────────────────────────

    def start_timer_updates(self):
        def loop():
            while self.update_timers:
                try:
                    self.root.after(0, self._update_vehicle_lists)
                except Exception:
                    pass
                time.sleep(30)
        Thread(target=loop, daemon=True).start()


# ─────────────────────────────────────────────────────────────────────────────
def main():
    root = tk.Tk()
    app  = ModernParkingSystem(root)
    root.mainloop()


if __name__ == "__main__":
    main()