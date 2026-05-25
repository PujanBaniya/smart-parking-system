import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import cv2
from PIL import Image, ImageTk
import numpy as np
from datetime import datetime
import json, os, re, hashlib, sys, uuid, hmac, base64
from threading import Thread
import time
import webbrowser
import urllib.parse
import urllib.request
import http.server
import socketserver
import subprocess
import platform

# ReportLab Imports (moved to top to avoid runtime ImportErrors)
try:
    from reportlab.lib.pagesizes import A5
    from reportlab.pdfgen import canvas as rl_canvas
    from reportlab.lib import colors
    from reportlab.lib.units import mm
    from reportlab.graphics.barcode.qr import QrCodeWidget
    from reportlab.graphics.shapes import Drawing
    from reportlab.graphics import renderPM
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.lib.utils import ImageReader
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

# ─────────────────────────────────────────────────────────────────────────────
# EXE PATH HELPER
# ─────────────────────────────────────────────────────────────────────────────

def _get_data_dir():
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

# ─────────────────────────────────────────────────────────────────────────────
# eSewa API v2 — HMAC-SHA256 Integration
# ─────────────────────────────────────────────────────────────────────────────

ESEWA_TEST_MERCHANT  = "EPAYTEST"
ESEWA_TEST_SECRET    = "8gBm/:&EnhH.1/q"
ESEWA_TEST_URL       = "https://rc-epay.esewa.com.np/api/epay/main/v2/form"
ESEWA_TEST_VERIFY    = "https://rc.esewa.com.np/api/epay/transaction/status/"
ESEWA_LIVE_URL       = "https://epay.esewa.com.np/api/epay/main/v2/form"
ESEWA_LIVE_VERIFY    = "https://epay.esewa.com.np/api/epay/transaction/status/"

# eSewa personal wallet QR fallback
ESEWA_NAME   = "Pujan Baniya"
ESEWA_NUMBER = "9860574498"

# Static eSewa QR — embedded JPEG (240x240), your real physical QR standee
# Pujan Baniya  |  9860574498
_STATIC_ESEWA_QR_B64 = (
    "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"
    "rlSteTT6vFcJToAHZ181B4HikO66NIeRVH//2Q=="
)

def _get_static_esewa_qr(size: int = 220) -> "Image.Image | None":
    """Return the real physical eSewa QR code as a PIL Image."""
    try:
        import base64 as _b64, io as _io
        data = _b64.b64decode(_STATIC_ESEWA_QR_B64)
        img  = Image.open(_io.BytesIO(data)).convert("RGB")
        return img.resize((size, size), Image.LANCZOS)
    except Exception as e:
        print(f"[static QR] {e}")
        return None


# Local callback server port
CALLBACK_PORT = 8765


def _esewa_generate_signature(message: str, secret: str) -> str:
    """Generate HMAC-SHA256 signature for eSewa v2 API."""
    h = hmac.new(secret.encode('utf-8'), message.encode('utf-8'), 'sha256')
    return base64.b64encode(h.digest()).decode('utf-8')


def _esewa_verify_payment(transaction_uuid: str, total_amount: float,
                           product_code: str, verify_url: str) -> dict:
    """
    Verify eSewa payment status via GET API.
    Returns dict with 'status' key: COMPLETE / PENDING / NOT_FOUND / ERROR
    """
    try:
        params = urllib.parse.urlencode({
            'product_code':     product_code,
            'total_amount':     float(total_amount),
            'transaction_uuid': transaction_uuid,
        })
        url = f"{verify_url}?{params}"
        req = urllib.request.Request(url, headers={'Content-Type': 'application/json'})
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode('utf-8'))
            return data
    except Exception as exc:
        return {'status': 'ERROR', 'error': str(exc)}


def _build_esewa_form_html(amount: float, transaction_uuid: str,
                            product_code: str, secret: str,
                            esewa_url: str,
                            success_url: str, failure_url: str) -> str:
    """Build a self-submitting HTML form for eSewa v2 payment."""
    total_amount = round(amount, 2)
    signed_fields = "total_amount,transaction_uuid,product_code"
    message = f"total_amount={total_amount},transaction_uuid={transaction_uuid},product_code={product_code}"
    signature = _esewa_generate_signature(message, secret)

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>eSewa Payment</title>
<style>
  body {{ font-family: Arial, sans-serif; background: #0b1528; color: #e2e8f0;
         display:flex; justify-content:center; align-items:center; height:100vh; margin:0; }}
  .card {{ background:#112038; border-radius:12px; padding:40px; text-align:center;
           box-shadow:0 4px 32px rgba(0,0,0,.5); max-width:400px; width:100%; }}
  h2 {{ color:#60BB46; margin-bottom:8px; }}
  .amount {{ font-size:2.5rem; font-weight:bold; color:#f59e0b; margin:16px 0; }}
  .info {{ color:#7a95b8; font-size:.9rem; margin-bottom:24px; }}
  .spinner {{ border:4px solid #1d3050; border-top:4px solid #60BB46;
              border-radius:50%; width:40px; height:40px;
              animation:spin 1s linear infinite; margin:0 auto 16px; }}
  @keyframes spin {{ to {{ transform:rotate(360deg); }} }}
</style>
</head>
<body>
<div class="card">
  <div class="spinner"></div>
  <h2>🟢 Redirecting to eSewa…</h2>
  <div class="amount">Rs. {total_amount}</div>
  <div class="info">Vehicle: {transaction_uuid}</div>
  <form id="esewaForm" action="{esewa_url}" method="POST">
    <input type="hidden" name="amount"              value="{total_amount}">
    <input type="hidden" name="tax_amount"          value="0">
    <input type="hidden" name="total_amount"        value="{total_amount}">
    <input type="hidden" name="transaction_uuid"    value="{transaction_uuid}">
    <input type="hidden" name="product_code"        value="{product_code}">
    <input type="hidden" name="product_service_charge"  value="0">
    <input type="hidden" name="product_delivery_charge" value="0">
    <input type="hidden" name="success_url"         value="{success_url}">
    <input type="hidden" name="failure_url"         value="{failure_url}">
    <input type="hidden" name="signed_field_names"  value="{signed_fields}">
    <input type="hidden" name="signature"           value="{signature}">
  </form>
  <script>document.getElementById('esewaForm').submit();</script>
</div>
</body>
</html>"""
    return html


# ─────────────────────────────────────────────────────────────────────────────
# Local callback HTTP server (receives eSewa redirect)
# ─────────────────────────────────────────────────────────────────────────────

class _CallbackHandler(http.server.BaseHTTPRequestHandler):
    """Handles eSewa success/failure redirects."""
    payment_results: dict = {}   # shared class-level dict

    def log_message(self, *_): pass   # silence console spam

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        query  = urllib.parse.parse_qs(parsed.query)
        txn_id = query.get('transaction_uuid', [None])[0]
        status = 'success' if parsed.path == '/esewa/success' else 'failure'
        if txn_id:
            _CallbackHandler.payment_results[txn_id] = {
                'status': status,
                'data':   query,
                'ts':     datetime.now().isoformat(),
            }
        # Send pretty response page
        color  = '#60BB46' if status=='success' else '#ef4444'
        icon   = '✅' if status=='success' else '❌'
        msg    = 'Payment Successful!' if status=='success' else 'Payment Failed / Cancelled'
        body   = f"""<!DOCTYPE html><html><head><meta charset="UTF-8">
<style>body{{font-family:Arial;background:#0b1528;color:#e2e8f0;
display:flex;justify-content:center;align-items:center;height:100vh;margin:0;}}
.card{{background:#112038;border-radius:12px;padding:48px;text-align:center;}}
h1{{color:{color};font-size:2rem;}} p{{color:#7a95b8;}}
</style></head><body>
<div class="card"><h1>{icon} {msg}</h1>
<p>You can close this window and return to the parking system.</p></div>
</body></html>"""
        self.send_response(200)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.end_headers()
        self.wfile.write(body.encode('utf-8'))


def _start_callback_server():
    """Start callback HTTP server on CALLBACK_PORT in a daemon thread."""
    try:
        srv = socketserver.TCPServer(('127.0.0.1', CALLBACK_PORT), _CallbackHandler)
        srv.allow_reuse_address = True
        t = Thread(target=srv.serve_forever, daemon=True)
        t.start()
        return srv
    except Exception as exc:
        print(f"[eSewa callback server] {exc}")
        return None


# ─────────────────────────────────────────────────────────────────────────────
# Nepali script conversion
# ─────────────────────────────────────────────────────────────────────────────

_ZONE_TO_DEVANAGARI = {
    "BA":"बा",
    "BAGMATI":"बागमती",
    "CHA":"च",
    "GA":"ग",
    "GANDAKI":"गण्डकी",
    "HA":"ह",
    "JA":"ज",
    "JHA":"झ",
    "KA":"क",
    "KHA":"ख",
    "KO":"को",
    "LU":"लु",
    "LUMBINI":"लुम्बिनी",
    "MA":"म",
    "MADESH":"मधेश",
    "ME":"मे",
    "NA":"ना",
    "PA":"प",
    "PRA":"प्रा",
    "PRADESH":"प्रदेश",
    "RA":"रा",
    "SU":"सु",
    "VE":"वे",
    "YA":"या",
}

_DEVANAGARI_DIGITS = str.maketrans('0123456789', '०१२३४५६७८९')


def plate_to_nepali_script(plate: str) -> str:
    parts = plate.strip().split()
    out   = []
    for p in parts:
        up = p.upper()
        if up in _ZONE_TO_DEVANAGARI:
            out.append(_ZONE_TO_DEVANAGARI[up])
        elif p.isdigit():
            out.append(p.translate(_DEVANAGARI_DIGITS))
        else:
            converted = ""
            for ch in p:
                if ch.isdigit():
                    converted += ch.translate(_DEVANAGARI_DIGITS)
                else:
                    converted += ch
            out.append(converted)
    return "  ".join(out)


# ─────────────────────────────────────────────────────────────────────────────
# Auto vehicle-type detection
# ─────────────────────────────────────────────────────────────────────────────

def _guess_vehicle_type_from_frame(frame, plate_detection_model) -> str:
    try:
        h, w = frame.shape[:2]
        frame_area = h * w
        res = plate_detection_model(frame, verbose=False)
        if not res or len(res[0].boxes) == 0:
            return '2W'
        best_area = 0
        best_ar   = 1.0
        for box in res[0].boxes:
            x1, y1, x2, y2 = map(int, box.xyxy[0])
            bw = x2 - x1
            bh = y2 - y1
            area = bw * bh
            if area > best_area:
                best_area = area
                best_ar   = bw / max(bh, 1)
        rel_area = best_area / max(frame_area, 1)
        if best_ar > 3.5 or rel_area > 0.012:
            return '4W'
        return '2W'
    except Exception:
        return '2W'


# ─────────────────────────────────────────────────────────────────────────────
# Slot Allocation Engine
# ─────────────────────────────────────────────────────────────────────────────

LONG_STAY_THRESHOLD_HRS = 5.0


class SlotAllocator:
    """
    Manages parking slot allocation.
    Strategy:
      - Predicted short stay (< 5h) → allocate from slot 1 upward (nearest)
      - Predicted long  stay (≥ 5h) → allocate from slot max downward (farthest)
    History file: parking_history.json — used for stay-duration prediction.
    """

    def __init__(self, data_dir: str):
        self.data_dir = data_dir
        self._history_path = os.path.join(data_dir, 'parking_history.json')
        self._alloc_path   = os.path.join(data_dir, 'slot_allocations.json')
        self.history      = self._load_json(self._history_path, {})
        self.allocations  = self._load_json(self._alloc_path,  {})

    # ── persistence ──────────────────────────────────────────────────────────

    def _load_json(self, path, default):
        if os.path.exists(path):
            try:
                with open(path) as f:
                    return json.loads(f.read().strip())
            except Exception:
                pass
        return default

    def _save(self):
        with open(self._alloc_path, 'w') as f:
            json.dump(self.allocations, f, indent=2)

    def save_history(self):
        with open(self._history_path, 'w') as f:
            json.dump(self.history, f, indent=2)

    # ── prediction ───────────────────────────────────────────────────────────

    def predict_stay_hours(self, plate: str) -> float:
        """Return predicted stay duration in hours for this plate."""
        plate_clean = plate.replace(' ', '').upper()
        stays = self.history.get(plate_clean, [])
        if not stays:
            return 2.0   # default: short stay
        # Use weighted average (recent entries have more weight)
        total_weight = 0.0
        total        = 0.0
        for i, entry in enumerate(stays[-10:]):
            w = (i + 1) * 1.0
            total        += entry.get('duration_hrs', 2.0) * w
            total_weight += w
        return total / max(total_weight, 1)

    # ── allocation ───────────────────────────────────────────────────────────

    def allocate(self, plate: str, vtype: str,
                 capacity_2w: int, capacity_4w: int) -> tuple:
        """
        Returns (slot_number: int, is_long_stay: bool, predicted_hrs: float).
        slot_number is 1-indexed.
        """
        capacity  = capacity_2w if vtype == '2W' else capacity_4w
        prefix    = 'S' if vtype == '2W' else 'C'  # S=scooter, C=car
        used_slots = {
            v['slot'] for v in self.allocations.values()
            if v.get('vtype') == vtype
        }
        predicted = self.predict_stay_hours(plate)
        is_long   = predicted >= LONG_STAY_THRESHOLD_HRS

        if is_long:
            # Allocate from back
            for slot in range(capacity, 0, -1):
                if slot not in used_slots:
                    return slot, True, predicted
        else:
            # Allocate from front
            for slot in range(1, capacity + 1):
                if slot not in used_slots:
                    return slot, False, predicted

        # Parking full — return next theoretical slot
        return capacity + 1, is_long, predicted

    def register(self, plate: str, vtype: str, slot: int):
        """Record that this plate is in this slot."""
        self.allocations[plate] = {
            'slot':       slot,
            'vtype':      vtype,
            'allocated':  datetime.now().isoformat(),
        }
        self._save()

    def release(self, plate: str, duration_hrs: float):
        """Release slot and record stay in history."""
        plate_clean = plate.replace(' ', '').upper()
        if plate in self.allocations:
            del self.allocations[plate]
            self._save()
        if plate_clean not in self.history:
            self.history[plate_clean] = []
        self.history[plate_clean].append({
            'date':         datetime.now().strftime('%Y-%m-%d'),
            'duration_hrs': round(duration_hrs, 3),
        })
        # Keep last 30 entries per plate
        self.history[plate_clean] = self.history[plate_clean][-30:]
        self.save_history()

    def get_slot(self, plate: str) -> int:
        """Return assigned slot for plate, or 0 if not found."""
        return self.allocations.get(plate, {}).get('slot', 0)

    def get_all_plates_for_vtype(self, vtype: str) -> dict:
        """Return {plate: slot} for vtype."""
        return {
            p: v['slot'] for p, v in self.allocations.items()
            if v.get('vtype') == vtype
        }


# ─────────────────────────────────────────────────────────────────────────────
# Dynamic eSewa QR Generator (personal wallet fallback)
# ─────────────────────────────────────────────────────────────────────────────

def _generate_esewa_qr_image(size: int = 240) -> "Image.Image | None":
    if not REPORTLAB_AVAILABLE:
        print("[eSewa QR] reportlab not installed")
        return None
    try:
        from io import BytesIO
        widget  = QrCodeWidget(ESEWA_NUMBER)
        bounds  = widget.getBounds()
        w, h    = bounds[2]-bounds[0], bounds[3]-bounds[1]
        drawing = Drawing(w, h)
        drawing.add(widget)
        buf = BytesIO()
        renderPM.drawToFile(drawing, buf, fmt="PNG")
        buf.seek(0)
        qr_img = Image.open(buf).convert("RGB")
        return qr_img.resize((size, size), Image.NEAREST)
    except Exception as _exc:
        print(f"[eSewa QR] {_exc}")
        return None


# ─────────────────────────────────────────────────────────────────────────────
# PDF Receipt Generator
# ─────────────────────────────────────────────────────────────────────────────

def generate_pdf_receipt(data: dict) -> str:
    if not REPORTLAB_AVAILABLE:
        raise ImportError("The 'reportlab' module is required to generate PDF receipts. Please install it with 'pip install reportlab'.")
    
    from io import BytesIO

    receipts_dir = os.path.join(_get_data_dir(), "receipts")
    os.makedirs(receipts_dir, exist_ok=True)

    safe_name = re.sub(r"[^A-Za-z0-9_]", "_", data.get('display_plate', 'receipt'))
    ts        = datetime.now().strftime("%Y%m%d_%H%M%S")
    pdf_path  = os.path.join(receipts_dir, f"receipt_{safe_name}_{ts}.pdf")

    W, H = A5
    c = rl_canvas.Canvas(pdf_path, pagesize=A5)

    ESEWA_GREEN = colors.HexColor('#60BB46')
    DARK        = colors.HexColor('#0b1528')
    ACCENT      = colors.HexColor('#06b6d4')
    YELLOW      = colors.HexColor('#f59e0b')
    LIGHT_BG    = colors.HexColor('#f0f4f8')
    MID_GRAY    = colors.HexColor('#7a95b8')

    # Header bar
    c.setFillColor(DARK)
    c.rect(0, H-38*mm, W, 38*mm, fill=1, stroke=0)
    c.setFillColor(ESEWA_GREEN)
    c.rect(0, H-40*mm, W, 4*mm, fill=1, stroke=0)
    c.setFillColor(colors.white)
    c.setFont("Helvetica-Bold", 16)
    c.drawCentredString(W/2, H-16*mm, "SMART PARKING  v5")
    c.setFont("Helvetica", 8)
    c.setFillColor(MID_GRAY)
    c.drawCentredString(W/2, H-22*mm, "Management System — Professional Edition")
    c.setFont("Helvetica-Bold", 9)
    c.setFillColor(ESEWA_GREEN)
    c.drawCentredString(W/2, H-29*mm, "PARKING RECEIPT")

    y = H-46*mm
    c.setFont("Helvetica", 7); c.setFillColor(MID_GRAY)
    ts_display = datetime.now().strftime("%d %b %Y  %H:%M:%S")
    receipt_no = f"RCP-{datetime.now().strftime('%Y%m%d%H%M%S')}"
    c.drawString(8*mm, y, f"Receipt No: {receipt_no}")
    c.drawRightString(W-8*mm, y, f"Printed: {ts_display}")
    c.setStrokeColor(ACCENT); c.setLineWidth(0.5)
    c.line(8*mm, y-2*mm, W-8*mm, y-2*mm)

    y -= 8*mm
    c.setFillColor(LIGHT_BG)
    c.roundRect(8*mm, y-14*mm, W-16*mm, 18*mm, 3*mm, fill=1, stroke=0)
    c.setFont("Helvetica-Bold", 18); c.setFillColor(DARK)
    plate_display = data.get('display_plate', data.get('plate', ''))
    c.drawCentredString(W/2, y-4*mm, plate_display)

    nepali = data.get('nepali_plate', '')
    if nepali and nepali != '—':
        try:
            font_paths = [
                "C:/Windows/Fonts/NirmalaUI.ttf",
                "C:/Windows/Fonts/mangal.ttf",
                "/usr/share/fonts/truetype/noto/NotoSansDevanagari-Regular.ttf",
            ]
            registered = False
            for fp in font_paths:
                if os.path.exists(fp):
                    try:
                        pdfmetrics.registerFont(TTFont('Devanagari', fp))
                        c.setFont("Devanagari", 12); registered = True; break
                    except Exception: pass
            if not registered: c.setFont("Helvetica", 9)
            c.setFillColor(MID_GRAY)
            c.drawCentredString(W/2, y-11*mm, nepali)
        except Exception: pass

    # Slot badge
    slot = data.get('slot', 0)
    if slot:
        c.setFillColor(colors.HexColor('#1d4ed8'))
        c.roundRect(W-44*mm, y-14*mm, 34*mm, 14*mm, 2*mm, fill=1, stroke=0)
        c.setFillColor(colors.white); c.setFont("Helvetica-Bold", 9)
        c.drawCentredString(W-27*mm, y-5*mm, f"SLOT  {slot}")
        c.setFont("Helvetica", 7)
        c.drawCentredString(W-27*mm, y-10*mm, "Parking Space")

    crop_path = data.get('plate_crop_path')
    if crop_path and os.path.exists(crop_path):
        try:
            c.drawImage(ImageReader(crop_path), 8*mm, y-14*mm,
                        width=42*mm, height=14*mm,
                        preserveAspectRatio=True, mask='auto')
        except Exception: pass

    y -= 20*mm
    entry_str    = data['entry_t'].strftime('%d %b %Y  %H:%M:%S')
    exit_str     = data['exit_t'].strftime('%d %b %Y  %H:%M:%S')
    dur_hrs      = int(data['duration_hrs'])
    dur_mins     = int((data['duration_hrs'] % 1) * 60)
    duration_str = f"{dur_hrs}h {dur_mins:02d}m"

    rows = [
        ("Vehicle Type",    data.get('vtype', '—')),
        ("Slot Number",     f"Slot {slot}" if slot else '—'),
        ("Entry Time",      entry_str),
        ("Exit Time",       exit_str),
        ("Duration",        duration_str),
        ("Rate",            f"Rs. {data['rate']}/hr"),
        ("Subtotal",        f"Rs. {data['raw_bill']:.2f}"),
    ]
    if data.get('min_applied'):
        rows.append(("Min. Charge", f"Rs. {data['min_amount']} (applied)"))
    if data.get('smart_rate_note'):
        rows.append(("Smart Rate",  data['smart_rate_note']))
    if data.get('grace_applied'):
        rows.append(("Grace Period","FREE EXIT"))
    # Payment info
    if data.get('esewa_txn_id'):
        rows.append(("eSewa TXN ID", data['esewa_txn_id'][:20]))
    rows.append(("Payment Method", data.get('payment_method', 'eSewa')))

    c.setFont("Helvetica", 8)
    row_h = 6.5*mm
    for i, (k, v) in enumerate(rows):
        bg = LIGHT_BG if i%2==0 else colors.white
        c.setFillColor(bg)
        c.rect(8*mm, y-row_h, W-16*mm, row_h, fill=1, stroke=0)
        c.setFillColor(MID_GRAY); c.setFont("Helvetica", 8)
        c.drawString(12*mm, y-row_h+2*mm, k)
        c.setFillColor(DARK); c.setFont("Helvetica-Bold", 8)
        c.drawRightString(W-12*mm, y-row_h+2*mm, v)
        y -= row_h

    y -= 3*mm
    c.setFillColor(DARK)
    c.roundRect(8*mm, y-14*mm, W-16*mm, 14*mm, 3*mm, fill=1, stroke=0)
    c.setFillColor(colors.white); c.setFont("Helvetica-Bold", 11)
    c.drawString(14*mm, y-9*mm, "TOTAL AMOUNT")
    c.setFillColor(YELLOW); c.setFont("Helvetica-Bold", 14)
    c.drawRightString(W-14*mm, y-9*mm,
                      "FREE" if data.get('grace_applied') else f"Rs. {data['final_bill']}")

    # Payment verified badge
    if data.get('payment_verified'):
        y -= 18*mm
        c.setFillColor(ESEWA_GREEN)
        c.roundRect(8*mm, y-8*mm, W-16*mm, 8*mm, 2*mm, fill=1, stroke=0)
        c.setFillColor(colors.white); c.setFont("Helvetica-Bold", 8)
        c.drawCentredString(W/2, y-5.5*mm, "✓  PAYMENT VERIFIED VIA eSewa API")
    else:
        y -= 18*mm

    # eSewa QR
    qr_size = 28*mm
    qr_img_pil = _generate_esewa_qr_image()
    if qr_img_pil:
        try:
            from reportlab.lib.utils import ImageReader
            buf2 = BytesIO()
            qr_img_pil.save(buf2, format='PNG'); buf2.seek(0)
            c.drawImage(ImageReader(buf2), 8*mm, y-qr_size,
                        width=qr_size, height=qr_size)
            c.setFont("Helvetica", 7); c.setFillColor(MID_GRAY)
            c.drawString(8*mm, y-qr_size-4*mm,
                         f"Scan QR to pay via eSewa  |  {ESEWA_NUMBER}  ({ESEWA_NAME})")
        except Exception: pass

    c.setFillColor(ESEWA_GREEN)
    c.rect(0, 0, W, 12*mm, fill=1, stroke=0)
    c.setFillColor(colors.white); c.setFont("Helvetica-Bold", 8)
    c.drawCentredString(W/2, 7*mm, "Thank you for parking with us!")
    c.setFont("Helvetica", 7)
    c.drawCentredString(W/2, 3*mm, "Smart Parking Management System  |  v5.0  |  eSewa Verified")

    c.save()
    return pdf_path


# ─────────────────────────────────────────────────────────────────────────────
# Colour palette
# ─────────────────────────────────────────────────────────────────────────────
C = {
    'bg0':      '#050c1a',
    'bg1':      '#0b1528',
    'bg2':      '#112038',
    'bg3':      '#172948',
    'border':   '#1d3050',
    'border2':  '#254070',
    'blue':     '#3b82f6',
    'blue_dk':  '#1d4ed8',
    'cyan':     '#06b6d4',
    'green':    '#10b981',
    'green_dk': '#059669',
    'red':      '#ef4444',
    'red_dk':   '#b91c1c',
    'yellow':   '#f59e0b',
    'orange':   '#f97316',
    'purple':   '#8b5cf6',
    'txt0':     '#e2e8f0',
    'txt1':     '#7a95b8',
    'txt2':     '#3a5070',
    'white':    '#ffffff',
    'esewa':    '#60BB46',
    'esewa_dk': '#4a9a34',
    'gate_red': '#dc2626',
    'gate_grn': '#16a34a',
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
    return tk.Frame(parent, bg=C['bg1'], relief='flat', bd=0, **kw)


def sep(parent, color=C['border'], height=1, pady=8):
    f = tk.Frame(parent, bg=color, height=height)
    f.pack(fill='x', pady=pady)
    return f


def _bind_smooth_scroll(canvas_widget):
    def _on_mousewheel(event):
        if event.delta:
            canvas_widget.yview_scroll(int(-1*(event.delta/120)), 'units')
        elif event.num == 4:
            canvas_widget.yview_scroll(-1, 'units')
        elif event.num == 5:
            canvas_widget.yview_scroll(1, 'units')
    canvas_widget.bind('<MouseWheel>', _on_mousewheel)
    canvas_widget.bind('<Button-4>',   _on_mousewheel)
    canvas_widget.bind('<Button-5>',   _on_mousewheel)
    return _on_mousewheel


class IconButton(tk.Frame):
    def __init__(self, parent, text, command=None,
                 bg=C['bg2'], hover=C['border2'],
                 fg=C['txt0'], font=FONT_BODY_B,
                 padx=16, pady=8, **kw):
        super().__init__(parent, bg=bg, cursor='hand2', **kw)
        self._bg=bg; self._hover=hover; self._cmd=command
        self._lbl=tk.Label(self, text=text, font=font, fg=fg, bg=bg,
                           padx=padx, pady=pady)
        self._lbl.pack(fill='both', expand=True)
        for w in (self, self._lbl):
            w.bind('<Enter>',    self._on_enter)
            w.bind('<Leave>',    self._on_leave)
            w.bind('<Button-1>', self._on_click)

    def _on_enter(self, _=None):
        self.configure(bg=self._hover); self._lbl.configure(bg=self._hover)
    def _on_leave(self, _=None):
        self.configure(bg=self._bg);   self._lbl.configure(bg=self._bg)
    def _on_click(self, _=None):
        if self._cmd: self._cmd()
    def configure_colors(self, bg, hover):
        self._bg, self._hover=bg, hover
        self.configure(bg=bg); self._lbl.configure(bg=bg)


class BigButton(tk.Frame):
    def __init__(self, parent, text, command=None,
                 bg=C['green'], hover=C['green_dk'],
                 fg=C['white'], font=FONT_HEAD,
                 height=52, **kw):
        super().__init__(parent, bg=bg, cursor='hand2', height=height, **kw)
        self.pack_propagate(False)
        self._bg=bg; self._hover=hover; self._cmd=command
        self._lbl=tk.Label(self, text=text, font=font, fg=fg, bg=bg)
        self._lbl.pack(fill='both', expand=True)
        for w in (self, self._lbl):
            w.bind('<Enter>',    self._on_enter)
            w.bind('<Leave>',    self._on_leave)
            w.bind('<Button-1>', self._on_click)

    def _on_enter(self, _=None):
        self.configure(bg=self._hover); self._lbl.configure(bg=self._hover)
    def _on_leave(self, _=None):
        self.configure(bg=self._bg);   self._lbl.configure(bg=self._bg)
    def _on_click(self, _=None):
        if self._cmd: self._cmd()


# ─────────────────────────────────────────────────────────────────────────────
# Gate Status Widget  (animated CLOSED ↔ OPEN indicator)
# ─────────────────────────────────────────────────────────────────────────────

class GateStatusWidget(tk.Frame):
    """
    Animated barrier gate indicator.
    States: 'closed' (red pulsing) | 'waiting' (yellow blinking) | 'open' (green)
    """
    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C['bg1'], **kw)
        self._state  = 'closed'
        self._blink  = False
        self._blink_on = True

        # Gate icon canvas
        self._canvas = tk.Canvas(self, width=120, height=80,
                                 bg=C['bg1'], highlightthickness=0)
        self._canvas.pack()

        self._status_lbl = tk.Label(self, text="⛔  GATE CLOSED",
                                    font=('Consolas', 11, 'bold'),
                                    bg=C['bg1'], fg=C['red'])
        self._status_lbl.pack(pady=(4, 2))

        self._sub_lbl = tk.Label(self, text="Payment required to exit",
                                 font=('Segoe UI', 8),
                                 bg=C['bg1'], fg=C['txt2'])
        self._sub_lbl.pack()

        self._draw()
        self._animate()

    def _draw(self):
        c = self._canvas
        c.delete('all')
        # Gate post
        c.create_rectangle(8, 20, 20, 78, fill='#7a95b8', outline='')
        # Barrier arm
        if self._state == 'open':
            # Arm pointing up
            c.create_rectangle(14, 18, 20, 22, fill=C['gate_grn'], outline='')
            c.create_rectangle(16, 4, 18, 22, fill=C['gate_grn'], outline='')
            color = C['gate_grn']
        elif self._state == 'waiting':
            # Arm at 45°
            import math
            color = C['yellow'] if self._blink_on else C['bg3']
            c.create_line(14, 20, 80, 0, width=6, fill=color, capstyle='round')
        else:
            # Arm horizontal (closed)
            color = C['gate_red'] if self._blink_on else '#7a1010'
            c.create_rectangle(14, 14, 112, 22, fill=color, outline='')
            # Stripes
            for x in range(20, 112, 18):
                c.create_rectangle(x, 14, x+9, 22, fill='white', outline='')

        # Status circle
        sc = C['gate_grn'] if self._state=='open' else (C['yellow'] if self._state=='waiting' else C['gate_red'])
        c.create_oval(90, 30, 115, 55, fill=sc, outline='white', width=2)
        sym = '✓' if self._state=='open' else ('⏳' if self._state=='waiting' else '✕')
        c.create_text(102, 42, text=sym, font=('Segoe UI', 12, 'bold'), fill='white')

    def _animate(self):
        if self._state != 'open':
            self._blink_on = not self._blink_on
            self._draw()
        self.after(600, self._animate)

    def set_state(self, state: str, sub_text: str = ""):
        """state: 'closed' | 'waiting' | 'open'"""
        self._state = state
        self._blink_on = True
        self._draw()
        if state == 'open':
            self._status_lbl.config(text="✅  GATE OPEN — CLEAR TO GO!", fg=C['gate_grn'])
            self._sub_lbl.config(text=sub_text or "Have a safe journey!", fg=C['green'])
        elif state == 'waiting':
            self._status_lbl.config(text="⏳  PROCESSING PAYMENT…", fg=C['yellow'])
            self._sub_lbl.config(text=sub_text or "Please wait…", fg=C['yellow'])
        else:
            self._status_lbl.config(text="⛔  GATE CLOSED", fg=C['gate_red'])
            self._sub_lbl.config(text=sub_text or "Payment required to exit", fg=C['txt2'])


# ─────────────────────────────────────────────────────────────────────────────
# Login Window
# ─────────────────────────────────────────────────────────────────────────────

class LoginWindow:
    def __init__(self, root, on_success):
        self.root=root; self.on_success=on_success
        self.win=tk.Toplevel(root)
        self.win.title("Login — Smart Parking System v5")
        self.win.geometry("440x540")
        self.win.configure(bg=C['bg0'])
        self.win.resizable(False, False)
        self.win.grab_set()
        self.win.protocol("WM_DELETE_WINDOW", self._on_cancel)
        self.win.update_idletasks()
        sw=self.win.winfo_screenwidth(); sh=self.win.winfo_screenheight()
        self.win.geometry(f"440x540+{(sw-440)//2}+{(sh-540)//2}")
        self._build()

    def _build(self):
        tk.Frame(self.win, bg=C['blue'], height=5).pack(fill='x')
        logo_frame=tk.Frame(self.win, bg=C['bg0']); logo_frame.pack(pady=(32,8))
        tk.Label(logo_frame, text="🅿", font=('Segoe UI',48),
                 bg=C['bg0'], fg=C['blue']).pack()
        tk.Label(logo_frame, text="SMART PARKING",
                 font=('Consolas',18,'bold'), bg=C['bg0'], fg=C['txt0']).pack()
        tk.Label(logo_frame, text="Management System  —  v5  |  eSewa API  |  Smart Slots",
                 font=('Segoe UI',9), bg=C['bg0'], fg=C['txt2']).pack(pady=(2,0))

        form=tk.Frame(self.win, bg=C['bg1'])
        form.pack(fill='x', padx=40, pady=24)
        tk.Label(form, text="Sign in to continue",
                 font=('Segoe UI',10,'bold'),
                 bg=C['bg1'], fg=C['txt1']).pack(pady=(16,14))

        for field_label, attr in [("Username","_user_var"),("Password","_pass_var")]:
            row=tk.Frame(form, bg=C['bg1']); row.pack(fill='x', padx=20, pady=(0,10))
            tk.Label(row, text=field_label, font=FONT_SMALL,
                     bg=C['bg1'], fg=C['txt2'], anchor='w').pack(fill='x')
            var=tk.StringVar(); setattr(self,attr,var)
            show='*' if attr=='_pass_var' else ''
            e=tk.Entry(row, textvariable=var, font=FONT_BODY,
                       bg=C['bg3'], fg=C['txt0'], insertbackground=C['txt0'],
                       relief='flat', bd=0, show=show)
            e.pack(fill='x', ipady=8)
            tk.Frame(row, bg=C['border2'], height=1).pack(fill='x')
            if attr=='_user_var': e.focus_set()
            e.bind('<Return>', lambda _: self._login())

        self._msg_lbl=tk.Label(form, text="", font=('Segoe UI',9),
                                bg=C['bg1'], fg=C['red'])
        self._msg_lbl.pack(pady=(0,6))
        btn_row=tk.Frame(form, bg=C['bg1']); btn_row.pack(fill='x', padx=20, pady=(0,20))
        BigButton(btn_row, "🔓  LOGIN", command=self._login,
                  bg=C['blue'], hover=C['blue_dk'], height=44,
                  font=FONT_HEAD).pack(fill='x')
        tk.Label(self.win, text="Default: admin / admin1234  (change in Settings → Account)",
                 font=('Segoe UI',8), bg=C['bg0'], fg=C['txt2'],
                 wraplength=400).pack(pady=(0,16))

    def _login(self):
        creds=_load_credentials()
        if (self._user_var.get().strip()==creds['username'] and
                _hash_password(self._pass_var.get())==creds['password_hash']):
            self.win.destroy(); self.on_success()
        else:
            self._msg_lbl.config(text="⚠  Incorrect username or password.")
            self._pass_var.set("")

    def _on_cancel(self): self.root.destroy()


# ─────────────────────────────────────────────────────────────────────────────
# Credential helpers
# ─────────────────────────────────────────────────────────────────────────────

def _hash_password(pw):
    return hashlib.sha256(pw.encode('utf-8')).hexdigest()

def _load_credentials():
    d={'username':'admin','password_hash':_hash_password('admin1234')}
    p=os.path.join(_get_data_dir(),'parking_credentials.json')
    if os.path.exists(p):
        try:
            with open(p) as f: d.update(json.loads(f.read().strip()))
        except Exception: pass
    return d

def _save_credentials(username, password_hash):
    p=os.path.join(_get_data_dir(),'parking_credentials.json')
    with open(p,'w') as f:
        json.dump({'username':username,'password_hash':password_hash}, f, indent=4)


# ─────────────────────────────────────────────────────────────────────────────
# Main App
# ─────────────────────────────────────────────────────────────────────────────

class ModernParkingSystem:

    def __init__(self, root):
        self.root=root
        self.root.title("Smart Parking Management System  v5  —  eSewa API  |  Smart Slots")
        self.root.geometry("1440x900")
        self.root.configure(bg=C['bg0'])
        self.root.minsize(1200,760)

        self.current_frame_entry  = None
        self.current_frame_exit   = None
        self.video_capture_entry  = None
        self.video_capture_exit   = None
        self.camera_running_entry = False
        self.camera_running_exit  = False
        self._last_plate_crop     = None

        self._frame_count  = {'entry':0,'exit':0}
        self._detecting    = {'entry':False,'exit':False}
        self._detect_every = 20

        self._VOTE_THRESHOLD = 3
        self._VOTE_WINDOW    = 20.0
        self._vote_log:  dict = {'entry':[],'exit':[]}
        self._vote_label: dict = {'entry':None,'exit':None}

        self._last_detected:  dict = {}
        self._detect_cooldown = 3.0
        self._pending_exit:  dict = {}

        self.registered_vehicles = {}
        self.settings    = self.load_settings()
        self.update_timers = True

        # Slot allocator
        self.slot_allocator = SlotAllocator(_get_data_dir())

        # Start eSewa callback server
        self._callback_server = _start_callback_server()

        # Pending payments: txn_uuid → {plate, amount, callback, verified}
        self._pending_payments: dict = {}

        self.load_models()
        self.setup_styles()
        self.setup_ui()
        self.load_vehicles()
        self.start_timer_updates()

    # ── Persistence ───────────────────────────────────────────────────────────

    def load_settings(self):
        defaults = {
            '2w_capacity': 50, '4w_capacity': 30,
            '2w_rate': 20,     '4w_rate': 50,
            '2w_occupied': 0,  '4w_occupied': 0,
            'min_charge_enabled':       False,
            'min_charge_amount':        20,
            'min_charge_minutes':       30,
            'weekend_rate_multiplier':  1.25,
            'peak_surcharge_pct':       20,
            'peak_threshold_pct':       90,
            'grace_period_minutes':     5,
            # eSewa API settings
            'esewa_mode':          'test',   # 'test' or 'live'
            'esewa_merchant_code': 'EPAYTEST',
            'esewa_secret':        '8gBm/:&EnhH.1/q',
            'esewa_use_api':       True,
        }
        path=os.path.join(_get_data_dir(),'parking_settings.json')
        if os.path.exists(path):
            try:
                with open(path) as f:
                    content=f.read().strip()
                    if content: defaults.update(json.loads(content))
            except Exception: pass
        # Safety: clamp rates/capacities to sane values to prevent corruption
        for int_key in ('2w_capacity','4w_capacity','2w_rate','4w_rate',
                        '2w_occupied','4w_occupied','min_charge_amount',
                        'min_charge_minutes','peak_surcharge_pct',
                        'peak_threshold_pct','grace_period_minutes'):
            try:
                v = int(float(defaults[int_key]))
                # Clamp rates to max Rs. 10000/hr, capacities to max 9999
                if int_key in ('2w_rate','4w_rate'):
                    v = max(1, min(v, 10000))
                elif int_key in ('2w_capacity','4w_capacity'):
                    v = max(1, min(v, 9999))
                elif int_key in ('2w_occupied','4w_occupied'):
                    v = max(0, v)
                defaults[int_key] = v
            except Exception:
                pass
        for float_key in ('weekend_rate_multiplier',):
            try:
                v = float(defaults[float_key])
                defaults[float_key] = max(1.0, min(v, 5.0))
            except Exception:
                pass
        return defaults

    def save_settings(self):
        path=os.path.join(_get_data_dir(),'parking_settings.json')
        with open(path,'w') as f: json.dump(self.settings,f,indent=4)

    def save_vehicles(self):
        path=os.path.join(_get_data_dir(),'registered_vehicles.json')
        with open(path,'w') as f: json.dump(self.registered_vehicles,f,indent=4)

    def load_vehicles(self):
        path=os.path.join(_get_data_dir(),'registered_vehicles.json')
        if os.path.exists(path):
            try:
                with open(path) as f:
                    content=f.read().strip()
                    if content: self.registered_vehicles=json.loads(content)
            except Exception: self.registered_vehicles={}
        # Sync slot allocations with current vehicles
        for plate in list(self.slot_allocator.allocations.keys()):
            if plate not in self.registered_vehicles:
                del self.slot_allocator.allocations[plate]
        self.slot_allocator._save()
        self.update_dashboard()

    # ── Model loading ─────────────────────────────────────────────────────────

    def load_models(self):
        try:
            from ultralytics import YOLO
            from huggingface_hub import hf_hub_download, list_repo_files
            repo_id = "workwithPujan/detect_plate.pt"
            plate_path = hf_hub_download(repo_id=repo_id, filename="detect_plate.pt")
            text_path = hf_hub_download(repo_id=repo_id, filename="robo_best.pt")
            self.plate_detection_model = YOLO(plate_path)
            self.text_extraction_model = YOLO(text_path)
            self.models_loaded=True
            print("✓ Both models loaded")
        except Exception as e:
            print(f"⚠ Models not loaded: {e}")
            self.plate_detection_model=None
            self.text_extraction_model=None
            self.models_loaded=False

    # ── Smart Pricing Engine ──────────────────────────────────────────────────

    def get_smart_rate(self, vtype: str) -> tuple:
        base_rate=self.settings['2w_rate' if vtype=='2W' else '4w_rate']
        rate=base_rate; notes=[]
        weekday=datetime.now().weekday()
        if weekday>=5:
            mult=self.settings.get('weekend_rate_multiplier',1.25)
            rate=rate*mult
            day="Saturday" if weekday==5 else "Sunday"
            notes.append(f"Weekend ({day}) ×{mult}")
        occ_key='2w_occupied' if vtype=='2W' else '4w_occupied'
        cap_key='2w_capacity' if vtype=='2W' else '4w_capacity'
        occ=self.settings.get(occ_key,0); cap=self.settings.get(cap_key,1)
        pct=(occ/max(cap,1))*100
        peak_thresh=self.settings.get('peak_threshold_pct',90)
        if pct>=peak_thresh:
            surcharge=self.settings.get('peak_surcharge_pct',20)
            rate=rate*(1+surcharge/100)
            notes.append(f"Peak +{surcharge}% ({pct:.0f}% full)")
        rate=round(rate,2)
        note=" | ".join(notes) if notes else ""
        return rate, note

    def _is_grace_period(self, entry_time: datetime) -> bool:
        grace=self.settings.get('grace_period_minutes',5)
        elapsed=(datetime.now()-entry_time).total_seconds()/60
        return elapsed<=grace

    def _apply_min_charge(self, duration_hours, raw_bill):
        enabled=self.settings.get('min_charge_enabled',False)
        min_amount=self.settings.get('min_charge_amount',20)
        min_mins=self.settings.get('min_charge_minutes',30)
        if enabled and (duration_hours*60)<min_mins:
            final=self.round_bill(max(raw_bill,min_amount))
            return True, min_amount, final
        return False, min_amount, self.round_bill(raw_bill)

    # ── eSewa API helpers ─────────────────────────────────────────────────────

    def _esewa_config(self):
        mode=self.settings.get('esewa_mode','test')
        if mode=='live':
            return {
                'merchant': self.settings.get('esewa_merchant_code','EPAYTEST'),
                'secret':   self.settings.get('esewa_secret', ESEWA_TEST_SECRET),
                'url':      ESEWA_LIVE_URL,
                'verify':   ESEWA_LIVE_VERIFY,
            }
        return {
            'merchant': ESEWA_TEST_MERCHANT,
            'secret':   ESEWA_TEST_SECRET,
            'url':      ESEWA_TEST_URL,
            'verify':   ESEWA_TEST_VERIFY,
        }

    def _initiate_esewa_payment(self, plate: str, amount: float,
                                 on_success, on_failure):
        """
        Open browser → eSewa payment page.
        Polls callback server for result.
        on_success(txn_uuid) / on_failure(reason) called on main thread.
        """
        cfg      = self._esewa_config()
        txn_uuid = f"PKG-{re.sub(r'[^A-Za-z0-9]','',plate)}-{int(time.time())}"
        success_url = f"http://127.0.0.1:{CALLBACK_PORT}/esewa/success?transaction_uuid={txn_uuid}"
        failure_url = f"http://127.0.0.1:{CALLBACK_PORT}/esewa/failure?transaction_uuid={txn_uuid}"

        html = _build_esewa_form_html(
            amount       = amount,
            transaction_uuid = txn_uuid,
            product_code = cfg['merchant'],
            secret       = cfg['secret'],
            esewa_url    = cfg['url'],
            success_url  = success_url,
            failure_url  = failure_url,
        )

        # Save HTML to temp file and open in browser
        tmp_dir  = os.path.join(_get_data_dir(), "_tmp_esewa")
        os.makedirs(tmp_dir, exist_ok=True)
        html_path = os.path.join(tmp_dir, f"pay_{txn_uuid}.html")
        with open(html_path, 'w', encoding='utf-8') as f:
            f.write(html)

        webbrowser.open(f"file:///{html_path.replace(os.sep,'/')}")

        # Poll callback in background
        def _poll():
            deadline = time.time() + 300  # 5-minute timeout
            while time.time() < deadline:
                result = _CallbackHandler.payment_results.get(txn_uuid)
                if result:
                    if result['status'] == 'success':
                        # Verify via API
                        verify_res = _esewa_verify_payment(
                            txn_uuid, amount, cfg['merchant'], cfg['verify'])
                        api_status = verify_res.get('status','UNKNOWN')
                        if api_status == 'COMPLETE':
                            self.root.after(0, lambda: on_success(txn_uuid, True))
                        else:
                            # Browser says success but API not yet COMPLETE — accept with warning
                            self.root.after(0, lambda: on_success(txn_uuid, False))
                    else:
                        self.root.after(0, lambda: on_failure("Payment cancelled or failed."))
                    return
                time.sleep(1)
            self.root.after(0, lambda: on_failure("Payment timeout (5 minutes)."))

        Thread(target=_poll, daemon=True).start()
        return txn_uuid

    # ── TTK Styles ────────────────────────────────────────────────────────────

    def setup_styles(self):
        s=ttk.Style(); s.theme_use('clam')
        s.configure('.',background=C['bg0'],foreground=C['txt0'],borderwidth=0,focuscolor='none')
        s.configure('TNotebook',background=C['bg0'],borderwidth=0,tabmargins=[0,0,0,0])
        s.configure('TNotebook.Tab',background=C['bg1'],foreground=C['txt1'],
                    padding=[24,13],borderwidth=0,font=('Segoe UI',10,'bold'))
        s.map('TNotebook.Tab',
              background=[('selected',C['bg2'])],
              foreground=[('selected',C['blue'])],
              expand=[('selected',[0,0,0,0])])
        s.configure('TFrame',background=C['bg0'])
        s.configure('TLabel',background=C['bg1'],foreground=C['txt0'],font=FONT_BODY)
        s.configure('TEntry',fieldbackground=C['bg3'],foreground=C['txt0'],
                    borderwidth=1,insertcolor=C['txt0'])
        s.configure('TRadiobutton',background=C['bg1'],foreground=C['txt0'],font=FONT_BODY)
        s.configure('Vertical.TScrollbar',background=C['bg3'],
                    troughcolor=C['bg1'],arrowcolor=C['txt1'],borderwidth=0)
        s.configure('TCheckbutton',background=C['bg1'],foreground=C['txt0'],font=FONT_BODY)
        s.configure('Green.Horizontal.TProgressbar',
                    background=C['green'],troughcolor=C['bg3'],borderwidth=0)
        s.configure('Yellow.Horizontal.TProgressbar',
                    background=C['yellow'],troughcolor=C['bg3'],borderwidth=0)
        s.configure('Red.Horizontal.TProgressbar',
                    background=C['red'],troughcolor=C['bg3'],borderwidth=0)

    # ── Top-level UI ──────────────────────────────────────────────────────────

    def setup_ui(self):
        self._build_header()
        self.notebook=ttk.Notebook(self.root)
        self.notebook.pack(fill='both',expand=True)
        self.entry_tab     = ttk.Frame(self.notebook)
        self.exit_tab      = ttk.Frame(self.notebook)
        self.dashboard_tab = ttk.Frame(self.notebook)
        self.history_tab   = ttk.Frame(self.notebook)
        self.settings_tab  = ttk.Frame(self.notebook)
        self.notebook.add(self.entry_tab,     text='  🚘  ENTRY  ')
        self.notebook.add(self.exit_tab,      text='  🚪  EXIT  ')
        self.notebook.add(self.dashboard_tab, text='  📊  DASHBOARD  ')
        self.notebook.add(self.history_tab,   text='  📋  HISTORY  ')
        self.notebook.add(self.settings_tab,  text='  ⚙  SETTINGS  ')
        self.setup_entry_tab()
        self.setup_exit_tab()
        self.setup_dashboard_tab()
        self.setup_history_tab()
        self.setup_settings_tab()
        self._build_statusbar()

    def _build_header(self):
        hdr=tk.Frame(self.root,bg=C['bg1'],height=72); hdr.pack(fill='x')
        hdr.pack_propagate(False)
        left=tk.Frame(hdr,bg=C['bg1']); left.pack(side='left',padx=24,fill='y')
        tk.Frame(left,bg=C['esewa'],width=4).pack(side='left',fill='y',pady=12)
        txt=tk.Frame(left,bg=C['bg1']); txt.pack(side='left',padx=(12,0),pady=12)
        tk.Label(txt,text="SMART PARKING",font=('Consolas',20,'bold'),
                 bg=C['bg1'],fg=C['txt0']).pack(anchor='w')
        tk.Label(txt,text="Management System  —  Professional Edition v5  |  eSewa API  |  Smart Slot Allocation",
                 font=('Segoe UI',9),bg=C['bg1'],fg=C['txt1']).pack(anchor='w')
        right=tk.Frame(hdr,bg=C['bg1']); right.pack(side='right',padx=28,fill='y')
        IconButton(right,"🔒 Logout",command=self._logout,
                   bg=C['bg0'],hover=C['border'],fg=C['txt2'],
                   font=('Segoe UI',8),padx=10,pady=4).pack(anchor='e',pady=(8,2))
        self.time_label=tk.Label(right,text="",font=('Consolas',11,'bold'),
                                  bg=C['bg1'],fg=C['txt0'])
        self.time_label.pack(anchor='e')
        chip=tk.Frame(right,bg=C['bg0']); chip.pack(anchor='e',pady=(4,0))
        tk.Label(chip,text="●",font=('Segoe UI',8),fg=C['esewa'],bg=C['bg0']).pack(side='left',padx=(6,2))
        tk.Label(chip,text="SYSTEM ONLINE  |  eSewa READY",
                 font=('Segoe UI',8,'bold'),fg=C['esewa'],bg=C['bg0']).pack(side='left',padx=(0,6))
        tk.Frame(self.root,bg=C['border'],height=1).pack(fill='x')
        self._update_clock()

    def _update_clock(self):
        self.time_label.config(text=datetime.now().strftime("%a %d %b %Y   %H:%M:%S"))
        self.root.after(1000,self._update_clock)

    def _logout(self):
        if messagebox.askyesno("Logout","Are you sure you want to logout?"):
            self.update_timers=False
            self.stop_camera('entry'); self.stop_camera('exit')
            self.root.withdraw()
            LoginWindow(self.root,self._on_login_success)

    def _on_login_success(self):
        self.update_timers=True; self.root.deiconify(); self.start_timer_updates()

    def _build_statusbar(self):
        bar=tk.Frame(self.root,bg=C['bg1'],height=28); bar.pack(fill='x',side='bottom')
        bar.pack_propagate(False)
        tk.Frame(self.root,bg=C['border'],height=1).pack(fill='x',side='bottom')
        self.status_label=tk.Label(bar,text="●  Ready",anchor='w',padx=16,
                                    bg=C['bg1'],fg=C['txt1'],font=('Segoe UI',9))
        self.status_label.pack(side='left',fill='y')
        tk.Label(bar,text="v5.0  |  eSewa API v2  |  Smart Slots  |  PDF Receipts  |  Payment Gate",
                 bg=C['bg1'],fg=C['txt2'],font=('Segoe UI',8),anchor='e',padx=16).pack(side='right',fill='y')

    def _set_status(self,text,color=C['txt1']):
        self.status_label.config(text=f"●  {text}",fg=color)

    # ─────────────────────────────────────────────────────────────────────────
    # ENTRY TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_entry_tab(self):
        root_f=tk.Frame(self.entry_tab,bg=C['bg0'])
        root_f.pack(fill='both',expand=True,padx=16,pady=16)

        cam_card=card(root_f); cam_card.pack(side='left',fill='both',expand=True,padx=(0,10))
        ch=tk.Frame(cam_card,bg=C['bg2'],height=44); ch.pack(fill='x'); ch.pack_propagate(False)
        tk.Label(ch,text="📹  CAMERA FEED",font=FONT_HEAD,bg=C['bg2'],fg=C['txt0']).pack(side='left',padx=16,pady=10)
        tb=tk.Frame(cam_card,bg=C['bg1'],height=48); tb.pack(fill='x'); tb.pack_propagate(False)
        for txt,cmd,bg,hv in [
            ("📁  Image",  lambda: self.select_image('entry'), C['bg2'],  C['border2']),
            ("🎥  Video",  lambda: self.select_video('entry'), C['bg2'],  C['border2']),
            ("📷  Camera", lambda: self.start_camera('entry'), C['blue'], C['blue_dk']),
            ("⏹  Stop",   lambda: self.stop_camera('entry'),  C['red'],  C['red_dk']),
        ]:
            IconButton(tb,txt,command=cmd,bg=bg,hover=hv,
                       fg=C['white'],padx=18,pady=8).pack(side='left',padx=(8,0),pady=8)
        self.video_label_entry=tk.Label(cam_card,bg='#000',text="No feed",fg=C['txt2'],font=FONT_BODY)
        self.video_label_entry.pack(fill='both',expand=True,padx=2,pady=(0,2))

        reg_card=card(root_f); reg_card.pack(side='right',fill='y',padx=(10,0))
        reg_card.configure(width=420); reg_card.pack_propagate(False)

        rh=tk.Frame(reg_card,bg=C['bg2'],height=44); rh.pack(fill='x'); rh.pack_propagate(False)
        tk.Label(rh,text="🎯  VEHICLE REGISTRATION  +  SLOT ASSIGNMENT",
                 font=('Consolas',10,'bold'),bg=C['bg2'],fg=C['txt0']).pack(side='left',padx=16,pady=10)
        
        # Slide down button
        self.entry_slide_btn = IconButton(rh, "🔽", command=lambda: self.entry_canvas.yview_moveto(1.0),
                                           bg=C['bg2'], hover=C['border2'], fg=C['txt0'],
                                           font=('Segoe UI', 10), padx=8, pady=4)
        self.entry_slide_btn.pack(side='right', padx=10)

        # Space bar
        self._entry_space_bar_frame=tk.Frame(reg_card,bg=C['bg3'])
        self._entry_space_bar_frame.pack(fill='x')
        self._entry_space_info=tk.Label(self._entry_space_bar_frame,text="",
                                         font=('Consolas',8,'bold'),bg=C['bg3'],fg=C['txt0'],pady=3)
        self._entry_space_info.pack(side='left',padx=10)
        self._entry_full_lbl=tk.Label(self._entry_space_bar_frame,text="",
                                       font=('Consolas',9,'bold'),bg=C['bg3'],fg=C['red'])
        self._entry_full_lbl.pack(side='right',padx=10)

        notice=tk.Frame(reg_card,bg='#1a2a00'); notice.pack(fill='x')
        tk.Label(notice,text="ℹ  AI detects plate & type — system auto-assigns nearest available slot",
                 font=('Segoe UI',8,'italic'),bg='#1a2a00',fg='#a3e635',anchor='w',padx=10).pack(fill='x',pady=4)

        scroll_container=tk.Frame(reg_card,bg=C['bg1']); scroll_container.pack(fill='both',expand=True)
        self.entry_canvas=tk.Canvas(scroll_container,bg=C['bg1'],highlightthickness=0,bd=0)
        scrollbar=ttk.Scrollbar(scroll_container,orient='vertical',command=self.entry_canvas.yview)
        self.entry_canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side='right',fill='y'); self.entry_canvas.pack(side='left',fill='both',expand=True)
        scroll_frame=tk.Frame(self.entry_canvas,bg=C['bg1'])
        canvas_window=self.entry_canvas.create_window((0,0),window=scroll_frame,anchor='nw')
        scroll_frame.bind('<Configure>',lambda _: self.entry_canvas.configure(scrollregion=self.entry_canvas.bbox('all')))
        self.entry_canvas.bind('<Configure>',lambda e: self.entry_canvas.itemconfig(canvas_window,width=e.width))
        _bind_smooth_scroll(self.entry_canvas)

        inner=tk.Frame(scroll_frame,bg=C['bg1']); inner.pack(fill='both',expand=True,padx=16,pady=12)

        self._section_label(inner,"VEHICLE TYPE")
        self.vehicle_type_entry=tk.StringVar(value="2W")
        vt_row=tk.Frame(inner,bg=C['bg1']); vt_row.pack(fill='x',pady=(4,4))
        for lbl,val in [("🏍️  2-Wheeler","2W"),("🚗  4-Wheeler","4W")]:
            ttk.Radiobutton(vt_row,text=lbl,variable=self.vehicle_type_entry,
                            value=val,command=self._refresh_entry_rate).pack(side='left',padx=8)
        self._auto_vtype_label_entry=tk.Label(inner,text="",font=('Segoe UI',8,'bold'),
                                               bg=C['bg1'],fg=C['purple'])
        self._auto_vtype_label_entry.pack(pady=(0,6))

        BigButton(inner,"🔍   DETECT NUMBER PLATE",
                  command=lambda: self.detect_vehicle('entry'),
                  bg=C['blue'],hover=C['blue_dk'],height=44).pack(fill='x',pady=(0,10))

        self._section_label(inner,"NUMBER PLATE  (Roman / English)")
        plate_frame=tk.Frame(inner,bg=C['bg3'],bd=1,relief='flat'); plate_frame.pack(fill='x',pady=(4,0))
        self.number_plate_entry=tk.Entry(plate_frame,font=FONT_PLATE,bg=C['bg3'],fg=C['cyan'],
                                          insertbackground=C['txt0'],relief='flat',bd=0,justify='center')
        self.number_plate_entry.pack(fill='x',ipady=12,padx=4)
        tk.Frame(inner,bg=C['cyan'],height=2).pack(fill='x')

        self._section_label(inner,"NUMBER PLATE  (Nepali / देवनागरी)")
        nepali_outer=tk.Frame(inner,bg=C['bg2'],bd=1,relief='flat'); nepali_outer.pack(fill='x',pady=(4,0))
        self.nepali_plate_entry=tk.Label(nepali_outer,text="—",font=('Nirmala UI',20,'bold'),
                                          bg=C['bg2'],fg=C['orange'],relief='flat',anchor='center',pady=10)
        self.nepali_plate_entry.pack(fill='x')
        tk.Frame(inner,bg=C['orange'],height=2).pack(fill='x')

        def _on_entry_plate_change(*_):
            t=self.number_plate_entry.get().strip()
            self.nepali_plate_entry.config(text=plate_to_nepali_script(t) if t else "—")
        self.number_plate_entry.bind('<KeyRelease>',_on_entry_plate_change)

        self.detection_info_entry=tk.Label(inner,text="",font=FONT_SMALL,
                                            bg=C['bg1'],fg=C['txt1'],wraplength=380)
        self.detection_info_entry.pack(pady=(6,2))
        self._vote_label['entry']=tk.Label(inner,text="",font=('Consolas',9,'bold'),
                                            bg=C['bg1'],fg=C['yellow'],wraplength=380)
        self._vote_label['entry'].pack(pady=(0,6))

        sep(inner,pady=8)
        self._section_label(inner,"ENTRY DETAILS  (Smart Rate + Slot Preview)")
        info_box=tk.Frame(inner,bg=C['bg2'],bd=0); info_box.pack(fill='x',pady=(6,0))
        self.entry_time_label  = self._info_row(info_box,"⏱  Entry Time","—")
        self.entry_rate_label  = self._info_row(info_box,"💰  Smart Tariff","—")
        self.entry_note_label  = self._info_row(info_box,"📌  Rate Modifier","—")
        self.entry_slot_label  = self._info_row(info_box,"🅿  Predicted Slot","—")
        self.entry_pred_label  = self._info_row(info_box,"🕐  Predicted Stay","—")

        tk.Frame(inner,bg=C['bg1'],height=10).pack()
        self._register_entry_btn=BigButton(inner,"✅   REGISTER VEHICLE + ASSIGN SLOT",
                                            command=self.register_entry,
                                            bg=C['green'],hover=C['green_dk'],height=52)
        self._register_entry_btn.pack(fill='x',pady=(0,6))
        self._refresh_entry_rate()

    def _refresh_entry_rate(self, _=None):
        vt=self.vehicle_type_entry.get()
        rate,note=self.get_smart_rate(vt)
        self.entry_rate_label.config(text=f"Rs. {rate}/hr")
        self.entry_note_label.config(text=note if note else "Standard rate",
                                      fg=C['yellow'] if note else C['txt1'])
        # Preview slot
        plate=self.number_plate_entry.get().strip() or "NEW"
        cap2=self.settings.get('2w_capacity',50)
        cap4=self.settings.get('4w_capacity',30)
        try:
            slot,is_long,pred=self.slot_allocator.allocate(plate,vt,cap2,cap4)
            self.entry_slot_label.config(text=f"Slot {slot}  ({'Back—long stay' if is_long else 'Front—short stay'})",
                                          fg=C['purple'] if is_long else C['cyan'])
            self.entry_pred_label.config(text=f"{pred:.1f} hrs (predicted)",
                                          fg=C['yellow'] if is_long else C['green'])
        except Exception:
            pass

    # ─────────────────────────────────────────────────────────────────────────
    # EXIT TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_exit_tab(self):
        root_f=tk.Frame(self.exit_tab,bg=C['bg0'])
        root_f.pack(fill='both',expand=True,padx=16,pady=16)

        cam_card=card(root_f); cam_card.pack(side='left',fill='both',expand=True,padx=(0,10))
        ch=tk.Frame(cam_card,bg=C['bg2'],height=44); ch.pack(fill='x'); ch.pack_propagate(False)
        tk.Label(ch,text="📹  CAMERA FEED",font=FONT_HEAD,bg=C['bg2'],fg=C['txt0']).pack(side='left',padx=16,pady=10)
        tb=tk.Frame(cam_card,bg=C['bg1'],height=48); tb.pack(fill='x'); tb.pack_propagate(False)
        for txt,cmd,bg,hv in [
            ("📁  Image",  lambda: self.select_image('exit'), C['bg2'],  C['border2']),
            ("🎥  Video",  lambda: self.select_video('exit'), C['bg2'],  C['border2']),
            ("📷  Camera", lambda: self.start_camera('exit'), C['blue'], C['blue_dk']),
            ("⏹  Stop",   lambda: self.stop_camera('exit'),  C['red'],  C['red_dk']),
        ]:
            IconButton(tb,txt,command=cmd,bg=bg,hover=hv,
                       fg=C['white'],padx=18,pady=8).pack(side='left',padx=(8,0),pady=8)
        self.video_label_exit=tk.Label(cam_card,bg='#000',text="No feed",fg=C['txt2'],font=FONT_BODY)
        self.video_label_exit.pack(fill='both',expand=True,padx=2,pady=(0,2))

        exit_card=card(root_f); exit_card.pack(side='right',fill='y',padx=(10,0))
        exit_card.configure(width=450); exit_card.pack_propagate(False)

        eh=tk.Frame(exit_card,bg=C['red_dk'],height=44); eh.pack(fill='x'); eh.pack_propagate(False)
        tk.Label(eh,text="🚪  VEHICLE EXIT & BILLING",font=FONT_HEAD,
                 bg=C['red_dk'],fg=C['white']).pack(side='left',padx=16,pady=10)

        notice=tk.Frame(exit_card,bg='#1a2a00'); notice.pack(fill='x')
        tk.Label(notice,text="ℹ  Gate remains CLOSED until eSewa payment is verified",
                 font=('Segoe UI',8,'italic'),bg='#1a2a00',fg='#a3e635',anchor='w',padx=10).pack(fill='x',pady=4)

        scroll_container=tk.Frame(exit_card,bg=C['bg1']); scroll_container.pack(fill='both',expand=True)
        canvas=tk.Canvas(scroll_container,bg=C['bg1'],highlightthickness=0,bd=0)
        scrollbar=ttk.Scrollbar(scroll_container,orient='vertical',command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side='right',fill='y'); canvas.pack(side='left',fill='both',expand=True)
        scroll_frame=tk.Frame(canvas,bg=C['bg1'])
        canvas_window=canvas.create_window((0,0),window=scroll_frame,anchor='nw')
        scroll_frame.bind('<Configure>',lambda _: canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.bind('<Configure>',lambda e: canvas.itemconfig(canvas_window,width=e.width))
        _bind_smooth_scroll(canvas)

        pad=tk.Frame(scroll_frame,bg=C['bg1']); pad.pack(fill='x',padx=16,pady=12)

        self._section_label(pad,"VEHICLE TYPE")
        self.vehicle_type_exit=tk.StringVar(value="2W")
        vt_row=tk.Frame(pad,bg=C['bg1']); vt_row.pack(fill='x',pady=(4,4))
        for lbl,val in [("🏍️  2-Wheeler","2W"),("🚗  4-Wheeler","4W")]:
            ttk.Radiobutton(vt_row,text=lbl,variable=self.vehicle_type_exit,value=val).pack(side='left',padx=8)
        self._auto_vtype_label_exit=tk.Label(pad,text="",font=('Segoe UI',8,'bold'),
                                              bg=C['bg1'],fg=C['purple'])
        self._auto_vtype_label_exit.pack(pady=(0,6))

        BigButton(pad,"🔍   DETECT NUMBER PLATE",
                  command=lambda: self.detect_vehicle('exit'),
                  bg=C['blue'],hover=C['blue_dk'],height=44).pack(fill='x',pady=(0,10))

        self._section_label(pad,"NUMBER PLATE  (Roman / English)")
        plate_frame_exit=tk.Frame(pad,bg=C['bg3'],bd=1,relief='flat'); plate_frame_exit.pack(fill='x',pady=(4,0))
        self.number_plate_exit=tk.Entry(plate_frame_exit,font=FONT_PLATE,bg=C['bg3'],fg=C['cyan'],
                                         insertbackground=C['txt0'],relief='flat',bd=0,justify='center')
        self.number_plate_exit.pack(fill='x',ipady=12,padx=4)
        tk.Frame(pad,bg=C['cyan'],height=2).pack(fill='x')

        self._section_label(pad,"NUMBER PLATE  (Nepali / देवनागरी)")
        nepali_outer_exit=tk.Frame(pad,bg=C['bg2'],bd=1,relief='flat'); nepali_outer_exit.pack(fill='x',pady=(4,0))
        self.nepali_plate_exit=tk.Label(nepali_outer_exit,text="—",font=('Nirmala UI',20,'bold'),
                                         bg=C['bg2'],fg=C['orange'],relief='flat',anchor='center',pady=10)
        self.nepali_plate_exit.pack(fill='x')
        tk.Frame(pad,bg=C['orange'],height=2).pack(fill='x')

        def _on_exit_plate_change(*_):
            t=self.number_plate_exit.get().strip()
            self.nepali_plate_exit.config(text=plate_to_nepali_script(t) if t else "—")
        self.number_plate_exit.bind('<KeyRelease>',_on_exit_plate_change)

        self.detection_info_exit=tk.Label(pad,text="",font=FONT_SMALL,
                                           bg=C['bg1'],fg=C['txt1'],wraplength=400)
        self.detection_info_exit.pack(pady=(6,2))
        self._vote_label['exit']=tk.Label(pad,text="",font=('Consolas',9,'bold'),
                                           bg=C['bg1'],fg=C['yellow'],wraplength=400)
        self._vote_label['exit'].pack(pady=(0,6))

        sep(pad,pady=10)
        self._section_label(pad,"BILL PREVIEW")
        bill_card=tk.Frame(pad,bg=C['bg0'],bd=0); bill_card.pack(fill='x',pady=(6,0))
        bh=tk.Frame(bill_card,bg=C['yellow'],height=32); bh.pack(fill='x')
        tk.Label(bh,text="🧾  PARKING RECEIPT",font=('Consolas',10,'bold'),
                 bg=C['yellow'],fg=C['bg0']).pack(side='left',padx=12,pady=6)
        self.bill_rows_frame=tk.Frame(bill_card,bg=C['bg0']); self.bill_rows_frame.pack(fill='x')
        self._build_bill_placeholder()

        sep(pad,color=C['border2'],pady=14)

        # ── Gate widget ───────────────────────────────────────────────────
        gate_frame=tk.Frame(pad,bg=C['bg1'],bd=1,relief='flat'); gate_frame.pack(fill='x',pady=(0,12))
        gf_head=tk.Frame(gate_frame,bg=C['bg2']); gf_head.pack(fill='x')
        tk.Label(gf_head,text="🚧  EXIT GATE STATUS",font=('Consolas',10,'bold'),
                 bg=C['bg2'],fg=C['txt0']).pack(side='left',padx=14,pady=8)
        self.gate_widget=GateStatusWidget(gate_frame)
        self.gate_widget.pack(pady=(8,8))

        BigButton(pad,"🚪   PROCESS EXIT  &  PAY VIA eSewa",
                  command=self.process_exit,
                  bg=C['esewa'],hover=C['esewa_dk'],
                  fg=C['white'],font=('Consolas',13,'bold'),height=62).pack(fill='x',pady=(0,8))
        IconButton(pad,"✕  Clear Fields",command=self._clear_exit_fields,
                   bg=C['bg2'],hover=C['border'],fg=C['txt1'],
                   font=FONT_SMALL).pack(fill='x',pady=(0,16))

    # ── Bill helpers ──────────────────────────────────────────────────────────

    def _build_bill_placeholder(self):
        for w in self.bill_rows_frame.winfo_children(): w.destroy()
        rows=[("Vehicle","—"),("Slot","—"),("Type","—"),("Entry","—"),("Exit","—"),
              ("Duration","—"),("Rate","—"),("Smart Rate","—"),
              ("Subtotal","—"),("Min. Charge","—"),("TOTAL","—")]
        for i,(k,v) in enumerate(rows):
            bg=C['bg1'] if i%2==0 else C['bg0']
            bold=i==len(rows)-1
            row=tk.Frame(self.bill_rows_frame,bg=bg); row.pack(fill='x')
            fnt=('Consolas',11,'bold') if bold else FONT_MONO
            fg_v=C['yellow'] if bold else C['txt0']
            tk.Label(row,text=f"  {k}",font=fnt,fg=C['txt1'],bg=bg,width=14,anchor='w').pack(side='left',pady=5)
            tk.Label(row,text=v,font=fnt,fg=fg_v,bg=bg,anchor='e').pack(side='right',padx=12,pady=5)

    def _populate_bill(self,plate,data,entry,exit_t,duration,rate,raw,final,
                        min_applied=False,min_amount=0,smart_note="",grace_applied=False,slot=0):
        for w in self.bill_rows_frame.winfo_children(): w.destroy()
        min_line=f"Rs. {min_amount} (applied)" if min_applied else "N/A"
        smart_line=smart_note if smart_note else "Standard"
        rows=[
            ("Vehicle",    plate),
            ("Slot",       f"Slot {slot}" if slot else "—"),
            ("Type",       data['type']),
            ("Entry",      entry.strftime('%d %b  %H:%M:%S')),
            ("Exit",       exit_t.strftime('%d %b  %H:%M:%S')),
            ("Duration",   f"{duration:.2f} hrs"),
            ("Rate",       f"Rs. {rate}/hr"),
            ("Smart Rate", smart_line),
            ("Subtotal",   f"Rs. {raw:.2f}"),
            ("Min. Charge",min_line),
            ("TOTAL",      "FREE" if grace_applied else f"Rs. {final}"),
        ]
        for i,(k,v) in enumerate(rows):
            bg=C['bg1'] if i%2==0 else C['bg0']
            bold=i==len(rows)-1
            row=tk.Frame(self.bill_rows_frame,bg=bg); row.pack(fill='x')
            if bold: tk.Frame(self.bill_rows_frame,bg=C['yellow'],height=1).pack(fill='x',before=row)
            fg_v=(C['yellow'] if bold else
                  C['blue']   if k=="Slot" else
                  C['orange'] if i==9 and min_applied else
                  C['yellow'] if i==7 and smart_note else C['txt0'])
            fnt=('Consolas',12,'bold') if bold else FONT_MONO
            tk.Label(row,text=f"  {k}",font=fnt,fg=C['txt1'],bg=bg,width=14,anchor='w').pack(side='left',pady=6)
            tk.Label(row,text=v,font=fnt,fg=fg_v,bg=bg,anchor='e').pack(side='right',padx=12,pady=6)

    def _clear_exit_fields(self):
        self.number_plate_exit.delete(0,tk.END)
        self.nepali_plate_exit.config(text="—")
        self._auto_vtype_label_exit.config(text="")
        self.detection_info_exit.config(text="")
        if self._vote_label['exit']: self._vote_label['exit'].config(text="")
        self._build_bill_placeholder()
        self.gate_widget.set_state('closed')

    # ─────────────────────────────────────────────────────────────────────────
    # DASHBOARD TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_dashboard_tab(self):
        root_f=tk.Frame(self.dashboard_tab,bg=C['bg0'])
        root_f.pack(fill='both',expand=True,padx=16,pady=16)
        kpi_row=tk.Frame(root_f,bg=C['bg0']); kpi_row.pack(fill='x',pady=(0,14))
        self._kpi_card(kpi_row,"2-Wheeler","🏍","2w")
        self._kpi_card(kpi_row,"4-Wheeler","🚗","4w")
        self._revenue_kpi(kpi_row)
        list_row=tk.Frame(root_f,bg=C['bg0']); list_row.pack(fill='both',expand=True)
        self._vehicle_list_panel(list_row,"2W",side='left')
        self._vehicle_list_panel(list_row,"4W",side='right')
        btn_row=tk.Frame(root_f,bg=C['bg0']); btn_row.pack(fill='x',pady=(12,0))
        BigButton(btn_row,"🔄   REFRESH DASHBOARD",command=self.update_dashboard,
                  bg=C['blue'],hover=C['blue_dk'],height=40,font=FONT_BODY_B).pack(side='left')

    def _kpi_card(self,parent,title,icon,vtype):
        card_f=tk.Frame(parent,bg=C['bg1']); card_f.pack(side='left',fill='both',expand=True,padx=(0,10))
        stripe=C['blue'] if vtype=='2w' else C['purple']
        tk.Frame(card_f,bg=stripe,height=4).pack(fill='x')
        inner=tk.Frame(card_f,bg=C['bg1']); inner.pack(fill='both',padx=18,pady=14)
        head=tk.Frame(inner,bg=C['bg1']); head.pack(fill='x')
        tk.Label(head,text=icon,font=('Segoe UI',22),bg=C['bg1'],fg=stripe).pack(side='left')
        tk.Label(head,text=title,font=FONT_BODY_B,bg=C['bg1'],fg=C['txt1']).pack(side='left',padx=8)
        lbl=tk.Label(inner,text="0 / 0",font=('Consolas',32,'bold'),bg=C['bg1'],fg=stripe)
        lbl.pack(anchor='w',pady=(8,2)); setattr(self,f"{vtype}_occupied_label",lbl)
        avail_lbl=tk.Label(inner,text="— available",font=('Consolas',10,'bold'),bg=C['bg1'],fg=C['green'])
        avail_lbl.pack(anchor='w'); setattr(self,f"{vtype}_avail_label",avail_lbl)
        tk.Label(inner,text="Occupied  /  Capacity",font=FONT_SMALL,bg=C['bg1'],fg=C['txt2']).pack(anchor='w')
        pb=ttk.Progressbar(inner,orient='horizontal',length=200,mode='determinate',
                            style='Green.Horizontal.TProgressbar')
        pb.pack(fill='x',pady=(8,0)); pb['value']=0; setattr(self,f"{vtype}_progressbar",pb)
        full_lbl=tk.Label(inner,text="",font=('Consolas',11,'bold'),bg=C['bg1'],fg=C['red'])
        full_lbl.pack(anchor='w',pady=(2,0)); setattr(self,f"{vtype}_full_label",full_lbl)

    def _revenue_kpi(self,parent):
        card_f=tk.Frame(parent,bg=C['bg1']); card_f.pack(side='left',fill='both',expand=True)
        tk.Frame(card_f,bg=C['yellow'],height=4).pack(fill='x')
        inner=tk.Frame(card_f,bg=C['bg1']); inner.pack(fill='both',padx=18,pady=14)
        head=tk.Frame(inner,bg=C['bg1']); head.pack(fill='x')
        tk.Label(head,text="💰",font=('Segoe UI',22),bg=C['bg1'],fg=C['yellow']).pack(side='left')
        tk.Label(head,text="Live Revenue",font=FONT_BODY_B,bg=C['bg1'],fg=C['txt1']).pack(side='left',padx=8)
        self.revenue_label=tk.Label(inner,text="Rs. 0",font=('Consolas',32,'bold'),
                                     bg=C['bg1'],fg=C['yellow'])
        self.revenue_label.pack(anchor='w',pady=(8,2))
        tk.Label(inner,text="Accrued from active vehicles",font=FONT_SMALL,bg=C['bg1'],fg=C['txt2']).pack(anchor='w')
        self.smart_rate_lbl=tk.Label(inner,text="",font=('Segoe UI',8,'bold'),bg=C['bg1'],fg=C['yellow'])
        self.smart_rate_lbl.pack(anchor='w',pady=(4,0))

    def _vehicle_list_panel(self,parent,vtype,side):
        pf=tk.Frame(parent,bg=C['bg0'])
        pf.pack(side=side,fill='both',expand=True,padx=(0,8) if side=='left' else (8,0))
        hdr=tk.Frame(pf,bg=C['bg1'],height=40); hdr.pack(fill='x'); hdr.pack_propagate(False)
        icon="🏍" if vtype=="2W" else "🚗"
        tk.Label(hdr,text=f"{icon}  {vtype} Parked Vehicles",font=FONT_HEAD,
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=14,pady=8)
        col_hdr=tk.Frame(pf,bg=C['bg2']); col_hdr.pack(fill='x')
        for col,w in [("Plate No.",14),("Slot",6),("Duration",12),("Bill (Rs.)",10)]:
            tk.Label(col_hdr,text=col,font=FONT_SMALL,bg=C['bg2'],fg=C['txt1'],
                     width=w,anchor='w').pack(side='left',padx=6,pady=6)
        canvas=tk.Canvas(pf,bg=C['bg1'],highlightthickness=0)
        vsb=ttk.Scrollbar(pf,orient='vertical',command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side='right',fill='y'); canvas.pack(fill='both',expand=True)
        _bind_smooth_scroll(canvas)
        sf=tk.Frame(canvas,bg=C['bg1'])
        cw=canvas.create_window((0,0),window=sf,anchor='nw')
        sf.bind('<Configure>',lambda e: canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.bind('<Configure>',lambda e: canvas.itemconfig(cw,width=e.width))
        setattr(self,f"{vtype.lower()}_list_frame",sf)
        setattr(self,f"{vtype.lower()}_list_canvas",canvas)

    # ─────────────────────────────────────────────────────────────────────────
    # HISTORY TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_history_tab(self):
        outer=tk.Frame(self.history_tab,bg=C['bg0']); outer.pack(fill='both',expand=True,padx=16,pady=16)
        hdr=tk.Frame(outer,bg=C['bg1'],height=44); hdr.pack(fill='x'); hdr.pack_propagate(False)
        tk.Label(hdr,text="📋  PARKING HISTORY  &  ANALYTICS",font=FONT_HEAD,
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=16,pady=10)
        BigButton(hdr,"🔄 Refresh",command=self._refresh_history_tab,
                  bg=C['blue'],hover=C['blue_dk'],height=30,
                  font=('Segoe UI',9,'bold')).pack(side='right',padx=16,pady=7)

        # Stats row
        stats_row=tk.Frame(outer,bg=C['bg0']); stats_row.pack(fill='x',pady=(12,0))
        self._hist_total_lbl    = self._stat_chip(stats_row,"Total Records","0",C['blue'])
        self._hist_plates_lbl   = self._stat_chip(stats_row,"Unique Plates","0",C['cyan'])
        self._hist_avg_stay_lbl = self._stat_chip(stats_row,"Avg Stay","—",C['yellow'])
        self._hist_revenue_lbl  = self._stat_chip(stats_row,"Est. Revenue","Rs. 0",C['green'])

        # Search bar
        sf=tk.Frame(outer,bg=C['bg2']); sf.pack(fill='x',pady=8)
        tk.Label(sf,text="🔍",font=('Segoe UI',14),bg=C['bg2'],fg=C['txt1']).pack(side='left',padx=12,pady=8)
        self._hist_search_var=tk.StringVar()
        self._hist_search_var.trace_add('write',lambda *_: self._refresh_history_tab())
        tk.Entry(sf,textvariable=self._hist_search_var,font=FONT_BODY,
                 bg=C['bg3'],fg=C['txt0'],insertbackground=C['txt0'],
                 relief='flat',bd=0).pack(fill='x',padx=(0,16),ipady=8,pady=8)

        # Columns
        col_hdr=tk.Frame(outer,bg=C['bg3']); col_hdr.pack(fill='x')
        for col,w in [("Plate",16),("Date",14),("Duration",12),("Times Parked",14),("Avg Stay",12),("Predicted",12)]:
            tk.Label(col_hdr,text=col,font=('Consolas',9,'bold'),bg=C['bg3'],fg=C['txt1'],
                     width=w,anchor='w').pack(side='left',padx=8,pady=6)

        # Scrollable list
        canvas=tk.Canvas(outer,bg=C['bg1'],highlightthickness=0)
        vsb=ttk.Scrollbar(outer,orient='vertical',command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side='right',fill='y'); canvas.pack(fill='both',expand=True)
        _bind_smooth_scroll(canvas)
        self._hist_scroll_frame=tk.Frame(canvas,bg=C['bg1'])
        cw=canvas.create_window((0,0),window=self._hist_scroll_frame,anchor='nw')
        self._hist_scroll_frame.bind('<Configure>',lambda e: canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.bind('<Configure>',lambda e: canvas.itemconfig(cw,width=e.width))
        self._refresh_history_tab()

    def _stat_chip(self,parent,label,value,color):
        f=tk.Frame(parent,bg=C['bg1']); f.pack(side='left',padx=(0,8),fill='y')
        tk.Frame(f,bg=color,height=3).pack(fill='x')
        lbl=tk.Label(f,text=value,font=('Consolas',20,'bold'),bg=C['bg1'],fg=color)
        lbl.pack(pady=(8,0))
        tk.Label(f,text=label,font=FONT_SMALL,bg=C['bg1'],fg=C['txt2']).pack(pady=(0,8))
        return lbl

    def _refresh_history_tab(self):
        for w in self._hist_scroll_frame.winfo_children(): w.destroy()
        history=self.slot_allocator.history
        query=self._hist_search_var.get().strip().upper()
        plates=[p for p in sorted(history.keys()) if not query or query in p]

        total_records=sum(len(v) for v in history.values())
        all_stays=[e['duration_hrs'] for v in history.values() for e in v]
        avg_stay=sum(all_stays)/max(len(all_stays),1)

        self._hist_total_lbl.config(text=str(total_records))
        self._hist_plates_lbl.config(text=str(len(history)))
        self._hist_avg_stay_lbl.config(text=f"{avg_stay:.1f} hrs")

        for i,plate in enumerate(plates[:200]):
            entries=history[plate]
            last=entries[-1]
            count=len(entries)
            avg=sum(e['duration_hrs'] for e in entries)/max(count,1)
            pred=self.slot_allocator.predict_stay_hours(plate)
            is_long=pred>=LONG_STAY_THRESHOLD_HRS

            bg=C['bg1'] if i%2==0 else C['bg0']
            row=tk.Frame(self._hist_scroll_frame,bg=bg); row.pack(fill='x')
            tk.Label(row,text=plate,font=('Consolas',10,'bold'),fg=C['cyan'],bg=bg,
                     width=16,anchor='w').pack(side='left',padx=8,pady=7)
            tk.Label(row,text=last.get('date','—'),font=FONT_SMALL,fg=C['txt1'],bg=bg,
                     width=14,anchor='w').pack(side='left',padx=4)
            tk.Label(row,text=f"{last['duration_hrs']:.1f}h",font=FONT_MONO,fg=C['txt0'],bg=bg,
                     width=12,anchor='w').pack(side='left',padx=4)
            tk.Label(row,text=str(count),font=FONT_MONO,fg=C['txt0'],bg=bg,
                     width=14,anchor='w').pack(side='left',padx=4)
            tk.Label(row,text=f"{avg:.1f}h avg",font=FONT_MONO,fg=C['txt0'],bg=bg,
                     width=12,anchor='w').pack(side='left',padx=4)
            pred_color=C['purple'] if is_long else C['green']
            pred_text=f"{'Long' if is_long else 'Short'} (~{pred:.1f}h)"
            tk.Label(row,text=pred_text,font=('Consolas',9,'bold'),fg=pred_color,bg=bg,
                     width=14,anchor='w').pack(side='left',padx=4)

    # ─────────────────────────────────────────────────────────────────────────
    # SETTINGS TAB
    # ─────────────────────────────────────────────────────────────────────────

    def setup_settings_tab(self):
        outer=tk.Frame(self.settings_tab,bg=C['bg0']); outer.pack(fill='both',expand=True)
        canvas=tk.Canvas(outer,bg=C['bg0'],highlightthickness=0)
        vsb=ttk.Scrollbar(outer,orient='vertical',command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side='right',fill='y'); canvas.pack(side='left',fill='both',expand=True)
        _bind_smooth_scroll(canvas)
        sf=tk.Frame(canvas,bg=C['bg0'])
        cw=canvas.create_window((0,0),window=sf,anchor='nw')
        sf.bind('<Configure>',lambda _: canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.bind('<Configure>',lambda e: canvas.itemconfig(cw,width=e.width))

        cont=tk.Frame(sf,bg=C['bg0']); cont.pack(fill='x',padx=60,pady=40)
        tk.Label(cont,text="⚙  PARKING CONFIGURATION  —  v5",
                 font=('Consolas',18,'bold'),bg=C['bg0'],fg=C['txt0']).pack(anchor='w',pady=(0,20))

        rates_card=tk.Frame(cont,bg=C['bg1']); rates_card.pack(fill='x',pady=(0,16))
        self._settings_section(rates_card,"2W","🏍️  2-Wheeler Settings",C['blue'],0)
        tk.Frame(rates_card,bg=C['border'],height=1).pack(fill='x',padx=32,pady=8)
        self._settings_section(rates_card,"4W","🚗  4-Wheeler Settings",C['purple'],1)

        smart_card=tk.Frame(cont,bg=C['bg1']); smart_card.pack(fill='x',pady=(0,16))
        self._smart_pricing_section(smart_card)

        min_card=tk.Frame(cont,bg=C['bg1']); min_card.pack(fill='x',pady=(0,16))
        self._min_charge_section(min_card)

        # eSewa API section
        esewa_card=tk.Frame(cont,bg=C['bg1']); esewa_card.pack(fill='x',pady=(0,16))
        self._esewa_settings_section(esewa_card)

        acc_card=tk.Frame(cont,bg=C['bg1']); acc_card.pack(fill='x',pady=(0,16))
        self._account_section(acc_card)

        save_bar=tk.Frame(cont,bg=C['bg0']); save_bar.pack(fill='x',pady=(8,40))
        BigButton(save_bar,"💾   SAVE ALL CONFIGURATION",command=self.save_settings_ui,
                  bg=C['green'],hover=C['green_dk'],height=54,
                  font=('Consolas',13,'bold')).pack(fill='x')

    def _esewa_settings_section(self,parent):
        sec=tk.Frame(parent,bg=C['bg1']); sec.pack(fill='x',padx=32,pady=(20,20))
        trow=tk.Frame(sec,bg=C['bg1']); trow.pack(fill='x',pady=(0,14))
        tk.Frame(trow,bg=C['esewa'],width=4,height=24).pack(side='left')
        tk.Label(trow,text="🟢  eSewa API Settings",font=('Segoe UI',13,'bold'),
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=10)

        info=tk.Frame(sec,bg=C['bg2']); info.pack(fill='x',pady=(0,12))
        tk.Label(info,
                 text="ℹ  Test: merchant=EPAYTEST, secret=8gBm/:&EnhH.1/q  |  "
                      "Switch to 'live' and enter your merchant credentials for production.",
                 font=('Segoe UI',9,'italic'),bg=C['bg2'],fg=C['txt2'],
                 wraplength=700,justify='left').pack(anchor='w',padx=16,pady=10)

        mode_row=tk.Frame(sec,bg=C['bg1']); mode_row.pack(fill='x',pady=6)
        tk.Label(mode_row,text="Mode",font=FONT_BODY,bg=C['bg1'],fg=C['txt1'],
                 width=22,anchor='w').pack(side='left')
        self._esewa_mode_var=tk.StringVar(value=self.settings.get('esewa_mode','test'))
        for lbl,val in [("🧪  Test (EPAYTEST)","test"),("🚀  Live","live")]:
            ttk.Radiobutton(mode_row,text=lbl,variable=self._esewa_mode_var,
                            value=val).pack(side='left',padx=8)

        for fl,attr,key in [
            ("Merchant Code",   "_esewa_merchant_var", "esewa_merchant_code"),
            ("Secret Key",      "_esewa_secret_var",   "esewa_secret"),
        ]:
            row=tk.Frame(sec,bg=C['bg1']); row.pack(fill='x',pady=6)
            tk.Label(row,text=fl,font=FONT_BODY,bg=C['bg1'],fg=C['txt1'],width=22,anchor='w').pack(side='left')
            var=tk.StringVar(value=self.settings.get(key,'')); setattr(self,attr,var)
            e=tk.Entry(row,textvariable=var,font=FONT_BODY,bg=C['bg3'],fg=C['txt0'],
                       insertbackground=C['txt0'],relief='flat',bd=0,width=30)
            e.pack(side='left',ipady=6,padx=(8,0))
            tk.Frame(row,bg=C['esewa'],height=2,width=100).pack(side='left',padx=4)

        use_api_row=tk.Frame(sec,bg=C['bg1']); use_api_row.pack(fill='x',pady=(10,0))
        self._esewa_use_api_var=tk.BooleanVar(value=self.settings.get('esewa_use_api',True))
        tk.Checkbutton(use_api_row,text="  Use eSewa API (browser payment) — uncheck to use QR-only mode",
                       variable=self._esewa_use_api_var,font=FONT_BODY,
                       bg=C['bg1'],fg=C['txt0'],activebackground=C['bg1'],
                       selectcolor=C['bg3']).pack(side='left')

    def _settings_section(self,parent,vtype,title,color,idx):
        sec=tk.Frame(parent,bg=C['bg1']); sec.pack(fill='x',padx=32,pady=(24 if idx==0 else 8,8))
        trow=tk.Frame(sec,bg=C['bg1']); trow.pack(fill='x',pady=(0,16))
        tk.Frame(trow,bg=color,width=4,height=24).pack(side='left')
        tk.Label(trow,text=title,font=('Segoe UI',13,'bold'),bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=10)
        for fl,vn,key in [
            ("Total Capacity (spaces)",f"_{vtype.lower()}_capacity_var",f"{vtype.lower()}_capacity"),
            ("Hourly Rate (Rs.)",       f"_{vtype.lower()}_rate_var",    f"{vtype.lower()}_rate"),
        ]:
            row=tk.Frame(sec,bg=C['bg1']); row.pack(fill='x',pady=6)
            tk.Label(row,text=fl,font=FONT_BODY,bg=C['bg1'],fg=C['txt1'],width=26,anchor='w').pack(side='left')
            var=tk.IntVar(value=self.settings[key]); setattr(self,vn,var)
            e=tk.Entry(row,textvariable=var,font=FONT_BODY,bg=C['bg3'],fg=C['txt0'],
                       insertbackground=C['txt0'],relief='flat',bd=0,width=12)
            e.pack(side='left',ipady=6,padx=(8,0))
            tk.Frame(row,bg=color,height=2,width=120).pack(side='left',padx=4)

    def _smart_pricing_section(self,parent):
        sec=tk.Frame(parent,bg=C['bg1']); sec.pack(fill='x',padx=32,pady=(20,20))
        trow=tk.Frame(sec,bg=C['bg1']); trow.pack(fill='x',pady=(0,14))
        tk.Frame(trow,bg=C['yellow'],width=4,height=24).pack(side='left')
        tk.Label(trow,text="⚡  Smart Pricing Settings",font=('Segoe UI',13,'bold'),
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=10)
        info=tk.Frame(sec,bg=C['bg2']); info.pack(fill='x',pady=(0,12))
        tk.Label(info,text="ℹ  Weekend multiplier & peak surcharge apply on top of base rate. Grace period = free exit.",
                 font=('Segoe UI',9,'italic'),bg=C['bg2'],fg=C['txt2'],
                 wraplength=680,justify='left').pack(anchor='w',padx=16,pady=10)
        fields=[
            ("Weekend Rate Multiplier (e.g. 1.25)","_weekend_mult_var","weekend_rate_multiplier",float,1.25),
            ("Peak Surcharge % (e.g. 20)","_peak_surcharge_var","peak_surcharge_pct",int,20),
            ("Peak Threshold % (e.g. 90)","_peak_thresh_var","peak_threshold_pct",int,90),
            ("Grace Period (minutes free)","_grace_var","grace_period_minutes",int,5),
        ]
        for fl,vn,key,typ,default in fields:
            row=tk.Frame(sec,bg=C['bg1']); row.pack(fill='x',pady=6)
            tk.Label(row,text=fl,font=FONT_BODY,bg=C['bg1'],fg=C['txt1'],width=38,anchor='w').pack(side='left')
            if typ==float: var=tk.DoubleVar(value=self.settings.get(key,default))
            else:          var=tk.IntVar(value=int(self.settings.get(key,default)))
            setattr(self,vn,var)
            e=tk.Entry(row,textvariable=var,font=FONT_BODY,bg=C['bg3'],fg=C['txt0'],
                       insertbackground=C['txt0'],relief='flat',bd=0,width=14)
            e.pack(side='left',ipady=6,padx=(8,0))
            tk.Frame(row,bg=C['yellow'],height=2,width=100).pack(side='left',padx=4)

    def _min_charge_section(self,parent):
        sec=tk.Frame(parent,bg=C['bg1']); sec.pack(fill='x',padx=32,pady=(20,20))
        trow=tk.Frame(sec,bg=C['bg1']); trow.pack(fill='x',pady=(0,14))
        tk.Frame(trow,bg=C['orange'],width=4,height=24).pack(side='left')
        tk.Label(trow,text="⏱️  Minimum Charge Settings",font=('Segoe UI',13,'bold'),
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=10)
        toggle_row=tk.Frame(sec,bg=C['bg1']); toggle_row.pack(fill='x',pady=(0,10))
        self._min_charge_enabled_var=tk.BooleanVar(value=self.settings.get('min_charge_enabled',False))
        chk_frame=tk.Frame(toggle_row,bg=C['bg2'],cursor='hand2'); chk_frame.pack(side='left',fill='x')
        self._min_charge_chk=tk.Checkbutton(
            chk_frame,text="  Enable Minimum Charge",
            variable=self._min_charge_enabled_var,font=FONT_BODY,
            bg=C['bg2'],fg=C['txt0'],activebackground=C['bg2'],
            activeforeground=C['cyan'],selectcolor=C['bg3'],
            command=self._toggle_min_charge_ui)
        self._min_charge_chk.pack(padx=12,pady=10)
        self._min_charge_options_frame=tk.Frame(sec,bg=C['bg2']); self._min_charge_options_frame.pack(fill='x',pady=(0,4))
        for fl,vn,key,unit in [
            ("Time Threshold (minutes)","_min_charge_minutes_var","min_charge_minutes","min"),
            ("Minimum Charge (Rs.)",    "_min_charge_amount_var", "min_charge_amount", "Rs."),
        ]:
            row=tk.Frame(self._min_charge_options_frame,bg=C['bg2']); row.pack(fill='x',padx=16,pady=6)
            tk.Label(row,text=fl,font=FONT_BODY,bg=C['bg2'],fg=C['txt1'],width=30,anchor='w').pack(side='left')
            var=tk.IntVar(value=self.settings.get(key,30 if 'minutes' in key else 20)); setattr(self,vn,var)
            e=tk.Entry(row,textvariable=var,font=FONT_BODY,bg=C['bg3'],fg=C['txt0'],
                       insertbackground=C['txt0'],relief='flat',bd=0,width=10)
            e.pack(side='left',ipady=6,padx=(8,0))
            tk.Label(row,text=unit,font=FONT_SMALL,bg=C['bg2'],fg=C['txt2']).pack(side='left',padx=6)
        tk.Frame(self._min_charge_options_frame,bg=C['bg1'],height=10).pack()
        self._toggle_min_charge_ui()

    def _toggle_min_charge_ui(self):
        enabled=self._min_charge_enabled_var.get()
        for w in self._min_charge_options_frame.winfo_children():
            try:
                if isinstance(w,tk.Frame):
                    for ch in w.winfo_children():
                        try:
                            if isinstance(ch,tk.Entry): ch.config(state='normal' if enabled else 'disabled')
                            elif isinstance(ch,tk.Label): ch.config(fg=C['txt1'] if enabled else C['txt2'])
                        except Exception: pass
                elif isinstance(w,tk.Label): w.config(fg=C['txt1'] if enabled else C['txt2'])
            except Exception: pass

    def _account_section(self,parent):
        sec=tk.Frame(parent,bg=C['bg1']); sec.pack(fill='x',padx=32,pady=(20,20))
        trow=tk.Frame(sec,bg=C['bg1']); trow.pack(fill='x',pady=(0,16))
        tk.Frame(trow,bg=C['cyan'],width=4,height=24).pack(side='left')
        tk.Label(trow,text="🔐  Account & Login Settings",font=('Segoe UI',13,'bold'),
                 bg=C['bg1'],fg=C['txt0']).pack(side='left',padx=10)
        creds=_load_credentials()
        info_row=tk.Frame(sec,bg=C['bg2']); info_row.pack(fill='x',pady=(0,14))
        tk.Label(info_row,text=f"  Current Username:  {creds['username']}   |   Password is stored securely (hashed)",
                 font=('Segoe UI',9),bg=C['bg2'],fg=C['txt1']).pack(anchor='w',padx=12,pady=10)
        for fl,attr,show in [("New Username","_new_username_var",''),
                              ("New Password","_new_password_var",'*'),
                              ("Confirm Password","_confirm_pass_var",'*')]:
            row=tk.Frame(sec,bg=C['bg1']); row.pack(fill='x',pady=6)
            tk.Label(row,text=fl,font=FONT_BODY,bg=C['bg1'],fg=C['txt1'],width=22,anchor='w').pack(side='left')
            var=tk.StringVar(); setattr(self,attr,var)
            e=tk.Entry(row,textvariable=var,font=FONT_BODY,bg=C['bg3'],fg=C['txt0'],
                       insertbackground=C['txt0'],relief='flat',bd=0,width=22,show=show)
            e.pack(side='left',ipady=6,padx=(8,0))
            tk.Frame(row,bg=C['cyan'],height=2,width=140).pack(side='left',padx=4)
        tk.Label(sec,text="Leave fields blank to keep current credentials.",
                 font=('Segoe UI',8,'italic'),bg=C['bg1'],fg=C['txt2']).pack(anchor='w',pady=(4,0))
        IconButton(sec,"🔑  Update Credentials",command=self._update_credentials,
                   bg=C['cyan'],hover=C['blue'],fg=C['bg0'],font=FONT_BODY_B,
                   padx=20,pady=8).pack(anchor='w',pady=(14,0))

    def _update_credentials(self):
        new_user=self._new_username_var.get().strip()
        new_pass=self._new_password_var.get()
        confirm=self._confirm_pass_var.get()
        if not new_user and not new_pass: messagebox.showinfo("No Changes","No new credentials entered."); return
        creds=_load_credentials()
        if new_pass or confirm:
            if new_pass!=confirm: messagebox.showerror("Mismatch","Passwords do not match."); return
            if len(new_pass)<6: messagebox.showerror("Too Short","Password must be at least 6 characters."); return
        username=new_user if new_user else creds['username']
        password_hash=_hash_password(new_pass) if new_pass else creds['password_hash']
        _save_credentials(username,password_hash)
        for a in ("_new_username_var","_new_password_var","_confirm_pass_var"): getattr(self,a).set("")
        messagebox.showinfo("✅  Updated",f"Credentials updated.\n\nUsername: {username}")
        self.setup_settings_tab_refresh()

    def setup_settings_tab_refresh(self):
        for w in self.settings_tab.winfo_children(): w.destroy()
        self.setup_settings_tab()

    # ── Shared UI helpers ─────────────────────────────────────────────────────

    def _section_label(self,parent,text):
        tk.Label(parent,text=text,font=('Consolas',8,'bold'),
                 fg=C['txt2'],bg=parent.cget('bg'),anchor='w').pack(fill='x',pady=(6,0))

    def _info_row(self,parent,key,val):
        row=tk.Frame(parent,bg=parent.cget('bg')); row.pack(fill='x',padx=12,pady=3)
        tk.Label(row,text=key,font=FONT_SMALL,fg=C['txt1'],bg=parent.cget('bg'),
                 width=22,anchor='w').pack(side='left')
        lbl=tk.Label(row,text=val,font=('Consolas',10,'bold'),
                     fg=C['txt0'],bg=parent.cget('bg'),anchor='e')
        lbl.pack(side='right',padx=4)
        return lbl

    # ─────────────────────────────────────────────────────────────────────────
    # Camera / Video
    # ─────────────────────────────────────────────────────────────────────────

    def select_image(self,mode):
        fp=filedialog.askopenfilename(filetypes=[("Image files","*.jpg *.jpeg *.png *.bmp *.webp")])
        if fp:
            self.stop_camera(mode)
            img=cv2.imread(fp)
            if img is None: messagebox.showerror("Error",f"Could not read image:\n{fp}"); return
            if mode=='entry': self.current_frame_entry=img
            else: self.current_frame_exit=img
            self.display_frame(img,mode)
            self._set_status(f"Image loaded: {os.path.basename(fp)}",C['cyan'])
            self._auto_detect_from_frame(img.copy(),mode,source="image")

    def select_video(self,mode):
        fp=filedialog.askopenfilename(filetypes=[("Video files","*.mp4 *.avi *.mov *.mkv *.wmv")])
        if fp:
            self.stop_camera(mode)
            self._frame_count[mode]=0; self._vote_log[mode].clear()
            if self._vote_label[mode]: self._vote_label[mode].config(text="",fg=C['yellow'])
            cap=cv2.VideoCapture(fp)
            if not cap.isOpened(): messagebox.showerror("Error",f"Could not open video:\n{fp}"); return
            if mode=='entry': self.video_capture_entry=cap; self.camera_running_entry=True; self.update_video('entry')
            else: self.video_capture_exit=cap; self.camera_running_exit=True; self.update_video('exit')
            self._set_status(f"Video: {os.path.basename(fp)}",C['cyan'])

    def start_camera(self,mode):
        self.stop_camera(mode)
        self._frame_count[mode]=0; self._vote_log[mode].clear()
        if self._vote_label[mode]: self._vote_label[mode].config(text="",fg=C['yellow'])
        cap=None
        for idx in (0,1):
            c=cv2.VideoCapture(idx)
            if c.isOpened(): cap=c; break
            c.release()
        if cap is None: messagebox.showerror("Error","No webcam found."); return
        cap.set(cv2.CAP_PROP_FRAME_WIDTH,1280); cap.set(cv2.CAP_PROP_FRAME_HEIGHT,720)
        if mode=='entry':
            self.video_capture_entry=cap; self.camera_running_entry=True
            self.update_video('entry'); self._set_status("🎥 Live webcam — ENTRY",C['green'])
        else:
            self.video_capture_exit=cap; self.camera_running_exit=True
            self.update_video('exit'); self._set_status("🎥 Live webcam — EXIT",C['green'])

    def stop_camera(self,mode):
        if mode=='entry':
            self.camera_running_entry=False
            if self.video_capture_entry: self.video_capture_entry.release(); self.video_capture_entry=None
        else:
            self.camera_running_exit=False
            if self.video_capture_exit: self.video_capture_exit.release(); self.video_capture_exit=None

    def update_video(self,mode):
        running=self.camera_running_entry if mode=='entry' else self.camera_running_exit
        cap=self.video_capture_entry if mode=='entry' else self.video_capture_exit
        if not running or cap is None: return
        ret,frame=cap.read()
        if not ret:
            if cap.get(cv2.CAP_PROP_POS_FRAMES)>0:
                self.stop_camera(mode); self._set_status(f"Video finished ({mode.upper()})",C['txt1'])
            return
        if mode=='entry': self.current_frame_entry=frame
        else: self.current_frame_exit=frame
        self.display_frame(frame,mode)
        self._frame_count[mode]+=1
        if (self._frame_count[mode]%self._detect_every==0
                and not self._detecting[mode] and self.models_loaded):
            self._auto_detect_from_frame(frame.copy(),mode,source="video")
        self.root.after(33,lambda: self.update_video(mode))

    def display_frame(self,frame,mode):
        if frame is not None:
            frame=cv2.resize(frame,(640,480))
            frame=cv2.cvtColor(frame,cv2.COLOR_BGR2RGB)
            img=Image.fromarray(frame)
            imgtk=ImageTk.PhotoImage(image=img)
            lbl=self.video_label_entry if mode=='entry' else self.video_label_exit
            lbl.imgtk=imgtk; lbl.configure(image=imgtk)

    def _auto_detect_from_frame(self,frame,mode,source="video"):
        self._detecting[mode]=True
        def _run():
            try:
                plate=self.detect_number_plate(frame)
                is_good=plate and not plate.startswith('⚠')
                auto_vtype=None
                if is_good and self.models_loaded:
                    try: auto_vtype=_guess_vehicle_type_from_frame(frame,self.plate_detection_model)
                    except Exception: pass
                if is_good:
                    try:
                        crop,_=self.crop_plate_region(frame)
                        if crop is not None and crop.size>0:
                            crop_dir=os.path.join(_get_data_dir(),"plate_crops")
                            os.makedirs(crop_dir,exist_ok=True)
                            safe=re.sub(r"[^A-Za-z0-9_]","_",plate)[:30]
                            crop_path=os.path.join(crop_dir,f"{safe}.jpg")
                            cv2.imwrite(crop_path,crop)
                            self._last_plate_crop=crop_path
                    except Exception: pass

                def _update_ui():
                    info_lbl=self.detection_info_entry if mode=='entry' else self.detection_info_exit
                    plate_entry=self.number_plate_entry if mode=='entry' else self.number_plate_exit
                    nepali_lbl=self.nepali_plate_entry if mode=='entry' else self.nepali_plate_exit
                    vtype_chip=self._auto_vtype_label_entry if mode=='entry' else self._auto_vtype_label_exit
                    vote_lbl=self._vote_label[mode]

                    if is_good:
                        new_clean=plate.replace(' ','')
                        current=plate_entry.get().strip()
                        curr_clean=current.replace(' ','')
                        if source=='image' or not current or len(new_clean)>=len(curr_clean):
                            plate_entry.delete(0,tk.END); plate_entry.insert(0,plate)
                            nepali_lbl.config(text=plate_to_nepali_script(plate))
                        if auto_vtype:
                            if mode=='entry': self.vehicle_type_entry.set(auto_vtype)
                            else: self.vehicle_type_exit.set(auto_vtype)
                            vtype_chip.config(
                                text=f"🤖 AI: {'🏍 2W' if auto_vtype=='2W' else '🚗 4W'}",
                                fg=C['blue'] if auto_vtype=='2W' else C['purple'])
                        if mode=='entry':
                            vt=self.vehicle_type_entry.get()
                            rate,note=self.get_smart_rate(vt)
                            self.entry_time_label.config(text=datetime.now().strftime('%H:%M:%S'))
                            self.entry_rate_label.config(text=f"Rs. {rate}/hr")
                            self.entry_note_label.config(text=note if note else "Standard rate",
                                                          fg=C['yellow'] if note else C['txt1'])
                            self._refresh_entry_rate()
                        icon="📷" if source=="image" else "🎥"
                        info_lbl.config(
                            text=f"{icon} Detected: {plate}  {'— click REGISTER' if mode=='entry' else '— click PROCESS EXIT'}",
                            fg=C['green'])
                        self._set_status(f"{icon} Plate: {plate}  ({mode.upper()})",C['green'])
                        if source=='video':
                            now_ts=time.time()
                            log=self._vote_log[mode]
                            log[:]= [(ts,p) for ts,p in log if (now_ts-ts)<=self._VOTE_WINDOW]
                            if log and log[-1][1]!=new_clean: log.clear()
                            log.append((now_ts,new_clean))
                            vote_count=sum(1 for _,p in log if p==new_clean)
                            dots="●"*vote_count+"○"*max(0,self._VOTE_THRESHOLD-vote_count)
                            v_color=C['green'] if vote_count>=self._VOTE_THRESHOLD else C['yellow']
                            if vote_lbl: vote_lbl.config(text=f"🗳  {dots}  {vote_count}/{self._VOTE_THRESHOLD} — {plate}",fg=v_color)
                        else:
                            if vote_lbl: vote_lbl.config(text="",fg=C['yellow'])
                    else:
                        if mode=='entry': nepali_lbl.config(text="—"); vtype_chip.config(text="")
                        if source=='image':
                            info_lbl.config(text="⚠  No plate found",fg=C['yellow'])
                            self._set_status("No plate detected",C['yellow'])
                self.root.after(0,_update_ui)
            except Exception as exc: print(f"[detect-{mode}] {exc}")
            finally: self._detecting[mode]=False

        Thread(target=_run,daemon=True).start()

    # ─────────────────────────────────────────────────────────────────────────
    # ENTRY REGISTRATION  +  SLOT ASSIGNMENT
    # ─────────────────────────────────────────────────────────────────────────

    def register_entry(self):
        vtype=self.vehicle_type_entry.get()
        plate=self.number_plate_entry.get().strip()
        if not plate: messagebox.showwarning("Missing","Detect or enter the number plate first."); return

        cap_key='2w_capacity' if vtype=='2W' else '4w_capacity'
        occ_key='2w_occupied' if vtype=='2W' else '4w_occupied'
        if self.settings[occ_key]>=self.settings[cap_key]:
            messagebox.showerror("Parking Full",f"{vtype} parking is at capacity!"); return

        if plate in self.registered_vehicles:
            messagebox.showerror("Duplicate Entry", 
                f"Vehicle with plate '{plate}' is already parked in the system.\n"
                "Please check the number plate or exit the vehicle first.")
            return
        
        storage_key=plate; comment=""

        # Smart slot allocation
        cap2=self.settings.get('2w_capacity',50)
        cap4=self.settings.get('4w_capacity',30)
        slot, is_long, predicted_hrs=self.slot_allocator.allocate(plate,vtype,cap2,cap4)
        self.slot_allocator.register(storage_key,vtype,slot)

        rate,smart_note=self.get_smart_rate(vtype)
        self.settings[occ_key]+=1
        entry_time=datetime.now()
        self.registered_vehicles[storage_key]={
            'type':          vtype,
            'display_plate': plate,
            'entry_time':    entry_time.isoformat(),
            'rate':          rate,
            'smart_note':    smart_note,
            'plate_crop':    self._last_plate_crop or "",
            'slot':          slot,
            'predicted_hrs': round(predicted_hrs,2),
            'is_long_stay':  is_long,
            'comment':       comment,
        }
        self.save_vehicles(); self.save_settings()
        self._set_status(f"Registered: {storage_key}  →  Slot {slot}",C['green'])
        self.update_dashboard()

        stay_type="🔵 Long-stay" if is_long else "🟢 Short-stay"
        slot_direction="from back (farthest)" if is_long else "from front (nearest)"
        messagebox.showinfo("✅  Vehicle Registered",
            f"{'─'*40}\n  VEHICLE REGISTERED  +  SLOT ASSIGNED\n{'─'*40}\n\n"
            f"  Plate       :  {plate}\n"
            f"  Type        :  {vtype}\n"
            f"  Slot No.    :  🅿  SLOT {slot}\n"
            f"  Stay Pred.  :  {stay_type}  (~{predicted_hrs:.1f} hrs)\n"
            f"  Allocation  :  {slot_direction}\n"
            f"  Rate        :  Rs. {rate}/hr  {('('+smart_note+')') if smart_note else ''}\n"
            f"  Entry Time  :  {entry_time.strftime('%H:%M:%S')}\n\n"
            f"  Please proceed to  Slot {slot}.")

        self.number_plate_entry.delete(0,tk.END)
        self.nepali_plate_entry.config(text="—")
        self._auto_vtype_label_entry.config(text="")
        self.detection_info_entry.config(text="")
        if self._vote_label['entry']: self._vote_label['entry'].config(text="")
        self._refresh_entry_rate()

    # ─────────────────────────────────────────────────────────────────────────
    # EXIT PROCESSING
    # ─────────────────────────────────────────────────────────────────────────

    def process_exit(self):
        plate=self.number_plate_exit.get().strip()
        if not plate: messagebox.showwarning("Missing","Enter or detect number plate."); return
        if plate not in self.registered_vehicles:
            messagebox.showerror("Not Found",f"'{plate}' is not registered."); return

        data=self.registered_vehicles[plate]
        entry_t=datetime.fromisoformat(data['entry_time'])
        exit_t=datetime.now()
        grace_applied=self._is_grace_period(entry_t)
        duration=(exit_t-entry_t).total_seconds()/3600
        rate=data['rate']
        raw_bill=0 if grace_applied else duration*rate
        smart_note=data.get('smart_note','')
        slot=data.get('slot',0)

        if grace_applied:
            min_applied,min_amount,final=False,0,0
        else:
            min_applied,min_amount,final=self._apply_min_charge(duration,raw_bill)

        display=data.get('display_plate',plate)
        nepali=plate_to_nepali_script(display)

        self._populate_bill(display,data,entry_t,exit_t,duration,rate,raw_bill,final,
                            min_applied,min_amount,smart_note,grace_applied,slot)

        # Show gate CLOSED — payment required
        self.gate_widget.set_state('closed',
            "FREE EXIT — Grace period" if grace_applied else "Payment required to open gate")

        receipt_data={
            'plate':            plate,
            'display_plate':    display,
            'nepali_plate':     nepali,
            'vtype':            data['type'],
            'entry_t':          entry_t,
            'exit_t':           exit_t,
            'duration_hrs':     duration,
            'rate':             rate,
            'raw_bill':         raw_bill,
            'final_bill':       final,
            'min_applied':      min_applied,
            'min_amount':       min_amount,
            'smart_rate_note':  smart_note,
            'grace_applied':    grace_applied,
            'plate_crop_path':  data.get('plate_crop',''),
            'slot':             slot,
            'esewa_txn_id':     '',
            'payment_verified': False,
            'payment_method':   'eSewa',
        }

        def _complete_exit(txn_id="", verified=False):
            receipt_data['esewa_txn_id']     = txn_id
            receipt_data['payment_verified'] = verified
            if plate in self.registered_vehicles:
                occ_key='2w_occupied' if data['type']=='2W' else '4w_occupied'
                self.settings[occ_key]=max(0,self.settings[occ_key]-1)
                del self.registered_vehicles[plate]
                self.save_vehicles(); self.save_settings()
            # Release slot and record history
            self.slot_allocator.release(plate, duration)
            self._set_status(f"✅ Exit: {display}  —  {'FREE' if grace_applied else 'Rs.'+str(final)}",C['green'])
            self.gate_widget.set_state('open')
            self.update_dashboard()

            # Generate PDF
            try:
                pdf_path=generate_pdf_receipt(receipt_data)
                try:
                    if platform.system()=='Windows': 
                        os.startfile(pdf_path)
                    elif platform.system()=='Darwin': 
                        subprocess.Popen(['open', pdf_path])
                    else: 
                        # Try xdg-open, then fall back to opening the folder if it fails
                        try:
                            subprocess.Popen(['xdg-open', pdf_path])
                        except Exception:
                            receipts_dir = os.path.dirname(pdf_path)
                            if os.path.exists(receipts_dir):
                                subprocess.Popen(['xdg-open', receipts_dir])
                except Exception: pass
                messagebox.showinfo("✅  Exit Complete  —  Gate Open!",
                    f"🟢  GATE IS NOW OPEN\n\n"
                    f"  Vehicle  :  {display}\n"
                    f"  Slot     :  {slot}\n"
                    f"  Total    :  {'FREE' if grace_applied else 'Rs. '+str(final)}\n"
                    f"  TXN ID   :  {txn_id or '—'}\n"
                    f"  Verified :  {'✓ Yes' if verified else '⚠ Unverified'}\n\n"
                    f"  PDF receipt saved:\n  {pdf_path}\n\n"
                    f"  Have a safe journey! 🙏")
            except Exception as exc:
                messagebox.showwarning("Exit Complete",
                    f"Exit processed. PDF error: {exc}")
            # Auto-close gate after 10s
            self.root.after(10000, lambda: self.gate_widget.set_state('closed'))

        # Grace = free, no payment needed
        if grace_applied:
            _complete_exit()
            return

        # Show payment dialog
        self._show_payment_dialog(display, final, receipt_data,
                                   on_payment_complete=_complete_exit,
                                   grace=False)

    # ─────────────────────────────────────────────────────────────────────────
    # Payment Dialog  (eSewa API  +  Gate)
    # ─────────────────────────────────────────────────────────────────────────

    def _show_payment_dialog(self, plate, amount, receipt_data,
                              on_payment_complete, grace=False):
        """
        3-tab payment dialog  (eSewa API  |  Scan QR  |  Cash).
        Gate opens only when admin/staff confirms payment.
        Dialog uses direct pack — no canvas, no scroll, guaranteed visible.
        """
        EG  = C['esewa']
        EGD = C['esewa_dk']

        # ── Window ────────────────────────────────────────────────────────
        win = tk.Toplevel(self.root)
        win.title("Payment")
        win.configure(bg=C['bg1'])
        win.resizable(False, False)
        W, H = 520, 660
        win.geometry(f"{W}x{H}")
        win.update()                     # render before grab_set
        sx = (win.winfo_screenwidth()  - W) // 2
        sy = (win.winfo_screenheight() - H) // 2
        win.geometry(f"{W}x{H}+{sx}+{sy}")
        win.grab_set()

        # ── Header ────────────────────────────────────────────────────────
        hdr = tk.Frame(win, bg=EG, height=52)
        hdr.pack(fill='x')
        hdr.pack_propagate(False)
        tk.Label(hdr, text="  🟢  eSewa / CASH PAYMENT",
                 font=('Consolas', 12, 'bold'), bg=EG, fg='white',
                 anchor='w').pack(side='left', fill='y')
        tk.Label(hdr, text=f"Rs. {amount}  |  {plate}  ",
                 font=('Consolas', 11, 'bold'), bg=EG, fg='white',
                 anchor='e').pack(side='right', fill='y')

        # ── Gate status bar ───────────────────────────────────────────────
        gate_bar = tk.Label(win,
                            text="⛔   GATE CLOSED  —  Select a payment method",
                            font=('Consolas', 9, 'bold'),
                            bg=C['gate_red'], fg='white', pady=5)
        gate_bar.pack(fill='x')

        # ── Shared: open gate ─────────────────────────────────────────────
        def _open_gate(txn_id, verified):
            gate_bar.config(text="✅   PAYMENT CONFIRMED  —  GATE IS OPEN!",
                            bg=C['gate_grn'], fg='white')
            self.gate_widget.set_state('open')
            win.grab_release()
            win.destroy()
            on_payment_complete(txn_id, verified)

        def _on_close():
            if messagebox.askyesno("Close",
                    "Close without payment?\nGate will remain CLOSED."):
                win.grab_release()
                win.destroy()
                self.gate_widget.set_state('closed', 'Payment incomplete')

        win.protocol("WM_DELETE_WINDOW", _on_close)

        # ── Tab bar ───────────────────────────────────────────────────────
        tab_bar = tk.Frame(win, bg=C['bg0'], height=36)
        tab_bar.pack(fill='x')
        tab_bar.pack_propagate(False)

        content_host = tk.Frame(win, bg=C['bg1'])
        content_host.pack(fill='both', expand=True)

        TAB_LABELS = ["  💳  eSewa API  ", "  📱  Scan QR  ", "  💵  Cash  "]
        tab_panels = [tk.Frame(content_host, bg=C['bg1']) for _ in TAB_LABELS]
        tab_btns   = []

        def _show_tab(idx):
            for p in tab_panels: p.pack_forget()
            tab_panels[idx].pack(fill='both', expand=True)
            for j, b in enumerate(tab_btns):
                if j == idx:
                    b.config(bg=C['bg2'], fg=EG, font=('Segoe UI', 9, 'bold'))
                else:
                    b.config(bg=C['bg0'], fg=C['txt2'], font=('Segoe UI', 9))

        for i, lbl in enumerate(TAB_LABELS):
            b = tk.Button(tab_bar, text=lbl,
                          font=('Segoe UI', 9),
                          bg=C['bg0'], fg=C['txt2'],
                          activebackground=C['bg2'], activeforeground=EG,
                          relief='flat', bd=0, cursor='hand2',
                          command=lambda x=i: _show_tab(x))
            b.pack(side='left', fill='y', ipadx=4)
            tab_btns.append(b)

        # ════════ TAB 0 — eSewa API ═══════════════════════════════════════
        p0 = tab_panels[0]

        tk.Frame(p0, bg=C['bg1'], height=8).pack()
        ab = tk.Frame(p0, bg=C['bg2']); ab.pack(fill='x', padx=14)
        tk.Label(ab, text="Amount Due", font=('Segoe UI', 9),
                 bg=C['bg2'], fg=C['txt1']).pack(pady=(8, 0))
        tk.Label(ab, text=f"Rs. {amount}",
                 font=('Consolas', 30, 'bold'), bg=C['bg2'], fg=EG).pack()
        tk.Label(ab, text="Browser will open eSewa → gate opens automatically.",
                 font=('Segoe UI', 8), bg=C['bg2'], fg=C['txt1'],
                 wraplength=460).pack(pady=(2, 8))

        api_st = tk.Label(p0, text="", font=('Consolas', 9, 'bold'),
                          bg=C['bg1'], fg=C['yellow'], wraplength=470, pady=2)
        api_st.pack(fill='x', padx=14)

        _abref = [None]

        def _pay_api():
            self.gate_widget.set_state('waiting', 'Processing…')
            gate_bar.config(text="⏳   Opening browser…",
                            bg=C['yellow'], fg=C['bg0'])
            b = _abref[0]
            if b: b._cmd = None; b.configure(bg='#555'); b._lbl.configure(bg='#555')
            api_st.config(text="⏳  Complete payment in browser…", fg=C['yellow'])
            win.update()

            def _ok(txn, ver):
                api_st.config(text=f"✅  Confirmed  |  TXN: {txn}", fg=C['green'])
                _open_gate(txn, ver)

            def _fail(r):
                gate_bar.config(text="❌  Payment failed — try again",
                                bg=C['gate_red'], fg='white')
                api_st.config(text=f"❌  {r}", fg=C['red'])
                self.gate_widget.set_state('closed')
                b2 = _abref[0]
                if b2: b2._cmd = _pay_api; b2.configure(bg=EG); b2._lbl.configure(bg=EG)

            self._initiate_esewa_payment(plate, float(amount), _ok, _fail)

        ab2 = BigButton(p0, "💳   PAY NOW VIA eSewa API  →  OPEN GATE",
                        command=_pay_api, bg=EG, hover=EGD,
                        height=48, font=('Segoe UI', 10, 'bold'))
        ab2.pack(fill='x', padx=14, pady=6)
        _abref[0] = ab2

        tk.Label(p0, text="ℹ  No browser? Use the Scan QR or Cash tabs.",
                 font=('Segoe UI', 8, 'italic'), bg=C['bg1'], fg=C['txt2'],
                 wraplength=470).pack()

        # ════════ TAB 1 — Static QR ═══════════════════════════════════════
        p1 = tab_panels[1]

        tk.Label(p1, text="📱  Open eSewa → Scan QR → Enter amount → Pay",
                 font=('Segoe UI', 9, 'bold'), bg=C['bg1'], fg=C['txt0'],
                 pady=6).pack()

        # Side-by-side: QR image left, details right
        row1 = tk.Frame(p1, bg=C['bg1']); row1.pack(fill='x', padx=12)

        # QR image
        qlf = tk.Frame(row1, bg=C['bg1']); qlf.pack(side='left', padx=(0, 10), pady=4)
        qr_pil = _get_static_esewa_qr(size=200)
        if qr_pil is None:
            try: qr_pil = _generate_esewa_qr_image(size=200)
            except Exception: pass
        if qr_pil:
            qf2 = tk.Frame(qlf, bg='white', bd=3, relief='solid'); qf2.pack()
            _qi = ImageTk.PhotoImage(image=qr_pil)
            ql2 = tk.Label(qf2, image=_qi, bg='white', padx=3, pady=3); ql2.pack()
            ql2.image = _qi
        else:
            tk.Label(qlf, text="QR N/A", bg=C['bg1'], fg=C['yellow']).pack()

        # Details
        qrf = tk.Frame(row1, bg=C['bg1']); qrf.pack(side='left', fill='both', expand=True)
        for lt, vt, vc in [
            ("eSewa No.",  ESEWA_NUMBER,    C['cyan']),
            ("Name",       ESEWA_NAME,      C['txt0']),
            ("Plate",      plate,           C['cyan']),
        ]:
            r = tk.Frame(qrf, bg=C['bg2']); r.pack(fill='x', pady=1)
            tk.Label(r, text=f" {lt}", font=('Segoe UI', 8), fg=C['txt2'],
                     bg=C['bg2'], width=9, anchor='w').pack(side='left')
            tk.Label(r, text=f"{vt} ", font=('Consolas', 9, 'bold'),
                     fg=vc, bg=C['bg2'], anchor='e').pack(side='right')

        amt_f = tk.Frame(qrf, bg='#0a2a10'); amt_f.pack(fill='x', pady=(8, 0))
        tk.Label(amt_f, text="Enter this amount:",
                 font=('Segoe UI', 8), bg='#0a2a10', fg=C['txt1']).pack(pady=(6, 0))
        tk.Label(amt_f, text=f"Rs. {amount}",
                 font=('Consolas', 18, 'bold'), bg='#0a2a10', fg=EG).pack(pady=(0, 6))

        tk.Frame(p1, bg=C['border2'], height=1).pack(fill='x', padx=12, pady=6)
        tk.Label(p1, text="After customer pays, click to open gate:",
                 font=('Segoe UI', 8), bg=C['bg1'], fg=C['txt1']).pack()

        def _qr_confirm():
            if messagebox.askyesno("Confirm QR Payment",
                    f"Confirm Rs. {amount} paid via eSewa QR for {plate}?\nGate will open."):
                _open_gate("QR-SCAN", False)

        BigButton(p1, "✅   Customer Paid via QR  →  OPEN GATE",
                  command=_qr_confirm, bg=EG, hover=EGD,
                  height=44, font=('Segoe UI', 10, 'bold')).pack(fill='x', padx=12, pady=6)

        # ════════ TAB 2 — Cash ════════════════════════════════════════════
        p2 = tab_panels[2]

        tk.Label(p2, text="💵", font=('Segoe UI', 44),
                 bg=C['bg1'], fg=C['yellow']).pack(pady=(18, 2))
        tk.Label(p2, text="Cash Payment",
                 font=('Consolas', 13, 'bold'), bg=C['bg1'], fg=C['txt0']).pack()

        cb = tk.Frame(p2, bg=C['bg2']); cb.pack(fill='x', padx=14, pady=12)
        tk.Label(cb, text="Collect from customer:",
                 font=('Segoe UI', 9), bg=C['bg2'], fg=C['txt1']).pack(pady=(10, 0))
        tk.Label(cb, text=f"Rs. {amount}",
                 font=('Consolas', 34, 'bold'), bg=C['bg2'], fg=C['yellow']).pack()
        tk.Label(cb, text=f"Vehicle: {plate}",
                 font=('Segoe UI', 9, 'bold'), bg=C['bg2'], fg=C['txt0']).pack(pady=(0, 10))

        tk.Label(p2, text="Once cash is in hand, click below:",
                 font=('Segoe UI', 9), bg=C['bg1'], fg=C['txt1']).pack()

        def _cash_confirm():
            if messagebox.askyesno("Confirm Cash",
                    f"Rs. {amount} cash received for {plate}?\nGate will open."):
                _open_gate("CASH", False)

        BigButton(p2, "✅   Cash Received  →  OPEN GATE",
                  command=_cash_confirm,
                  bg=C['yellow'], hover=C['orange'],
                  fg=C['bg0'], height=48,
                  font=('Segoe UI', 10, 'bold')).pack(fill='x', padx=14, pady=10)

        # ── Bottom close button ───────────────────────────────────────────
        tk.Frame(win, bg=C['border2'], height=1).pack(fill='x', padx=14)
        IconButton(win, "✕  Close  (gate stays closed)",
                   command=_on_close,
                   bg=C['bg1'], hover=C['border'], fg=C['txt2'],
                   font=('Segoe UI', 8), padx=12, pady=5).pack(
                       fill='x', padx=14, pady=6)

        # Show tab 0 and force full render
        _show_tab(0)
        win.update()
        win.lift()
        win.focus_force()

    # ─────────────────────────────────────────────────────────────────────────
    # Plate detection pipeline
    # ─────────────────────────────────────────────────────────────────────────

    def detect_vehicle(self,mode):
        frame=self.current_frame_entry if mode=='entry' else self.current_frame_exit
        if frame is None: messagebox.showwarning("No Feed","Load an image, video, or webcam first."); return
        info_lbl=self.detection_info_entry if mode=='entry' else self.detection_info_exit
        if self._detecting[mode]: info_lbl.config(text="⏳  Detection already running…",fg=C['yellow']); return
        info_lbl.config(text="⏳  Detecting…",fg=C['yellow']); self.root.update_idletasks()
        self._auto_detect_from_frame(frame.copy(),mode,source="image")

    def _upscale_if_needed(self,img,min_w=200,min_h=60):
        h,w=img.shape[:2]; scale=max(min_w/max(w,1),min_h/max(h,1),1.0)
        if scale>1.0: img=cv2.resize(img,None,fx=scale,fy=scale,interpolation=cv2.INTER_CUBIC)
        return img

    def _deskew_plate(self,gray):
        edges=cv2.Canny(gray,50,150,apertureSize=3)
        lines=cv2.HoughLinesP(edges,1,np.pi/180,60,minLineLength=gray.shape[1]//4,maxLineGap=10)
        if lines is None: return gray
        angles=[]
        for line in lines:
            x1,y1,x2,y2=line[0]
            if x2!=x1: angles.append(np.degrees(np.arctan2(y2-y1,x2-x1)))
        if not angles: return gray
        med=float(np.median(angles))
        if abs(med)>15: return gray
        h,w=gray.shape[:2]; M=cv2.getRotationMatrix2D((w/2,h/2),med,1.0)
        return cv2.warpAffine(gray,M,(w,h),flags=cv2.INTER_CUBIC,borderMode=cv2.BORDER_REPLICATE)

    def _enhance_contrast(self,gray):
        return cv2.createCLAHE(clipLimit=3.0,tileGridSize=(4,4)).apply(gray)

    def crop_plate_region(self,frame):
        h,w=frame.shape[:2]; best_crop,best_conf=None,0.0
        for scale in [1.0,1.5,0.75]:
            fw=int(w*scale); fh=int(h*scale)
            probe=cv2.resize(frame,(fw,fh),interpolation=cv2.INTER_LINEAR) if scale!=1.0 else frame
            res=self.plate_detection_model(probe,verbose=False)
            if not res or len(res[0].boxes)==0: continue
            for box in res[0].boxes:
                conf=float(box.conf[0])
                if conf<=best_conf: continue
                x1,y1,x2,y2=map(int,box.xyxy[0])
                x1=int(x1/scale); y1=int(y1/scale); x2=int(x2/scale); y2=int(y2/scale)
                pad=12; x1=max(0,x1-pad); y1=max(0,y1-pad); x2=min(w,x2+pad); y2=min(h,y2+pad)
                crop=frame[y1:y2,x1:x2]
                if crop.size>0: best_crop,best_conf=crop,conf
        return best_crop,best_conf

    def preprocess_plate(self,plate_bgr):
        plate_bgr=self._upscale_if_needed(plate_bgr)
        gray=cv2.cvtColor(plate_bgr,cv2.COLOR_BGR2GRAY)
        gray=self._deskew_plate(gray); gray=self._enhance_contrast(gray)
        gray=cv2.resize(gray,None,fx=2,fy=2,interpolation=cv2.INTER_CUBIC)
        gray=cv2.bilateralFilter(gray,9,75,75)
        blurred=cv2.GaussianBlur(gray,(0,0),3)
        gray=cv2.addWeighted(gray,1.8,blurred,-0.8,0)
        gray=np.clip(gray,0,255).astype(np.uint8)
        return cv2.cvtColor(gray,cv2.COLOR_GRAY2BGR)

    def _preprocess_binarised(self,plate_bgr):
        plate_bgr=self._upscale_if_needed(plate_bgr)
        gray=cv2.cvtColor(plate_bgr,cv2.COLOR_BGR2GRAY)
        gray=self._deskew_plate(gray); gray=self._enhance_contrast(gray)
        gray=cv2.resize(gray,None,fx=2,fy=2,interpolation=cv2.INTER_CUBIC)
        gray=cv2.bilateralFilter(gray,9,75,75)
        _,binary=cv2.threshold(gray,0,255,cv2.THRESH_BINARY+cv2.THRESH_OTSU)
        return cv2.cvtColor(binary,cv2.COLOR_GRAY2BGR)

    def _preprocess_red_plate(self,plate_bgr):
        plate_bgr=self._upscale_if_needed(plate_bgr,min_w=240,min_h=70)
        b,g,r=cv2.split(plate_bgr)
        gray=np.clip(g.astype(np.int32)*140//100+b.astype(np.int32)*140//100
                     -r.astype(np.int32)*80//100,0,255).astype(np.uint8)
        gray=self._deskew_plate(gray); gray=self._enhance_contrast(gray)
        gray=cv2.resize(gray,None,fx=2,fy=2,interpolation=cv2.INTER_CUBIC)
        gray=cv2.bilateralFilter(gray,9,75,75)
        blurred=cv2.GaussianBlur(gray,(0,0),3)
        gray=cv2.addWeighted(gray,1.9,blurred,-0.9,0)
        gray=np.clip(gray,0,255).astype(np.uint8)
        return cv2.cvtColor(gray,cv2.COLOR_GRAY2BGR)

    def _detect_plate_color(self,plate_bgr):
        hsv=cv2.cvtColor(plate_bgr,cv2.COLOR_BGR2HSV)
        m1=cv2.inRange(hsv,np.array([0,100,80]),np.array([10,255,255]))
        m2=cv2.inRange(hsv,np.array([160,100,80]),np.array([180,255,255]))
        if cv2.countNonZero(m1|m2)/(plate_bgr.shape[0]*plate_bgr.shape[1])>0.15: return 'red'
        wm=cv2.inRange(hsv,np.array([0,0,180]),np.array([180,60,255]))
        if cv2.countNonZero(wm)/(plate_bgr.shape[0]*plate_bgr.shape[1])>0.30: return 'white'
        return 'unknown'

    def extract_plate_text(self,preprocessed_img):
        res=self.text_extraction_model(preprocessed_img,verbose=False)
        if not res or len(res[0].boxes)==0: return ""
        r=res[0]; chars=[]
        for box in r.boxes:
            x1,y1,x2,y2=box.xyxy[0].tolist()
            chars.append({"x":(x1+x2)/2,"y":(y1+y2)/2,"y1":y1,"y2":y2,"h":y2-y1,
                           "label":r.names[int(box.cls[0])],"conf":float(box.conf[0])})
        chars=[c for c in chars if c["conf"]>=0.18]
        if not chars: return ""

        def _iou(a,b):
            ix1=max(a['x']-a['h']*0.5,b['x']-b['h']*0.5)
            ix2=min(a['x']+a['h']*0.5,b['x']+b['h']*0.5)
            iy1=max(a['y1'],b['y1']); iy2=min(a['y2'],b['y2'])
            inter=max(0,ix2-ix1)*max(0,iy2-iy1)
            union=a['h']**2+b['h']**2-inter
            return inter/union if union>0 else 0.0

        chars.sort(key=lambda c:c['conf'],reverse=True)
        kept=[]
        for c in chars:
            if all(_iou(c,k)<0.6 for k in kept): kept.append(c)
        chars=kept; chars.sort(key=lambda c:c["y"])

        def overlap(c,row):
            ry1=min(rc["y1"] for rc in row); ry2=max(rc["y2"] for rc in row)
            ov=max(0.0,min(c["y2"],ry2)-max(c["y1"],ry1))
            sh=min(c["h"],ry2-ry1)
            return ov/sh if sh>0 else 0.0

        rows=[]
        for ch in chars:
            best_r,best_v=None,0.0
            for row in rows:
                v=overlap(ch,row)
                if v>best_v: best_v,best_r=v,row
            if best_r and best_v>=0.35: best_r.append(ch)
            else: rows.append([ch])
        rows.sort(key=lambda row: np.mean([c["y"] for c in row]))
        text=""
        for row in rows:
            row.sort(key=lambda c:c["x"])
            text+="".join(c["label"] for c in row)
        return text

    def detect_number_plate(self,frame):
        try:
            if not self.models_loaded: return "⚠  Models not loaded"
            candidates=[]
            crop,conf=self.crop_plate_region(frame)
            if crop is not None:
                plate_color=self._detect_plate_color(crop)
                preprocessors=[
                    (self.preprocess_plate,"enhanced",1.0),
                    (self._preprocess_binarised,"binary",1.0),
                    (self._preprocess_red_plate,"red_ch",1.2 if plate_color=='red' else 0.8),
                ]
                def _inv(p): return cv2.bitwise_not(self._preprocess_binarised(p))
                preprocessors.append((_inv,"inv_binary",0.9))
                for fn,lbl,weight in preprocessors:
                    try:
                        text=self.extract_plate_text(fn(crop))
                        if text: candidates.append((text,conf*weight,lbl))
                    except Exception: pass
            fh,fw=frame.shape[:2]
            scale=min(1.0,1280.0/max(fw,1))
            probe=cv2.resize(frame,(int(fw*scale),int(fh*scale)),interpolation=cv2.INTER_LINEAR) if scale<1.0 else frame
            for fn,lbl,w in [(self.preprocess_plate,"full_std",0.5),(self._preprocess_red_plate,"full_red",0.5)]:
                try:
                    text=self.extract_plate_text(fn(probe))
                    if text: candidates.append((text,0.3*w,lbl))
                except Exception: pass
            if not candidates: return "⚠  No plate detected"

            def _score(text):
                tokens=re.findall(r'[A-Z]+|\d+',text.upper()); score=0
                for i,t in enumerate(tokens[:4]):
                    if i==0 and t.isalpha() and len(t)==2: score+=2
                    elif i==1 and t.isdigit(): score+=2
                    elif i==2 and t.isalpha(): score+=2
                    elif i==3 and t.isdigit() and len(t)>=2: score+=3
                    else: score+=1
                return score

            candidates.sort(key=lambda c:(_score(c[0]),len(c[0]),c[1]),reverse=True)
            best=candidates[0][0]
            return self.format_nepali_plate(best) if best else "⚠  No text found"
        except Exception as e:
            return f"⚠  {e}"

    def format_nepali_plate(self,text):
        NEPALI_DIGITS=str.maketrans('०१२३४५६७८९','0123456789')
        OCR_FIXES={'O':'0','I':'1','S':'5','Z':'2','Q':'0','B':'8'}
        SINGLE_TO_ZONE={
            "K":"KA","KH":"KHA","G":"GA","GH":"GHA","C":"CHA","CH":"CHA",
            "J":"JA","JH":"JHA","T":"TA","TH":"THA","D":"DA","DH":"DHA",
            "N":"NA","P":"PA","PH":"PHA","BH":"BHA","M":"MA","Y":"YA",
            "R":"RA","L":"LA","W":"WA","V":"WA","S":"SA","SH":"SHA","H":"HA",
            "KA":"KA","KHA":"KHA","GA":"GA","GHA":"GHA","CHA":"CHA","JA":"JA",
            "JHA":"JHA","TA":"TA","THA":"THA","DA":"DA","DHA":"DHA","NA":"NA",
            "PA":"PA","PHA":"PHA","BHA":"BHA","MA":"MA","YA":"YA","RA":"RA",
            "LA":"LA","WA":"WA","SA":"SA","SHA":"SHA","HA":"HA",
        }
        text=text.translate(NEPALI_DIGITS)
        clean=text.replace(" ","").upper()
        tokens=re.findall(r'[A-Z]+|\d+',clean)
        if not tokens: return clean

        def _fix(s):
            r=list(s)
            for i,ch in enumerate(r):
                if ch in OCR_FIXES:
                    ld=(i>0 and r[i-1].isdigit()); rd=(i<len(r)-1 and r[i+1].isdigit())
                    if ld or rd: r[i]=OCR_FIXES[ch]
            return ''.join(r)

        clean=_fix(clean); tokens=re.findall(r'[A-Z]+|\d+',clean)
        district=series=zone=None; pending=[]
        for tok in tokens:
            if district is None: district=tok
            elif series is None and tok.isdigit(): series=tok
            elif zone is None and tok.isalpha(): zone=SINGLE_TO_ZONE.get(tok,tok)
            elif tok.isdigit(): pending.append(tok)
        number="".join(pending) if pending else None
        parts=[p for p in [district,series,zone,number] if p]
        if len(parts)>=3: return " ".join(parts)
        if len(clean)>=9: return f"{clean[:2]} {clean[2:3]} {clean[3:6]} {clean[6:]}"
        if len(clean)>=7: return f"{clean[:2]} {clean[2:3]} {clean[3:5]} {clean[5:]}"
        return clean

    # ─────────────────────────────────────────────────────────────────────────
    # Dashboard update
    # ─────────────────────────────────────────────────────────────────────────

    def update_dashboard(self):
        for vtype in ['2w','4w']:
            occ=self.settings[f'{vtype}_occupied']
            cap=self.settings[f'{vtype}_capacity']
            avail=max(0,cap-occ)
            pct=(occ/cap)*100 if cap>0 else 0

            getattr(self,f'{vtype}_occupied_label').config(text=f"{occ}  /  {cap}")
            getattr(self,f'{vtype}_avail_label').config(
                text=f"{avail} available",
                fg=(C['green'] if avail>5 else C['yellow'] if avail>0 else C['red']))

            pb=getattr(self,f'{vtype}_progressbar')
            pb['value']=min(pct,100)
            if pct>80: pb.configure(style='Red.Horizontal.TProgressbar')
            elif pct>50: pb.configure(style='Yellow.Horizontal.TProgressbar')
            else: pb.configure(style='Green.Horizontal.TProgressbar')

            full_lbl=getattr(self,f'{vtype}_full_label')
            full_lbl.config(text=f"⛔ {vtype.upper()} FULL" if avail==0 else "")

        self._update_entry_space_indicator()

        notes=[]
        if datetime.now().weekday()>=5: notes.append("🗓 Weekend rate active")
        for vt in ['2W','4W']:
            occ=self.settings[f'{vt.lower()}_occupied']
            cap=self.settings[f'{vt.lower()}_capacity']
            thresh=self.settings.get('peak_threshold_pct',90)
            if cap>0 and (occ/cap)*100>=thresh:
                notes.append(f"⚡ {vt} peak surcharge active")
        self.smart_rate_lbl.config(text="  |  ".join(notes) if notes else "Standard rates apply")

        total_revenue=0.0
        for _,data in self.registered_vehicles.items():
            try:
                entry_t=datetime.fromisoformat(data['entry_time'])
                hrs=(datetime.now()-entry_t).total_seconds()/3600
                total_revenue+=hrs*data['rate']
            except Exception: pass
        self.revenue_label.config(text=f"Rs. {total_revenue:.0f}")
        self._update_vehicle_lists()

    def _update_entry_space_indicator(self):
        try:
            vt=self.vehicle_type_entry.get()
            occ_key='2w_occupied' if vt=='2W' else '4w_occupied'
            cap_key='2w_capacity' if vt=='2W' else '4w_capacity'
            occ=self.settings.get(occ_key,0); cap=self.settings.get(cap_key,1)
            avail=max(0,cap-occ)
            self._entry_space_info.config(
                text=f"{avail} of {cap} {'2W' if vt=='2W' else '4W'} spaces free",
                fg=(C['green'] if avail>5 else C['yellow'] if avail>0 else C['red']))
            if avail==0:
                self._entry_full_lbl.config(text="⛔ FULL")
                for w in (self._register_entry_btn,self._register_entry_btn._lbl):
                    try: w.configure(bg='#3a3a3a')
                    except Exception: pass
                self._register_entry_btn._cmd=None
            else:
                self._entry_full_lbl.config(text="")
                self._register_entry_btn._cmd=self.register_entry
                for w in (self._register_entry_btn,self._register_entry_btn._lbl):
                    try: w.configure(bg=C['green'])
                    except Exception: pass
        except Exception: pass

    def _update_vehicle_lists(self):
        for vtype in ['2W','4W']:
            frame=getattr(self,f'{vtype.lower()}_list_frame')
            for w in frame.winfo_children(): w.destroy()
            vehicles={p:d for p,d in self.registered_vehicles.items() if d['type']==vtype}
            if not vehicles:
                tk.Label(frame,text="No vehicles parked",font=FONT_SMALL,
                         bg=C['bg1'],fg=C['txt2']).pack(pady=20); continue
            # Sort by slot number
            sorted_vehicles=sorted(vehicles.items(),key=lambda x: x[1].get('slot',999))
            for i,(plate,data) in enumerate(sorted_vehicles):
                bg=C['bg1'] if i%2==0 else C['bg0']
                row=tk.Frame(frame,bg=bg,cursor='hand2'); row.pack(fill='x')
                entry_t=datetime.fromisoformat(data['entry_time'])
                hrs=(datetime.now()-entry_t).total_seconds()/3600
                bill=hrs*data['rate']
                display_p=data.get('display_plate',plate)
                slot=data.get('slot',0)
                dup_tag="  ⊕" if '#' in plate else ""
                grace_warn=" 🕐" if self._is_grace_period(entry_t) else ""
                long_tag=" 🔵" if data.get('is_long_stay') else ""

                tk.Label(row,text=f"{display_p}{dup_tag}{grace_warn}",
                         font=('Consolas',10,'bold'),
                         fg=C['orange'] if dup_tag else C['cyan'],bg=bg,
                         width=14,anchor='w').pack(side='left',padx=8,pady=7)
                slot_fg=C['purple'] if data.get('is_long_stay') else C['blue']
                tk.Label(row,text=f"S{slot}{long_tag}" if slot else "—",
                         font=('Consolas',9,'bold'),fg=slot_fg,bg=bg,
                         width=6,anchor='w').pack(side='left',padx=2)
                tk.Label(row,text=f"{int(hrs)}h {int((hrs%1)*60)}m",
                         font=FONT_SMALL,fg=C['txt1'],bg=bg,
                         width=12,anchor='w').pack(side='left')
                tk.Label(row,text=f"Rs. {bill:.0f}",
                         font=('Consolas',10,'bold'),fg=C['green'],bg=bg,
                         width=10,anchor='e').pack(side='right',padx=10)

    # ─────────────────────────────────────────────────────────────────────────
    # Settings save
    # ─────────────────────────────────────────────────────────────────────────

    def save_settings_ui(self):
        try:
            cap2 = int(self._2w_capacity_var.get())
            cap4 = int(self._4w_capacity_var.get())
            rate2 = int(self._2w_rate_var.get())
            rate4 = int(self._4w_rate_var.get())
            # Sanity guards
            if not (1 <= rate2 <= 10000): raise ValueError(f"2W rate must be 1–10000, got {rate2}")
            if not (1 <= rate4 <= 10000): raise ValueError(f"4W rate must be 1–10000, got {rate4}")
            if not (1 <= cap2 <= 9999):   raise ValueError(f"2W capacity must be 1–9999")
            if not (1 <= cap4 <= 9999):   raise ValueError(f"4W capacity must be 1–9999")
        except ValueError as e:
            messagebox.showerror("Invalid Value", f"Please check your entries:\n\n{e}"); return

        self.settings['2w_capacity'] = cap2
        self.settings['4w_capacity'] = cap4
        self.settings['2w_rate']     = rate2
        self.settings['4w_rate']     = rate4
        try:
            mult = float(self._weekend_mult_var.get())
            if not (1.0 <= mult <= 5.0): raise ValueError("Weekend multiplier must be 1.0–5.0")
            self.settings['weekend_rate_multiplier'] = mult
            self.settings['peak_surcharge_pct']      = int(self._peak_surcharge_var.get())
            self.settings['peak_threshold_pct']      = int(self._peak_thresh_var.get())
            self.settings['grace_period_minutes']    = int(self._grace_var.get())
        except Exception as e:
            messagebox.showerror("Invalid", f"Smart pricing values are invalid:\n{e}"); return
        self.settings['min_charge_enabled'] = self._min_charge_enabled_var.get()
        try:
            self.settings['min_charge_amount']  = int(self._min_charge_amount_var.get())
            self.settings['min_charge_minutes'] = int(self._min_charge_minutes_var.get())
        except Exception:
            messagebox.showerror("Invalid", "Min charge values must be whole numbers."); return
        # eSewa
        self.settings['esewa_mode']          = self._esewa_mode_var.get()
        self.settings['esewa_merchant_code'] = self._esewa_merchant_var.get().strip()
        self.settings['esewa_secret']        = self._esewa_secret_var.get().strip()
        self.settings['esewa_use_api']       = self._esewa_use_api_var.get()
        self.save_settings()
        messagebox.showinfo("Saved", "✅  All configuration saved successfully.")
        self.update_dashboard()

    def round_bill(self,amount):
        last=int(amount)%10
        if last<3:   return int(amount)-last
        elif last<8: return int(amount)-last+5
        else:        return int(amount)-last+10

    # ─────────────────────────────────────────────────────────────────────────
    # Timer background thread
    # ─────────────────────────────────────────────────────────────────────────

    def start_timer_updates(self):
        def loop():
            while self.update_timers:
                try: self.root.after(0,self.update_dashboard)
                except Exception: pass
                time.sleep(30)
        Thread(target=loop,daemon=True).start()


# ─────────────────────────────────────────────────────────────────────────────

def main():
    root=tk.Tk()
    root.withdraw()
    app_instance=[None]
    def _launch():
        root.deiconify()
        app_instance[0]=ModernParkingSystem(root)
    LoginWindow(root,on_success=_launch)
    root.mainloop()

if __name__=="__main__":
    main()
                            
