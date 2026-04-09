#!/usr/bin/env python3
"""
Picture Keyworder – Komplettes Web-UI
Start: python3 keyword_stock.py [--port 8765] [--dir PATH]
"""

import argparse
import base64
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import webbrowser
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer
import socketserver
from io import BytesIO
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import urlparse, unquote
from urllib.request import urlopen, Request as URLRequest

try:
    from PIL import Image
except ImportError:
    sys.exit("Fehler: pip3 install Pillow")

try:
    import anthropic
except ImportError:
    sys.exit("Fehler: pip3 install anthropic")

# ─── Konstanten ──────────────────────────────────────────────────────────────

TARGET_KW   = 40
MAX_SIDE    = 512
API_DELAY   = 1.5
DEFAULT_PORT = 8765

MODELS = {
    "claude-sonnet-4-5": {
        "label": "Sonnet 4.5 – Empfohlen",
        "input_price": 3.0, "output_price": 15.0,
    },
    "claude-opus-4-6": {
        "label": "Opus 4.6 – Beste Qualität",
        "input_price": 15.0, "output_price": 75.0,
    },
    "claude-haiku-4-5-20251001": {
        "label": "Haiku 4.5 – Günstig",
        "input_price": 0.80, "output_price": 4.0,
    },
}
DEFAULT_MODEL = "claude-sonnet-4-5"
EST_IN  = 900    # geschätzte Input-Tokens pro Bild (768px Bild ~520 Tok + Prompt ~380 Tok)
EST_OUT = 500    # geschätzte Output-Tokens pro Bild (49 Keywords auf Englisch)

PROMPT_BASE = """Du bist ein Experte für die Verschlagwortung von Fotos für Adobe Stock, um maximale Verkäufe und Sichtbarkeit zu erzielen. Analysiere dieses Bild und gib NUR ein gültiges JSON-Objekt zurück – kein Markdown, keine Erklärung, keine Code-Blöcke.

Regeln für den Titel:
- Nur Deutsch
- Beschreibend und sachlich, fokussiert auf das Sichtbare
- Maximal 200 Zeichen
- Motiv + Kontext + Umgebung klar beschreiben
- Keine Markennamen, keine Personennamen
- Keine Sonderzeichen außer Komma, Bindestrich und Punkt
{location_title_hint}
Regeln für die Keywords:
- Nur Deutsch – dies ist entscheidend für die Auffindbarkeit auf Adobe Stock
- GENAU {target_kw} Keywords, nach Relevanz sortiert (wichtigstes zuerst)
- Die ERSTEN 7 Keywords werden von Adobe Stock am stärksten gewichtet – diese besonders sorgfältig wählen
- Keine Wörter wiederholen, die bereits im Titel verwendet wurden
- Alle zutreffenden Dimensionen abdecken:
  * Hauptmotiv und seine Eigenschaften (Farbe, Größe, Form, Textur)
  * Aktion oder Zustand (fliegend, laufend, verlassen, blühend…)
  * Stimmung und Emotion (ruhig, dramatisch, lebendig, melancholisch…)
  * Umgebung und Schauplatz (städtisch, ländlich, Innenraum, Küste…)
  * Tageszeit / Jahreszeit / Wetter (goldene Stunde, Winter, bedeckt…)
  * Fotografiestil (Vogelperspektive, Nahaufnahme, Weitwinkel, Silhouette, Langzeitbelichtung…)
  * Konzeptuelle / redaktionelle Themen (Nachhaltigkeit, Technologie, Freiheit, Isolation…)
  * Branchen-Anwendungsfälle (Reisen, Architektur, Business, Natur, Lifestyle…)
- Spezifische Begriffe mit breiten Suchbegriffen mischen, die Käufer tatsächlich verwenden
- 1–3 Wörter pro Keyword, kein Artikel (ein, eine, der, die, das), keine Satzzeichen
- Keine Markennamen, keine Personennamen
- STRENG VERBOTEN – Adobe Stock lehnt diese ab: Markennamen, eingetragene Warenzeichen, Prominentennamen, Model-/Personennamen, Firmennamen, anstößige oder obszöne Inhalte, Drogenreferenzen
{location_kw_hint}
Gib exakt diese Struktur zurück:
{{"title": "Titel hier", "keywords": ["keyword1", "keyword2", ...]}}"""

def build_prompt(location: dict = None) -> str:
    """Erstellt den Prompt, optional mit Orts-Hinweisen aus Reverse Geocoding."""
    if location:
        parts = [p for p in [location.get("suburb"), location.get("city"),
                              location.get("state")] if p]
        loc_str = ", ".join(parts)
        title_hint = f"- GPS-Standort der Aufnahme: {loc_str} – im Titel berücksichtigen\n"
        kw_hint = (f"- GPS-Standort: {loc_str} – Stadtteil und/oder Stadt als separate Keywords ergänzen "
                   f"(z. B. \"{location.get('suburb','')}\", \"{location.get('city','')}\") wenn bekannt\n")
    else:
        title_hint = ""
        kw_hint = "- Keine spezifischen Ortsnamen da kein GPS vorhanden\n"
    return PROMPT_BASE.format(
        target_kw=TARGET_KW,
        location_title_hint=title_hint,
        location_kw_hint=kw_hint,
    )

# ─── Globaler State ──────────────────────────────────────────────────────────

_dir: Path = None
_progress: dict = {}
_prog_lock = threading.Lock()
_meta_cache: dict = {}       # filename → exiftool metadata
_meta_loading = False        # True während ExifTool im Hintergrund lädt
_meta_total   = 0            # Gesamtzahl zu ladender Bilder
_meta_done    = 0            # Bereits geladene Bilder
_meta_epoch   = 0            # Zähler: erhöht sich nach jedem abgeschlossenen Ladevorgang
_jpegs_cache: list = []      # gecachte Dateiliste für aktuellen Ordner
_thumb_cache: dict = {}      # filename → JPEG bytes
_geo_cache:  dict = {}       # "lat,lon" → {city, suburb, state}

_analysis = {
    "running": False, "total": 0, "done": 0,
    "current_file": "", "log": [],
    "input_tokens": 0, "output_tokens": 0, "cost": 0.0, "error": None,
}
_ana_lock = threading.Lock()

# ─── Progress-Datei ──────────────────────────────────────────────────────────

def _prog_file() -> Path:
    return _dir / "progress.json"

def load_progress() -> dict:
    try:
        if _prog_file().exists():
            return json.loads(_prog_file().read_text("utf-8"))
    except Exception:
        pass
    return {}

def save_progress():
    tmp = _prog_file().with_suffix(".tmp")
    tmp.write_text(json.dumps(_progress, ensure_ascii=False, indent=2), "utf-8")
    os.replace(tmp, _prog_file())

def set_dir(path: Path):
    global _dir, _progress, _meta_cache, _thumb_cache, _jpegs_cache, _meta_total, _meta_done, _meta_epoch
    _dir = path
    _meta_cache.clear()
    _thumb_cache.clear()
    _jpegs_cache.clear()
    _meta_total = 0
    _meta_done  = 0
    _meta_epoch = 0
    with _prog_lock:
        _progress = load_progress()

# ─── Hilfsfunktionen ─────────────────────────────────────────────────────────

def _now() -> str:
    return datetime.now(timezone.utc).isoformat()

def _esc(s) -> str:
    return (str(s).replace("&","&amp;").replace("<","&lt;")
            .replace(">","&gt;").replace('"',"&quot;").replace("'","&#39;"))

def _jpegs() -> list:
    """Alle JPEGs direkt im gewählten Ordner (keine Unterordner, gecacht pro Ordner)."""
    global _jpegs_cache
    if not _jpegs_cache:
        _jpegs_cache = sorted(p for p in _dir.glob("*")
                              if p.suffix.lower() in (".jpg", ".jpeg") and p.is_file()
                              and not p.name.startswith("."))
    return _jpegs_cache

def _relpath(p: Path) -> str:
    """Relativer Pfad zum Stammordner, z.B. 'subfolder/image.jpg'."""
    return str(p.relative_to(_dir))

def _parse_date(filename: str, exif_dt: str) -> str:
    basename = Path(filename).name   # Unterordner-Präfix ignorieren
    if exif_dt:
        try: return exif_dt[:10].replace(":", "-")
        except Exception: pass
    try: return f"{basename[:4]}-{basename[4:6]}-{basename[6:8]}"
    except Exception: return ""

# ─── exiftool ────────────────────────────────────────────────────────────────

def find_et() -> str:
    for c in [shutil.which("exiftool"),
              str(Path.home()/"bin"/"exiftool"),
              "/usr/local/bin/exiftool",
              "/opt/homebrew/bin/exiftool"]:
        if c and Path(c).exists():
            return c
    return None

_ET_FLAGS = [
    "-IPTC:ObjectName", "-IPTC:Keywords",
    "-XMP:Title", "-XMP:Subject",
    "-GPSLatitude", "-GPSLongitude", "-GPSAltitude",
    "-GPSLatitudeRef", "-GPSLongitudeRef",
    "-EXIF:DateTimeOriginal",
    "-EXIF:Make", "-EXIF:Model",
    "-EXIF:LensModel", "-LensModel",
    "-EXIF:FocalLength", "-EXIF:FocalLengthIn35mmFormat",
    "-EXIF:FNumber", "-EXIF:ExposureTime", "-EXIF:ISO",
    "-EXIF:ExposureCompensation",
    "-EXIF:Flash", "-EXIF:MeteringMode",
    "-EXIF:ExposureProgram", "-EXIF:WhiteBalance",
    "-EXIF:Software", "-EXIF:SerialNumber",
    "-EXIF:ImageWidth", "-EXIF:ImageHeight",
    "-XMP:Rating",
    "-IPTC:City", "-IPTC:Sub-location",
    "-IPTC:Province-State",
    "-IPTC:Country-Primary-Location-Name",
    "-IPTC:CopyrightNotice", "-IPTC:Caption-Abstract",
    "-EXIF:Copyright",
    "-Composite:Megapixels",
    "-File:FileSize",
]

def read_all_meta(et: str, progress_cb=None) -> dict:
    """Liest IPTC/GPS-Metadaten für alle JPEGs in Batches (500 Bilder je Aufruf)."""
    if not et:
        return {}
    files = [str(p) for p in _jpegs()]
    if not files:
        return {}
    BATCH = 500
    result = {}
    for i in range(0, len(files), BATCH):
        batch = files[i:i + BATCH]
        try:
            r = subprocess.run(
                [et, "-json"] + _ET_FLAGS + batch,
                capture_output=True, text=True, timeout=120, encoding="utf-8")
            data = json.loads(r.stdout)
            for d in data:
                key = str(Path(d["SourceFile"]).relative_to(_dir))
                result[key] = d
        except Exception:
            pass  # Batch überspringen, nächsten versuchen
        if progress_cb:
            progress_cb(min(i + BATCH, len(files)), len(files))
    return result

def _parse_coord(val, ref="") -> float:
    """GPS-Koordinate in Dezimalgrad umwandeln."""
    if val is None:
        return None
    if isinstance(val, (int, float)):
        v = float(val)
        if str(ref).strip()[:1].upper() in ("S", "W"):
            v = -v
        return v
    s = str(val).strip()
    # DMS zuerst prüfen: "50 deg 6' 32.93\" N"
    m = re.match(r"([\d.]+)\s+deg\s+([\d.]+)[`']\s*([\d.]+)", s)
    if m:
        v = float(m[1]) + float(m[2])/60 + float(m[3])/3600
        # Richtung aus dem String selbst extrahieren (z.B. " N" am Ende)
        tail = s[m.end():].strip()
        direction = tail[0].upper() if tail else str(ref).strip()[:1].upper()
        if direction in ("S", "W"):
            v = -v
        return v
    # Dezimalgrad als Fallback
    try:
        v = float(s)
        if str(ref).strip()[:1].upper() in ("S", "W"):
            v = -v
        return v
    except ValueError:
        return None

def _fmt_gps(lat: float, lon: float, alt=None) -> dict:
    def dms(deg, pos_ch, neg_ch):
        d = int(abs(deg))
        m = int((abs(deg)-d)*60)
        s = (abs(deg)-d-m/60)*3600
        ch = pos_ch if deg >= 0 else neg_ch
        return f"{d}°{m:02d}'{s:04.1f}\"{ch}"
    alt_s = f", {float(str(alt).split()[0]):.0f} m" if alt is not None else ""
    return {
        "lat": round(lat, 6), "lon": round(lon, 6),
        "formatted": f"{dms(lat,'N','S')}, {dms(lon,'E','W')}{alt_s}",
        "maps_url": f"https://maps.apple.com/?q={lat},{lon}",
    }

def reverse_geocode(lat: float, lon: float) -> dict:
    """Ort per Nominatim ermitteln. Ergebnis wird gecacht."""
    key = f"{lat:.3f},{lon:.3f}"
    if key in _geo_cache:
        return _geo_cache[key]
    try:
        url = (f"https://nominatim.openstreetmap.org/reverse"
               f"?lat={lat}&lon={lon}&format=json&accept-language=de")
        req = URLRequest(url, headers={"User-Agent": "PictureKeyworder/1.0"})
        with urlopen(req, timeout=8) as r:
            addr = json.loads(r.read()).get("address", {})
        result = {
            "city":   addr.get("city") or addr.get("town") or addr.get("village") or "",
            "suburb": addr.get("suburb") or addr.get("neighbourhood") or addr.get("quarter") or "",
            "state":  addr.get("state") or "",
        }
    except Exception:
        result = {}
    _geo_cache[key] = result
    return result

def write_meta(image_path: Path, title: str, keywords: list, et: str) -> str:
    """Schreibt Titel + Keywords (überschreibt bestehende Felder). None = OK."""
    cmd = [et, "-overwrite_original"]
    if title:
        cmd += [f"-IPTC:ObjectName={title}", f"-XMP:Title={title}"]
    if keywords:
        for k in keywords:
            cmd += [f"-IPTC:Keywords={k}"]
        for k in keywords:
            cmd += [f"-XMP:Subject={k}"]
    if len(cmd) == 2:
        return None
    cmd.append(str(image_path))
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=30, encoding="utf-8")
        return None if r.returncode == 0 else (r.stderr.strip() or r.stdout.strip())
    except subprocess.TimeoutExpired:
        return "exiftool Timeout"
    except Exception as e:
        return str(e)

# ─── Thumbnail ───────────────────────────────────────────────────────────────

def get_thumb(image_path: Path) -> bytes:
    key = _relpath(image_path)
    if key not in _thumb_cache:
        try:
            img = Image.open(image_path).convert("RGB")
            img.thumbnail((320, 320), Image.LANCZOS)
            buf = BytesIO()
            img.save(buf, format="JPEG", quality=75)
            _thumb_cache[key] = buf.getvalue()
        except Exception:
            _thumb_cache[key] = b""
    return _thumb_cache[key]

# ─── Claude API ──────────────────────────────────────────────────────────────

def prepare_img(path: Path) -> str:
    img = Image.open(path).convert("RGB")
    w, h = img.size
    if max(w, h) > MAX_SIDE:
        r = MAX_SIDE / max(w, h)
        img = img.resize((int(w*r), int(h*r)), Image.LANCZOS)
    buf = BytesIO()
    img.save(buf, format="JPEG", quality=85)
    return base64.standard_b64encode(buf.getvalue()).decode()

def analyze(client, path: Path, model: str, location: dict = None) -> tuple:
    """→ (title, keywords, input_tokens, output_tokens)"""
    img_b64 = prepare_img(path)
    prompt  = build_prompt(location)
    total_in, total_out = 0, 0
    for attempt in range(3):
        try:
            resp = client.messages.create(
                model=model, max_tokens=1024,
                messages=[{"role":"user","content":[
                    {"type":"image","source":{"type":"base64",
                     "media_type":"image/jpeg","data":img_b64}},
                    {"type":"text","text":prompt}
                ]}])
            total_in  += resp.usage.input_tokens
            total_out += resp.usage.output_tokens
            raw = resp.content[0].text.strip()
            if raw.startswith("```"):
                raw = raw.split("```")[1]
                if raw.startswith("json"): raw = raw[4:]
            data = json.loads(raw.strip())
            title = str(data["title"]).strip()
            kws = [str(k).strip() for k in data["keywords"]]
            if len(kws) > TARGET_KW: kws = kws[:TARGET_KW]
            elif len(kws) < TARGET_KW and attempt < 2:
                raise ValueError(f"Nur {len(kws)} Keywords")
            return title, kws, total_in, total_out
        except anthropic.RateLimitError:
            time.sleep(30)
        except anthropic.APIConnectionError:
            if attempt == 2: raise
            time.sleep(2**(attempt+1))
        except (json.JSONDecodeError, KeyError, ValueError):
            if attempt == 2: raise
            time.sleep(2)
    raise RuntimeError("Alle Versuche fehlgeschlagen")

# ─── Analyse-Thread ──────────────────────────────────────────────────────────

PARALLEL_WORKERS = 3   # gleichzeitige KI-Anfragen

def run_analysis(filenames: list, model: str, api_key: str):
    global _analysis
    client = anthropic.Anthropic(api_key=api_key)
    price  = MODELS.get(model, MODELS[DEFAULT_MODEL])

    with _ana_lock:
        _analysis.update({"running":True,"total":len(filenames),"done":0,
                          "current_file":"","log":[],
                          "input_tokens":0,"output_tokens":0,"cost":0.0,"error":None})

    def process_one(fname):
        # Stopp-Check
        with _ana_lock:
            if not _analysis["running"]:
                return fname, "stopped", {}
        # Bereits analysiert → überspringen (Fortsetzung unterbrochener Analyse)
        with _prog_lock:
            if _progress.get(fname, {}).get("status") == "pending":
                return fname, "skipped", {}

        path = _dir / fname
        try:
            m = _meta_cache.get(fname, {})
            lat = _parse_coord(m.get("GPSLatitude"),  m.get("GPSLatitudeRef",  ""))
            lon = _parse_coord(m.get("GPSLongitude"), m.get("GPSLongitudeRef", ""))
            location = reverse_geocode(lat, lon) if lat and lon else None

            title, kws, in_t, out_t = analyze(client, path, model, location)
            cost = in_t/1e6*price["input_price"] + out_t/1e6*price["output_price"]
            with _prog_lock:
                if fname not in _progress: _progress[fname] = {}
                _progress[fname].update({
                    "status":"pending","title":title,"keywords":kws,
                    "input_tokens":in_t,"output_tokens":out_t,
                    "cost":cost,"timestamp":_now(),"error_msg":""})
                save_progress()
            _meta_cache.pop(fname, None)
            return fname, "ok", {"in_t":in_t,"out_t":out_t,"cost":cost,"kw_count":len(kws)}
        except Exception as e:
            with _prog_lock:
                if fname not in _progress: _progress[fname] = {}
                _progress[fname].update({"status":"error","error_msg":str(e),"timestamp":_now()})
                save_progress()
            return fname, "error", {"error":str(e)}

    with ThreadPoolExecutor(max_workers=PARALLEL_WORKERS) as executor:
        futures = {executor.submit(process_one, fn): fn for fn in filenames}
        for future in as_completed(futures):
            fname, status, data = future.result()
            with _ana_lock:
                _analysis["done"] += 1
                _analysis["current_file"] = fname
                if status == "ok":
                    _analysis["input_tokens"]  += data["in_t"]
                    _analysis["output_tokens"] += data["out_t"]
                    _analysis["cost"]          += data["cost"]
                    _analysis["log"].append({"filename":fname,"status":"ok",
                        "kw_count":data["kw_count"],"in_tokens":data["in_t"],
                        "out_tokens":data["out_t"],"cost":data["cost"]})
                elif status == "error":
                    _analysis["log"].append({"filename":fname,"status":"error",
                        "error":data.get("error","")})
                elif status == "skipped":
                    _analysis["log"].append({"filename":fname,"status":"skipped"})

    with _ana_lock:
        _analysis["running"] = False
        _analysis["current_file"] = ""

# ─── HTTP-Handler ─────────────────────────────────────────────────────────────

class ThreadedHTTPServer(socketserver.ThreadingMixIn, HTTPServer):
    daemon_threads = True

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a): pass

    def do_GET(self):
        p = urlparse(self.path).path
        if p in ("/", "/index.html"):
            self._html(build_page())
        elif p.startswith("/thumbnail/"):
            self._thumb(unquote(p[11:]))
        elif p.startswith("/preview/"):
            self._preview(unquote(p[9:]))
        elif p == "/api/images":      self._api_images()
        elif p == "/api/meta-status": self._json({"loading": _meta_loading, "cached": len(_meta_cache), "total": _meta_total, "done": _meta_done, "epoch": _meta_epoch})
        elif p == "/api/status":    self._json(_analysis_status())
        elif p == "/api/stats":     self._api_stats()
        else: self._send(404,"text/plain",b"Not found")

    def do_POST(self):
        n = int(self.headers.get("Content-Length",0))
        body = self.rfile.read(n)
        data = json.loads(body) if body else {}
        p = urlparse(self.path).path
        if   p == "/api/pick-folder":  self._api_pick()
        elif p == "/api/analyze":      self._api_analyze(data)
        elif p == "/api/stop":         self._api_stop()
        elif p == "/api/save":         self._api_save(data)
        elif p == "/api/save-all-pending": self._api_save_all_pending()
        elif p == "/api/copy-meta":    self._api_copy_meta(data)
        elif p == "/api/refresh-meta": self._api_refresh_meta()
        elif p == "/api/reset":        self._api_reset(data)
        else: self._json({"error":"Not found"},404)

    # ── Endpoints ────────────────────────────────────────────────────────────

    def _api_images(self):
        global _meta_loading, _meta_total, _meta_done
        et = find_et()
        # Metadaten im Hintergrund laden falls noch nicht vorhanden
        if not _meta_cache and not _meta_loading:
            _meta_loading = True
            _meta_total = len(_jpegs())
            _meta_done  = 0
            def _bg_load():
                global _meta_loading, _meta_done, _meta_total, _meta_epoch
                def _progress(done, total):
                    global _meta_done, _meta_total
                    _meta_done  = done
                    _meta_total = total
                try:
                    _meta_cache.update(read_all_meta(et, progress_cb=_progress))
                    _meta_epoch += 1   # signalisiert: neue Metadaten verfügbar
                finally:
                    _meta_loading = False
            threading.Thread(target=_bg_load, daemon=True).start()
        meta_snapshot = len(_meta_cache)   # Cache-Größe VOR dem Loop merken
        result = []
        for p in _jpegs():
            n = _relpath(p)             # "subfolder/image.jpg" oder "image.jpg"
            m = _meta_cache.get(n, {})
            with _prog_lock:
                prog = _progress.get(n, {})

            ex_title = m.get("ObjectName") or m.get("Title") or ""
            ex_kw = m.get("Keywords") or m.get("Subject") or []
            if isinstance(ex_kw, str): ex_kw = [ex_kw]

            lat = _parse_coord(m.get("GPSLatitude"), m.get("GPSLatitudeRef",""))
            lon = _parse_coord(m.get("GPSLongitude"), m.get("GPSLongitudeRef",""))
            gps = _fmt_gps(lat, lon, m.get("GPSAltitude")) if lat and lon else None

            result.append({
                "filename": n,
                "status":   prog.get("status","unbearbeitet"),
                "title":    prog.get("title", ex_title),
                "keywords": prog.get("keywords", ex_kw),
                "ex_title": ex_title,
                "ex_kw":    ex_kw,
                "gps":      gps,
                "date":     _parse_date(n, m.get("DateTimeOriginal","")),
                "input_tokens":  prog.get("input_tokens",0),
                "output_tokens": prog.get("output_tokens",0),
                "cost":      prog.get("cost",0.0),
                "error_msg": prog.get("error_msg",""),
                "timestamp": prog.get("timestamp",""),
                "camera":    (lambda mk,mo: (mo if mo.startswith(mk) else (mk+' '+mo).strip()) if mk and mo else (mk or mo))(str(m.get("Make","")).strip(), str(m.get("Model","")).strip()),
                "lens":      str(m.get("LensModel","")).strip(),
                "focal":     str(m.get("FocalLength","")).strip(),
                "focal35":   str(m.get("FocalLengthIn35mmFormat","")).strip(),
                "aperture":  str(m.get("FNumber","")).strip(),
                "shutter":   str(m.get("ExposureTime","")).strip(),
                "iso":       str(m.get("ISO","")).strip(),
                "ev":        str(m.get("ExposureCompensation","")).strip(),
                "flash":     str(m.get("Flash","")).strip(),
                "metering":  str(m.get("MeteringMode","")).strip(),
                "program":   str(m.get("ExposureProgram","")).strip(),
                "wb":        str(m.get("WhiteBalance","")).strip(),
                "software":  str(m.get("Software","")).strip(),
                "serial":    str(m.get("SerialNumber","")).strip(),
                "rating":    int(m.get("Rating") or 0),
                "city":      str(m.get("City","")).strip(),
                "subloc":    str(m.get("Sub-location","")).strip(),
                "state":     str(m.get("Province-State","")).strip(),
                "country":   str(m.get("Country-Primary-Location-Name",
                                        m.get("Country-PrimaryLocationName",""))).strip(),
                "copyright": str(m.get("CopyrightNotice", m.get("Copyright",""))).strip(),
                "caption":   str(m.get("Caption-Abstract","")).strip(),
                "megapixels":str(m.get("Megapixels","")).strip(),
                "width":     m.get("ImageWidth",""),
                "height":    m.get("ImageHeight",""),
                "filesize":  str(m.get("FileSize","")).strip(),
            })
        self._json(result, extra_headers={"X-Meta-Cached": str(meta_snapshot)})

    def _thumb(self, filename):
        path = _dir / filename          # relativer Pfad inkl. Unterordner
        if not path.exists() or path.suffix.lower() not in (".jpg",".jpeg"):
            self._send(404,"text/plain",b""); return
        data = get_thumb(path)
        self._send(200,"image/jpeg",data)

    def _preview(self, filename):
        path = _dir / filename          # relativer Pfad inkl. Unterordner
        if not path.exists() or path.suffix.lower() not in (".jpg", ".jpeg"):
            self._send(404, "text/plain", b""); return
        try:
            img = Image.open(path).convert("RGB")
            img.thumbnail((1400, 1000), Image.LANCZOS)
            buf = BytesIO()
            img.save(buf, format="JPEG", quality=88)
            self._send(200, "image/jpeg", buf.getvalue())
        except Exception:
            self._send(500, "text/plain", b"")

    def _api_pick(self):
        try:
            r = subprocess.run(
                ["osascript","-e",
                 'POSIX path of (choose folder with prompt "Adobe Stock Ordner wählen:")'],
                capture_output=True, text=True, timeout=60, encoding="utf-8")
            if r.returncode != 0:
                self._json({"error":"Abgebrochen"},400); return
            new = Path(r.stdout.strip())
            if not new.is_dir():
                self._json({"error":"Ungültiger Pfad"},400); return
            set_dir(new)
            self._json({"path":str(new),"name":new.name})
        except Exception as e:
            self._json({"error":str(e)},500)

    def _api_analyze(self, data):
        with _ana_lock:
            if _analysis["running"]:
                self._json({"error":"Läuft bereits"},400); return
        key = data.get("api_key","").strip() or os.environ.get("ANTHROPIC_API_KEY","")
        if not key:
            self._json({"error":"ANTHROPIC_API_KEY fehlt"},400); return
        model = data.get("model", DEFAULT_MODEL)
        fnames = data.get("filenames",[])
        if not fnames:
            self._json({"error":"Keine Bilder ausgewählt"},400); return
        threading.Thread(target=run_analysis,args=(fnames,model,key),daemon=True).start()
        self._json({"ok":True,"total":len(fnames)})

    def _api_stop(self):
        with _ana_lock: _analysis["running"] = False
        self._json({"ok":True})

    def _api_save(self, data):
        fname = data.get("filename","")
        title = str(data.get("title","")).strip()
        kws   = [str(k).strip() for k in data.get("keywords",[]) if str(k).strip()]
        path  = (_dir / fname).resolve()
        # Sicherheitscheck: Pfad muss innerhalb _dir bleiben
        try: path.relative_to(_dir.resolve())
        except ValueError: self._json({"error":"Ungültiger Pfad"},400); return
        if not path.exists():
            self._json({"error":"Datei nicht gefunden"},400); return
        et = find_et()
        if not et:
            self._json({"error":"exiftool nicht gefunden"},500); return
        err = write_meta(path, title, kws, et)
        if err:
            self._json({"error":err},500); return
        status = "unbearbeitet" if not title and not kws else "done"
        with _prog_lock:
            if fname not in _progress: _progress[fname] = {}
            _progress[fname].update({"status":status,"title":title,
                                     "keywords":kws,"timestamp":_now()})
            save_progress()
        # Metadaten-Cache für dieses Bild invalidieren
        _meta_cache.pop(fname, None)
        self._json({"ok":True})

    def _api_save_all_pending(self):
        """Alle Bilder mit status=pending direkt speichern (ohne Review)."""
        et = find_et()
        if not et:
            self._json({"error":"exiftool nicht gefunden"},500); return
        with _prog_lock:
            pending = [(fname, d.copy()) for fname, d in _progress.items()
                       if d.get("status") == "pending"]
        saved, errors = 0, []
        for fname, d in pending:
            title = str(d.get("title","")).strip()
            kws   = [str(k).strip() for k in d.get("keywords",[]) if str(k).strip()]
            try:
                path = (_dir / fname).resolve()
                path.relative_to(_dir.resolve())
                if not path.exists(): raise FileNotFoundError(fname)
                err = write_meta(path, title, kws, et)
                if err: raise RuntimeError(err)
                with _prog_lock:
                    if fname not in _progress: _progress[fname] = {}
                    _progress[fname].update({"status":"done","title":title,
                                             "keywords":kws,"timestamp":_now()})
                _meta_cache.pop(fname, None)
                saved += 1
            except Exception as ex:
                errors.append(f"{fname}: {ex}")
        save_progress()
        self._json({"ok":True,"saved":saved,"errors":errors})

    def _api_copy_meta(self, data):
        """Titel + Keywords von einem Bild auf mehrere andere übertragen."""
        source  = data.get("source", "")
        targets = data.get("targets", [])
        with _prog_lock:
            src = _progress.get(source, {})
        title = src.get("title", "")
        kws   = src.get("keywords", [])
        if not title and not kws:
            self._json({"error":"Keine Metadaten am Quellbild"},400); return
        et = find_et()
        if not et:
            self._json({"error":"exiftool nicht gefunden"},500); return
        errors = []
        for t in targets:
            try:
                path = (_dir / t).resolve()
                path.relative_to(_dir.resolve())  # Sicherheitscheck
                if not path.exists(): raise FileNotFoundError(t)
                err = write_meta(path, title, kws, et)
                if err: raise RuntimeError(err)
                with _prog_lock:
                    if t not in _progress: _progress[t] = {}
                    _progress[t].update({"status":"done","title":title,
                                         "keywords":kws,"timestamp":_now()})
                _meta_cache.pop(t, None)
            except Exception as e:
                errors.append({"file":t,"error":str(e)})
        with _prog_lock:
            save_progress()
        self._json({"ok":True,"errors":errors,"count":len(targets)-len(errors)})

    def _api_refresh_meta(self):
        _meta_cache.clear()
        self._json({"ok":True})

    def _api_reset(self, data):
        fname     = data.get("filename")
        only_errors = data.get("only_errors", False)
        with _prog_lock:
            if fname:
                _progress.pop(Path(fname).name, None)
            elif only_errors:
                errors = [k for k,v in _progress.items() if v.get("status") == "error"]
                for k in errors:
                    del _progress[k]
            else:
                _progress.clear()
            save_progress()
        _meta_cache.clear()
        self._json({"ok":True})

    def _api_stats(self):
        with _prog_lock:
            entries = list(_progress.values())
        self._json({
            "total_input":  sum(e.get("input_tokens",0)  for e in entries),
            "total_output": sum(e.get("output_tokens",0) for e in entries),
            "total_cost":   sum(e.get("cost",0.0)        for e in entries),
            "done":    sum(1 for e in entries if e.get("status")=="done"),
            "pending": sum(1 for e in entries if e.get("status")=="pending"),
            "errors":  sum(1 for e in entries if e.get("status")=="error"),
            "per_image": [
                {"filename":k,"input_tokens":v.get("input_tokens",0),
                 "output_tokens":v.get("output_tokens",0),"cost":v.get("cost",0.0),
                 "status":v.get("status","")}
                for k,v in _progress.items()
                if v.get("status","") in ("done","pending","error")
            ]
        })

    def _analysis_status(self):
        with _ana_lock:
            return dict(_analysis)

    # ── HTTP-Hilfsmethoden ───────────────────────────────────────────────────

    def _send(self, code, ct, body, extra_headers=None):
        try:
            self.send_response(code)
            self.send_header("Content-Type", ct)
            self.send_header("Content-Length", len(body))
            if extra_headers:
                for k, v in extra_headers.items():
                    self.send_header(k, v)
            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass  # Browser hat Verbindung geschlossen – harmlos

    def _json(self, data, code=200, extra_headers=None):
        self._send(code,"application/json",
                   json.dumps(data,ensure_ascii=False).encode(),
                   extra_headers=extra_headers)

    def _html(self, html: str):
        self._send(200,"text/html; charset=utf-8", html.encode("utf-8"))


def _analysis_status():
    with _ana_lock:
        return dict(_analysis)

# ─── HTML / SPA ──────────────────────────────────────────────────────────────

def build_page() -> str:
    models_js  = json.dumps(MODELS,  ensure_ascii=False)
    target_kw  = TARGET_KW
    est_in_tok = EST_IN
    est_out_tok = EST_OUT
    default_model = DEFAULT_MODEL
    folder_path  = _esc(str(_dir))
    folder_name  = _esc(_dir.name)
    env_key_set  = "true" if os.environ.get("ANTHROPIC_API_KEY") else "false"

    return f"""<!DOCTYPE html>
<html lang="de">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Picture Keyworder</title>
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='6' fill='%23212121'/%3E%3Cpath d='M6 12a2 2 0 0 1 2-2h1.5l1.8-2.5h9.4L22.5 10H24a2 2 0 0 1 2 2v10a2 2 0 0 1-2 2H8a2 2 0 0 1-2-2V12z' fill='%23455a64'/%3E%3Ccircle cx='16' cy='17' r='4.2' fill='none' stroke='%2390caf9' stroke-width='1.8'/%3E%3Ccircle cx='16' cy='17' r='2' fill='%2390caf9'/%3E%3Ccircle cx='23' cy='13' r='1' fill='%23b0bec5'/%3E%3C/svg%3E">
<style>
*{{box-sizing:border-box;margin:0;padding:0}}
:root{{
  --bg:#1a1a1a;--surface:#252525;--surface2:#2d2d2d;--border:#383838;
  --text:#e0e0e0;--muted:#888;--accent:#1976d2;--green:#2e7d32;
  --orange:#e65100;--red:#c62828;--tag-bg:#37474f;
}}
body{{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;
      background:var(--bg);color:var(--text);font-size:14px;height:100vh;
      display:flex;flex-direction:column;padding-bottom:28px}}

/* ── Header ── */
header{{background:var(--surface);border-bottom:1px solid var(--border);
        padding:10px 20px;display:flex;align-items:center;gap:12px;flex-wrap:wrap;flex-shrink:0}}
header h1{{font-size:16px;font-weight:700;color:#fff;white-space:nowrap}}
.folder-badge{{background:var(--surface2);border:1px solid var(--border);
               border-radius:6px;padding:4px 10px;font-size:12px;color:var(--muted);
               max-width:400px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.btn-folder{{background:var(--accent);color:#fff;border:none;padding:5px 12px;
             border-radius:5px;cursor:pointer;font-size:12px;white-space:nowrap}}
.btn-folder:hover{{background:#1565c0}}
.header-stats{{margin-left:auto;display:flex;gap:14px;font-size:12px;color:var(--muted)}}
.header-stats span{{white-space:nowrap}}
.hs-done{{color:#81c784}}
.hs-pend{{color:#ffb74d}}

/* ── Tabs ── */
nav{{background:var(--surface);border-bottom:1px solid var(--border);
     padding:0 20px;display:flex;gap:0;flex-shrink:0}}
.tab{{background:none;border:none;color:var(--muted);padding:11px 18px;cursor:pointer;
      font-size:13px;font-weight:500;border-bottom:2px solid transparent;transition:.15s}}
.tab:hover{{color:var(--text)}}
.tab.active{{color:#fff;border-bottom-color:var(--accent)}}

/* ── Main ── */
main{{flex:1;overflow:hidden;display:flex;flex-direction:column}}
.tab-content{{flex:1;overflow-y:auto;padding:16px 20px;display:none}}
.tab-content.active{{display:flex;flex-direction:column;gap:12px}}

/* ── Toolbar ── */
.sticky-header{{position:sticky;top:0;z-index:50;background:var(--bg)}}
.toolbar{{display:flex;gap:6px;align-items:center;flex-wrap:wrap;flex-shrink:0;
          padding:10px 0 10px;
          border-bottom:1px solid var(--border);margin-bottom:4px}}
.toolbar-group{{display:flex;gap:4px;align-items:center}}
.toolbar-label{{font-size:10px;font-weight:700;color:var(--muted);text-transform:uppercase;
                letter-spacing:.6px;padding:0 4px;white-space:nowrap}}
.toolbar-sep{{width:1px;height:20px;background:var(--border);margin:0 4px}}
.toolbar-section{{display:flex;align-items:center;gap:4px;
                  padding:4px 8px;border-radius:7px}}
.toolbar-section.section-filter{{background:rgba(255,255,255,.04);border:1px solid #2a2a2a}}
.toolbar-section.section-select{{background:rgba(25,100,180,.08);border:1px solid rgba(25,100,180,.25)}}
.filter-btn{{background:var(--surface2);border:1px solid var(--border);color:var(--muted);
             padding:4px 11px;border-radius:4px;cursor:pointer;font-size:12px;white-space:nowrap}}
.filter-btn:hover{{color:var(--text);border-color:#555}}
.filter-btn.active{{background:#2a2a2a;color:#fff;border-color:#666;font-weight:600}}
.toolbar-spacer{{flex:1}}
.btn-sm{{background:var(--surface2);border:1px solid var(--border);color:var(--text);
         padding:5px 12px;border-radius:5px;cursor:pointer;font-size:12px}}
.btn-sm:hover{{background:#333}}
.btn-primary{{background:var(--accent);border:none;color:#fff;
              padding:6px 14px;border-radius:5px;cursor:pointer;font-size:12px;font-weight:600}}
.btn-primary:hover{{background:#1565c0}}
.btn-primary:disabled{{opacity:.4;cursor:default}}
.select-count{{font-size:12px;color:var(--muted)}}

/* ── Galerie ── */
.gallery-grid{{display:grid;grid-template-columns:1fr;gap:14px}}
.card{{background:var(--surface2);border:1px solid var(--border);border-radius:10px;
       display:grid;grid-template-columns:1fr 1fr 220px;overflow:hidden;
       transition:border-color .2s;align-items:stretch}}
.card[data-status="done"]{{border-color:#2e7d32;background:rgba(0,80,0,0.4)}}
.card[data-status="pending"]{{border-color:#1565c0}}
.card[data-status="error"]{{border-color:var(--red)}}
.card.hidden{{display:none!important}}

/* Spalte 1: Bild */
.card-left{{background:#0d0d0d;display:flex;flex-direction:column;
            border-right:1px solid var(--border);position:relative}}
.card-img-wrap{{display:block;overflow:hidden}}
.card-img-wrap img{{width:100%;height:auto;display:block;cursor:zoom-in;
                    object-fit:unset}}
.card-left-footer{{display:flex;align-items:center;justify-content:space-between;
                   padding:4px 8px;gap:6px;flex-shrink:0;background:#111}}
.card-filename{{font-size:10px;color:var(--muted);text-align:center;word-break:break-all;
               width:100%;padding:0 4px}}
.card-select{{display:flex;align-items:center;gap:4px;font-size:10px;font-weight:600;
              color:#90caf9;cursor:pointer;background:#1a237e;border:1px solid #283593;
              padding:2px 7px;border-radius:10px;white-space:nowrap;transition:background .15s}}
.card-select:hover{{background:#283593}}
.card-select input{{cursor:pointer;accent-color:#64b5f6;margin:0}}
.badge{{font-size:10px;padding:2px 9px;border-radius:10px;font-weight:600;text-align:center}}
.badge-done{{background:#1b5e20;color:#a5d6a7}}
.badge-pending{{background:#0d47a1;color:#90caf9}}
.badge-unbearbeitet{{background:#333;color:#aaa}}
.badge-error{{background:#b71c1c;color:#ef9a9a}}

/* Spalte 3: Metadaten */
.card-meta{{padding:14px;display:flex;flex-direction:column;gap:7px;
            border-left:1px solid var(--border);font-size:12px}}
.card-meta.hidden{{display:none}}
.card.meta-hidden{{grid-template-columns:1fr 1fr}}
.meta-row{{display:flex;flex-direction:column;gap:2px}}
.meta-label{{font-size:10px;font-weight:700;color:#555;text-transform:uppercase;letter-spacing:.5px}}
.meta-val{{color:#9e9e9e;word-break:break-word;line-height:1.5}}
.meta-val.highlight{{color:#ddd}}
.meta-divider{{border:none;border-top:1px solid #2a2a2a;margin:4px 0}}
.gps-link{{font-size:11px;color:#64b5f6;text-decoration:none;word-break:break-word}}
.gps-link:hover{{text-decoration:underline}}
.meta-exkw{{display:flex;flex-wrap:wrap;gap:3px;margin-top:2px}}
.meta-exkw span{{background:#1e1e1e;border:1px solid #333;color:#666;
                 padding:1px 5px;border-radius:3px;font-size:10px}}

/* Spalte 3: Titel + Keywords */
.card-right{{padding:14px;display:flex;flex-direction:column;gap:8px;min-width:0}}
.field-label{{font-size:10px;font-weight:700;color:var(--muted);
              text-transform:uppercase;letter-spacing:.6px}}
.title-input{{background:#1a1a1a;border:1px solid var(--border);color:var(--text);
              padding:6px 9px;border-radius:4px;font-size:13px;width:100%}}
.title-input:focus{{outline:none;border-color:#4fc3f7}}
.title-counter{{font-size:10px}}
.kw-header{{display:flex;align-items:center;justify-content:space-between}}
.kw-counter{{font-size:11px;font-weight:700;padding:2px 7px;border-radius:10px}}
.kw-ok{{background:#1b5e20;color:#a5d6a7}}
.kw-warn{{background:var(--orange);color:#ffcc80}}
.tags{{background:#1a1a1a;border:1px solid var(--border);border-radius:4px;
       padding:6px;display:flex;flex-wrap:wrap;gap:4px;min-height:32px;
       max-height:120px;overflow-y:auto}}
.tag{{background:var(--tag-bg);color:#b0bec5;padding:3px 6px 3px 8px;border-radius:3px;
      font-size:11px;display:flex;align-items:center;gap:3px;transition:opacity .15s}}
.tag[draggable]{{cursor:grab}}
.tag[draggable]:active{{cursor:grabbing}}
.tag.dragging{{opacity:.35;cursor:grabbing}}
.tag.drop-left{{box-shadow:-3px 0 0 #4fc3f7;border-radius:0 4px 4px 0}}
.tag.drop-right{{box-shadow:3px 0 0 #4fc3f7;border-radius:4px 0 0 4px}}
.tag-x{{background:none;border:none;color:#78909c;cursor:pointer;font-size:13px;
         line-height:1;padding:0}}
.tag-x:hover{{color:#ef9a9a}}
.add-row{{display:flex;gap:6px}}
.kw-input{{flex:1;background:#1a1a1a;border:1px solid var(--border);color:var(--text);
           padding:5px 8px;border-radius:4px;font-size:12px}}
.kw-input:focus{{outline:none;border-color:#4fc3f7}}
.kw-input::placeholder{{color:#555}}
.btn-add{{background:var(--accent);color:#fff;border:none;padding:5px 10px;
          border-radius:4px;cursor:pointer;font-size:14px;tabindex:-1}}
.btn-add:hover{{background:#1565c0}}
.card-footer{{display:flex;align-items:center;gap:6px;margin-top:auto;padding-top:6px}}
.btn-save{{background:var(--green);color:#fff;border:none;padding:7px 10px;
           border-radius:4px;cursor:pointer;font-size:12px;font-weight:600;width:100%}}
.btn-save:hover{{background:#388e3c}}
.error-msg{{font-size:12px;color:#ef9a9a;background:rgba(198,40,40,.12);
            border:1px solid var(--red);border-radius:4px;padding:5px 9px}}

/* ── Datumsfilter ── */
.date-filter-bar{{display:none;align-items:center;gap:8px;padding:5px 14px;
                  background:#1a1a1a;border-bottom:1px solid var(--border);flex-wrap:wrap}}
.date-filter-bar.open{{display:flex}}
.df-select{{background:#111;border:1px solid var(--border);color:var(--text);
            padding:4px 8px;border-radius:5px;font-size:12px;cursor:pointer;
            color-scheme:dark}}
.df-select:focus{{outline:none;border-color:#555}}
.df-select:disabled{{opacity:.35;cursor:default}}
.df-active{{border-color:#4fc3f7!important}}
.df-clear{{background:none;border:1px solid #444;color:#888;padding:4px 10px;
           border-radius:5px;font-size:12px;cursor:pointer}}
.df-clear:hover{{color:#fff;border-color:#666}}
.df-count{{font-size:11px;color:var(--muted)}}
.btn-filter-toggle{{background:var(--surface2);border:1px solid var(--border);color:var(--muted);
                    padding:5px 10px;border-radius:5px;cursor:pointer;font-size:12px}}
.btn-filter-toggle:hover{{color:var(--text);border-color:#555}}
.btn-filter-toggle.active{{border-color:#4fc3f7;color:#4fc3f7}}
.rating-bar{{display:none;align-items:center;gap:6px;padding:5px 14px;
             background:#1a1a1a;border-bottom:1px solid var(--border)}}
.rating-bar.open{{display:flex}}
.rating-btn{{background:none;border:1px solid #333;color:#888;padding:3px 10px;
             border-radius:5px;font-size:13px;cursor:pointer;white-space:nowrap}}
.rating-btn:hover{{border-color:#666;color:#ffd700}}
.rating-btn.active{{border-color:#ffd700;color:#ffd700;background:#1a1500}}
.meta-rating{{color:#ffd700;font-size:13px;letter-spacing:1px}}
.folder-filter-bar{{display:none;align-items:center;gap:6px;padding:5px 14px;
                    background:#1a1a1a;border-bottom:1px solid var(--border);flex-wrap:wrap}}
.folder-filter-bar.open{{display:flex}}
.folder-btn{{background:none;border:1px solid #333;color:#aaa;padding:3px 10px;
             border-radius:5px;font-size:12px;cursor:pointer;white-space:nowrap}}
.folder-btn:hover{{border-color:#666;color:#fff}}
.folder-btn.active{{border-color:#4fc3f7;color:#4fc3f7;background:rgba(79,195,247,.08)}}
.folder-btn .folder-count{{font-size:10px;color:var(--muted);margin-left:4px}}
/* ── KI-Analyse ── */
.analyse-layout{{display:grid;grid-template-columns:320px 1fr;gap:16px;flex:1}}
.analyse-config{{background:var(--surface2);border:1px solid var(--border);
                 border-radius:10px;padding:16px;display:flex;flex-direction:column;
                 gap:14px;align-self:start}}
.analyse-config h2{{font-size:14px;font-weight:600}}
.form-row{{display:flex;flex-direction:column;gap:5px}}
.form-label{{font-size:11px;color:var(--muted);font-weight:600;text-transform:uppercase}}
select, .key-input{{background:#1a1a1a;border:1px solid var(--border);color:var(--text);
                    padding:6px 9px;border-radius:5px;font-size:13px;width:100%}}
select:focus, .key-input:focus{{outline:none;border-color:#555}}
.cost-box{{background:#1a1a1a;border:1px solid var(--border);border-radius:6px;
           padding:10px;font-size:12px;line-height:1.8;color:var(--muted)}}
.cost-box strong{{color:var(--text);font-size:15px}}
.sel-count{{font-size:13px;font-weight:600;color:var(--text)}}
.sel-count span{{color:#ffb74d}}
.btn-start{{background:#2e7d32;color:#fff;border:none;padding:9px;border-radius:6px;
            cursor:pointer;font-size:13px;font-weight:700;width:100%}}
.btn-start:hover{{background:#388e3c}}
.btn-start:disabled{{opacity:.4;cursor:default}}
.btn-stop{{background:#b71c1c;color:#fff;border:none;padding:7px;border-radius:6px;
           cursor:pointer;font-size:12px;width:100%;display:none}}
.btn-stop:hover{{background:#c62828}}

.analyse-log-panel{{background:var(--surface2);border:1px solid var(--border);
                    border-radius:10px;padding:16px;display:flex;flex-direction:column;gap:10px}}
.analyse-log-panel h2{{font-size:14px;font-weight:600}}
.prog-bar-wrap{{background:#333;border-radius:4px;height:8px}}
.prog-fill{{background:#4caf50;height:8px;border-radius:4px;transition:width .4s;width:0%}}
.prog-text{{font-size:12px;color:var(--muted)}}
.log-area{{flex:1;overflow-y:auto;max-height:500px;display:flex;flex-direction:column;gap:4px}}
.log-item{{font-size:12px;padding:5px 8px;border-radius:4px;background:#1a1a1a;
           display:flex;justify-content:space-between;gap:8px}}
.log-ok{{border-left:3px solid #4caf50}}
.log-err{{border-left:3px solid var(--red);color:#ef9a9a}}
.log-run{{border-left:3px solid #ffb74d;animation:pulse 1s infinite}}
@keyframes pulse{{0%,100%{{opacity:1}}50%{{opacity:.5}}}}
.log-cost{{color:var(--muted);white-space:nowrap}}

/* ── Auswertung ── */
.stats-cards{{display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:12px}}
.stat-card{{background:var(--surface2);border:1px solid var(--border);border-radius:8px;
            padding:14px}}
.stat-card .label{{font-size:11px;color:var(--muted);text-transform:uppercase;
                   font-weight:600;letter-spacing:.5px}}
.stat-card .value{{font-size:26px;font-weight:700;color:#fff;margin-top:4px}}
.stat-card .sub{{font-size:11px;color:var(--muted);margin-top:2px}}
.stats-table{{width:100%;border-collapse:collapse;font-size:12px;margin-top:4px}}
.stats-table th{{background:#333;padding:7px 10px;text-align:left;font-weight:600;
                 font-size:11px;color:var(--muted);text-transform:uppercase}}
.stats-table td{{padding:7px 10px;border-bottom:1px solid var(--border)}}
.stats-table tr:hover td{{background:#222}}
.empty-state{{color:var(--muted);font-size:13px;padding:40px;text-align:center}}

/* ── Toast ── */
.toast{{position:fixed;bottom:60px;right:20px;background:#333;color:#fff;
        padding:9px 16px;border-radius:7px;font-size:13px;z-index:999;
        display:none;box-shadow:0 4px 12px rgba(0,0,0,.4);max-width:400px}}
/* ── Statusbar ── */
#statusbar{{position:fixed;bottom:0;left:0;right:0;height:26px;
            background:#222;border-top:1px solid #383838;
            display:flex;align-items:center;padding:0 14px;gap:8px;
            font-size:12px;color:#9e9e9e;z-index:900;user-select:none}}
#statusbar .sb-dot{{width:8px;height:8px;border-radius:50%;background:#555;flex-shrink:0}}
#statusbar .sb-dot.active{{background:#66bb6a;box-shadow:0 0 7px #66bb6a99;
  animation:sbpulse 1s ease-in-out infinite}}
@keyframes sbpulse{{0%,100%{{opacity:1}}50%{{opacity:.25}}}}
#statusbar .sb-text{{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:#bdbdbd}}
#statusbar .sb-right{{margin-left:auto;color:#666;font-size:11px;white-space:nowrap}}
/* Bild-Ladeindikator */
.rv-imgwrap .img-status{{position:absolute;color:#666;font-size:13px;pointer-events:none}}
.rv-imgwrap{{position:relative}}
/* ── Warn-Dialog ── */
.warn-modal{{position:fixed;inset:0;z-index:2000;display:flex;align-items:center;justify-content:center}}
.warn-modal.hidden{{display:none!important}}
.warn-overlay{{position:absolute;inset:0;background:rgba(0,0,0,.72);cursor:pointer}}
.warn-dialog{{position:relative;z-index:1;background:var(--surface2);border-radius:10px;
             padding:20px;width:440px;max-width:92vw;box-shadow:0 8px 32px rgba(0,0,0,.6)}}
.warn-title{{font-weight:700;font-size:13px;margin-bottom:10px;color:var(--text)}}
.warn-list{{background:#1a1a1a;border:1px solid var(--border);border-radius:5px;padding:8px 10px;
           font-size:12px;color:var(--muted);max-height:130px;overflow-y:auto;margin-bottom:14px}}
.warn-list li{{list-style:none;padding:2px 0}}
.warn-btns{{display:flex;gap:8px;justify-content:flex-end;flex-wrap:wrap}}
.btn-wcancel{{background:none;border:1px solid var(--border);color:var(--muted);padding:7px 14px;
             border-radius:6px;font-size:13px;cursor:pointer}}
.btn-wcancel:hover{{color:var(--text)}}
.btn-wskip{{background:var(--surface);border:1px solid var(--border);color:var(--text);
           padding:7px 14px;border-radius:6px;font-size:13px;cursor:pointer;font-weight:600}}
.btn-wskip:hover{{background:#2a2a2a}}
.btn-wall{{background:#1565c0;color:#fff;border:none;padding:7px 14px;
          border-radius:6px;font-size:13px;cursor:pointer;font-weight:600}}
.btn-wall:hover{{background:#1976d2}}
/* ── Review-Modal ── */
.btn-review{{background:#1565c0;color:#fff;border:none;padding:5px 14px;border-radius:5px;
            cursor:pointer;font-size:12px;font-weight:600;display:none}}
.btn-review:hover{{background:#1976d2}}
.card-left img{{cursor:zoom-in}}
.rv-gps{{font-size:11px;color:var(--muted)}}
.rv-gps a{{color:#4da6ff;text-decoration:none}}
.rv-gps a:hover{{text-decoration:underline}}
.title-counter{{font-size:11px;color:var(--muted);margin-top:2px}}
.title-counter.warn{{color:#ff9800}}
/* ── Transfer-Modal ── */
.transfer-modal{{position:fixed;inset:0;z-index:2100;display:flex;align-items:center;justify-content:center}}
.transfer-modal.hidden{{display:none!important}}
.transfer-overlay{{position:absolute;inset:0;background:rgba(0,0,0,.75);cursor:pointer}}
.transfer-dialog{{position:relative;z-index:1;background:var(--surface2);border-radius:12px;
                 width:680px;max-width:96vw;max-height:85vh;display:flex;flex-direction:column;
                 overflow:hidden;box-shadow:0 8px 40px rgba(0,0,0,.7)}}
.transfer-head{{padding:14px 16px;border-bottom:1px solid var(--border);display:flex;align-items:center;gap:8px}}
.transfer-head strong{{flex:1;font-size:14px}}
.transfer-actions{{padding:8px 12px;display:flex;gap:6px;border-bottom:1px solid var(--border)}}
.transfer-list{{overflow-y:auto;flex:1;padding:12px;
                display:grid;grid-template-columns:repeat(auto-fill,minmax(140px,1fr));gap:8px}}
.transfer-item{{display:flex;flex-direction:column;gap:4px;padding:6px;border-radius:8px;
               cursor:pointer;border:2px solid transparent;transition:.15s}}
.transfer-item:hover{{border-color:#444}}
.transfer-item.selected{{border-color:#1976d2;background:rgba(25,118,210,0.18)}}
.transfer-item img{{width:100%;aspect-ratio:4/3;object-fit:cover;border-radius:4px;display:block}}
.transfer-item-name{{font-size:10px;color:var(--muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.transfer-foot{{padding:10px 14px;border-top:1px solid var(--border);display:flex;justify-content:flex-end;gap:8px}}
.review-modal{{position:fixed;inset:0;z-index:1000;display:flex;align-items:center;justify-content:center}}
.review-modal.hidden{{display:none!important}}
.review-overlay{{position:absolute;inset:0;background:rgba(0,0,0,.82)}}
.review-dialog{{position:relative;z-index:1;background:var(--surface2);border-radius:12px;
               display:flex;flex-direction:column;width:92vw;max-width:1120px;
               max-height:93vh;overflow:hidden;box-shadow:0 8px 40px rgba(0,0,0,.7)}}
.rv-header{{display:flex;align-items:center;padding:11px 16px;border-bottom:1px solid var(--border);gap:10px;flex-shrink:0}}
.rv-hcount{{font-weight:700;font-size:13px;min-width:60px}}
.rv-hname{{flex:1;font-size:12px;color:var(--muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.rv-hclose{{background:none;border:none;color:var(--muted);font-size:20px;cursor:pointer;line-height:1;padding:0 6px;border-radius:4px}}
.rv-hclose:hover{{color:var(--text);background:var(--surface)}}
.rv-body{{display:flex;flex:1;min-height:0}}
.rv-imgwrap{{flex:1;background:#0c0c0c;display:flex;align-items:center;justify-content:center;overflow:hidden}}
.rv-imgwrap img{{max-width:100%;max-height:100%;object-fit:contain;display:block}}
.rv-fields{{flex:0 0 340px;padding:14px;display:flex;flex-direction:column;gap:10px;overflow-y:auto;border-left:1px solid var(--border)}}
.rv-fields.hidden{{display:none}}
.rv-footer{{display:flex;align-items:center;gap:8px;padding:10px 14px;border-top:1px solid var(--border);flex-shrink:0}}
.btn-rnav{{background:var(--surface);border:1px solid var(--border);color:var(--text);padding:7px 14px;border-radius:6px;font-size:13px;cursor:pointer}}
.btn-rnav:hover{{background:#2a2a2a}}
.btn-rnav:disabled,.btn-rskip:disabled{{opacity:.35;cursor:default;pointer-events:none}}
.btn-rskip{{background:none;border:1px solid var(--border);color:var(--muted);padding:7px 14px;border-radius:6px;font-size:13px;cursor:pointer}}
.btn-rskip:hover{{color:var(--text);border-color:#555}}
.btn-rsave{{margin-left:auto;background:#1565c0;color:#fff;border:none;padding:8px 22px;border-radius:6px;font-size:13px;font-weight:700;cursor:pointer}}
.btn-rsave:hover{{background:#1976d2}}
</style>
</head>
<body>

<header>
  <h1>Picture Keyworder</h1>
  <div class="folder-badge" id="folder-path" title="{folder_path}">{folder_path}</div>
  <button class="btn-folder" onclick="pickFolder()">Ordner wählen</button>
  <div class="header-stats" id="header-stats"></div>
</header>

<nav>
  <button class="tab active" onclick="showTab('gallery')">Galerie</button>
  <button class="tab" onclick="showTab('analysis')">KI-Keywords</button>
  <button class="tab" onclick="showTab('stats')">Auswertung</button>
</nav>

<main>
  <!-- Galerie -->
  <div id="tab-gallery" class="tab-content active">
    <div class="sticky-header">
    <div class="toolbar">
      <div class="toolbar-section section-filter">
        <span class="toolbar-label">Anzeigen</span>
        <div class="toolbar-group">
          <button class="filter-btn active" onclick="setFilter('all',this)" title="Alle Bilder anzeigen">Alle Bilder</button>
          <button class="filter-btn" onclick="setFilter('ohne',this)" title="Bilder ohne gespeicherte Keywords">Ohne Keywords</button>
          <button class="filter-btn" onclick="setFilter('mit',this)" title="Bilder mit gespeicherten Keywords">Mit Keywords</button>
        </div>
      </div>
      <div class="toolbar-section section-select">
        <span class="toolbar-label">Auswahl</span>
        <div class="toolbar-group">
          <button class="btn-sm" onclick="selectAll()" title="Alle Bilder für KI-Analyse auswählen">&#x2611; Alle</button>
          <button class="btn-sm" onclick="selectNone()" title="Auswahl aufheben">&#x2610; Keine</button>
          <button class="btn-sm" onclick="select100()" title="Genau 100 sichtbare Bilder auswählen (von oben)">&#x2611; 100</button>
          <button class="btn-sm" onclick="selectUnprocessed()" title="Nur neue (noch nicht analysierte) Bilder auswählen">&#x25CB; Nur Neue</button>
          <button class="btn-sm" style="color:#ef9a9a" onclick="resetErrors()" title="Fehlgeschlagene Bilder zurücksetzen und erneut analysierbar machen">&#x21BA; Fehler reset</button>
        </div>
      </div>
      <div class="toolbar-spacer"></div>
      <button class="btn-filter-toggle" id="btn-meta-toggle" onclick="toggleMetaCols()" title="Metadaten-Spalte ein-/ausblenden">&#x1F4CB; Metadaten</button>
      <button class="btn-filter-toggle" id="btn-rating-toggle" onclick="toggleRatingFilter()" title="Nach Lightroom-Bewertung filtern">&#x2B50; Rating</button>
      <button class="btn-filter-toggle" id="btn-date-toggle" onclick="toggleDateFilter()" title="Datumsfilter ein-/ausblenden">&#x1F4C5; Datum</button>
      <button class="btn-filter-toggle" id="btn-folder-toggle" onclick="toggleFolderFilter()" title="Nach Unterordner filtern" style="display:none">&#x1F4C1; Ordner</button>
      <span class="select-count" id="sel-count">0 ausgew&#xE4;hlt</span>
      <button class="btn-review" id="btn-review-gallery" onclick="openReview()" title="KI-Vorschl&#xE4;ge Bild f&#xFC;r Bild pr&#xFC;fen und speichern">&#x2713; Vorschl&#xE4;ge pr&#xFC;fen</button>
      <button class="btn-primary" onclick="goAnalysis()" title="Ausgew&#xE4;hlte Bilder mit KI analysieren und Keywords generieren">&#x2728; Keywords generieren &#x203A;</button>
    </div>
    <div class="rating-bar" id="rating-bar">
      <span class="toolbar-label">Min. Rating</span>
      <button class="rating-btn active" onclick="setRatingFilter(0,this)">Alle</button>
      <button class="rating-btn" onclick="setRatingFilter(1,this)">&#x2605;1+</button>
      <button class="rating-btn" onclick="setRatingFilter(2,this)">&#x2605;&#x2605;2+</button>
      <button class="rating-btn" onclick="setRatingFilter(3,this)">&#x2605;&#x2605;&#x2605;3+</button>
      <button class="rating-btn" onclick="setRatingFilter(4,this)">&#x2605;&#x2605;&#x2605;&#x2605;4+</button>
      <button class="rating-btn" onclick="setRatingFilter(5,this)">&#x2605;&#x2605;&#x2605;&#x2605;&#x2605;5</button>
    </div>
    <div class="date-filter-bar" id="date-filter-bar">
      <span class="toolbar-label">Datum</span>
      <select class="df-select" id="df-year" onchange="dfYearChange()"><option value="">Alle Jahre</option></select>
      <select class="df-select" id="df-month" onchange="dfMonthChange()"><option value="">Alle Monate</option></select>
      <select class="df-select" id="df-day" onchange="applyAllFilters()"><option value="">Alle Tage</option></select>
      <button class="df-clear" id="df-clear-btn" onclick="clearDateFilter()" style="display:none">&#x2715; Zur&#xFC;cksetzen</button>
      <span class="df-count" id="df-count"></span>
    </div>
    <div class="folder-filter-bar" id="folder-filter-bar">
      <span class="toolbar-label">Ordner</span>
      <div id="folder-btns" style="display:contents"></div>
      <button class="df-clear" id="folder-clear-btn" onclick="clearFolderFilter()" style="display:none">&#x2715; Zur&#xFC;cksetzen</button>
      <span class="df-count" id="folder-count"></span>
    </div>
    </div><!-- /sticky-header -->
    <div class="gallery-grid" id="gallery-grid">
      <div class="empty-state" id="gallery-empty">Bilder werden geladen…</div>
    </div>
  </div>

  <!-- KI-Analyse -->
  <div id="tab-analysis" class="tab-content">
    <div class="analyse-layout">
      <div class="analyse-config">
        <h2>KI-Keywords</h2>
        <div class="form-row">
          <div class="form-label">Ausgewählte Bilder</div>
          <div class="sel-count">
            <span id="ana-count">0</span> Bilder ausgewählt
          </div>
        </div>
        <div class="form-row">
          <label class="form-label" for="model-sel">Modell</label>
          <select id="model-sel" onchange="updateCost()">
          </select>
        </div>
        <div class="cost-box" id="cost-box">
          Bitte Bilder in der Galerie auswählen.
        </div>
        <div class="form-row">
          <label class="form-label" for="api-key">Anthropic API Key</label>
          <input class="key-input" id="api-key" type="password"
                 placeholder="sk-ant-api03-..."
                 value="">
          <div style="font-size:10px;color:var(--muted);margin-top:3px">
            {"API Key aus Umgebungsvariable geladen." if {env_key_set} else "Leer lassen wenn ANTHROPIC_API_KEY gesetzt ist."}
          </div>
        </div>
        <button class="btn-start" id="btn-start" onclick="startAnalysis()">
          ▶ Keywords generieren
        </button>
        <button class="btn-stop" id="btn-stop" onclick="stopAnalysis()">
          ■ Stoppen
        </button>
        <button class="btn-review" id="btn-review-ana" onclick="openReview()" style="width:100%;margin-top:4px">
          ▶ Review starten
        </button>
        <button class="btn-sm" onclick="saveAllPending()" style="width:100%;margin-top:4px;background:#1b5e20;color:#fff" title="Ausgewählte Bilder analysieren und Keywords ohne Review direkt speichern">
          &#x1F4BE; Analysieren &amp; direkt speichern
        </button>
      </div>

      <div class="analyse-log-panel">
        <h2>Fortschritt</h2>
        <div class="prog-bar-wrap">
          <div class="prog-fill" id="prog-fill"></div>
        </div>
        <div class="prog-text" id="prog-text">Bereit.</div>
        <div class="log-area" id="log-area">
          <div class="empty-state">Noch keine Analyse gestartet.</div>
        </div>
      </div>
    </div>
  </div>

  <!-- Auswertung -->
  <div id="tab-stats" class="tab-content">
    <div class="stats-cards" id="stats-cards"></div>
    <div style="margin-top:16px;font-size:13px;font-weight:600;color:var(--muted)">
      Aufschlüsselung pro Bild
    </div>
    <table class="stats-table">
      <thead><tr>
        <th>Dateiname</th><th>Status</th>
        <th>Input Tokens</th><th>Output Tokens</th><th>Kosten (USD)</th>
      </tr></thead>
      <tbody id="stats-tbody"></tbody>
    </table>
  </div>
</main>

<div class="toast" id="toast"></div>
<div id="statusbar">
  <div class="sb-dot" id="sb-dot"></div>
  <div class="sb-text" id="sb-text">Bereit</div>
  <div class="sb-right" id="sb-right"></div>
</div>

<script>
const MODELS = {models_js};
const TARGET_KW = {target_kw};
const EST_IN = {est_in_tok};
const EST_OUT = {est_out_tok};
const DEFAULT_MODEL = "{default_model}";
const ENV_KEY_SET = {env_key_set};

let allImages = [];
let selected = new Set();
let currentFilter = 'all';
let pollTimer = null;
let _excludedFolders = new Set();
let _allFolders = [];

// ── Init ──────────────────────────────────────────────────────────────────

document.addEventListener('DOMContentLoaded', () => {{
  // Modell-Dropdown befüllen
  const sel = document.getElementById('model-sel');
  for (const [id, m] of Object.entries(MODELS)) {{
    const opt = document.createElement('option');
    opt.value = id; opt.textContent = m.label;
    if (id === DEFAULT_MODEL) opt.selected = true;
    sel.appendChild(opt);
  }}
  loadImages();
}});

// ── Tabs ──────────────────────────────────────────────────────────────────

function showTab(name) {{
  document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
  document.querySelectorAll('.tab').forEach(el => el.classList.remove('active'));
  document.getElementById('tab-' + name).classList.add('active');
  event.target.classList.add('active');
  if (name === 'stats') loadStats();
  if (name === 'analysis') updateCost();
}}

// ── Galerie laden ─────────────────────────────────────────────────────────

let _metaPollTimer = null;

async function loadImages() {{
  const grid = document.getElementById('gallery-grid');
  document.getElementById('gallery-empty').style.display = '';
  sbSet('Lade Bilder…', true);
  try {{
    const res = await fetch('/api/images');
    const metaCachedAtFetch = parseInt(res.headers.get('X-Meta-Cached') || '0');
    allImages = await res.json();
    if (metaCachedAtFetch > 0) {{
      renderGallery();
      updateHeaderStats();
      _rvUpdateButtons();
      document.getElementById('gallery-empty').style.display = 'none';
    }}
    // Prüfen ob ExifTool-Metadaten noch geladen werden
    // Metadaten-Status prüfen
    const ms = await fetch('/api/meta-status').then(r=>r.json()).catch(()=>({{epoch:0}}));
    const epochAtFetch = ms.epoch || 0;

    if (metaCachedAtFetch > 0 && !ms.loading) {{
      // Warm-Cache: Metadaten waren schon beim Abruf vorhanden – fertig
      buildDateFilter(); buildFolderFilter();
      sbIdle(allImages.length + ' Bilder geladen');
    }} else {{
      // Cold-Start: Bilder kamen ohne Metadaten – pollen bis Epoch sich ändert
      if (_metaPollTimer) clearInterval(_metaPollTimer);
      if (ms.loading) {{
        const msg = 'Metadaten werden geladen… ' + (ms.done||0) + ' / ' + (ms.total||allImages.length);
        sbSet(msg, true);
        document.getElementById('gallery-empty').textContent = msg;
      }} else {{
        sbSet('Metadaten werden geladen…', true);
        document.getElementById('gallery-empty').textContent = 'Metadaten werden geladen…';
      }}
      _metaPollTimer = setInterval(async () => {{
        const s = await fetch('/api/meta-status').then(r=>r.json()).catch(()=>({{epoch:epochAtFetch}}));
        if (s.loading) {{
          const msg = 'Metadaten werden geladen… ' + (s.done||0) + ' / ' + (s.total||allImages.length);
          sbSet(msg, true);
          document.getElementById('gallery-empty').textContent = msg;
        }} else if ((s.epoch || 0) > epochAtFetch) {{
          // Epoch gestiegen → neue Metadaten vorhanden → Galerie neu laden
          clearInterval(_metaPollTimer); _metaPollTimer = null;
          await loadImages();
        }} else {{
          // ExifTool nicht verfügbar oder fehlgeschlagen → trotzdem rendern
          clearInterval(_metaPollTimer); _metaPollTimer = null;
          renderGallery();
          updateHeaderStats();
          _rvUpdateButtons();
          document.getElementById('gallery-empty').style.display = 'none';
          buildDateFilter(); buildFolderFilter();
          sbIdle(allImages.length + ' Bilder geladen (keine Metadaten)');
        }}
      }}, 600);
    }}
  }} catch(e) {{
    document.getElementById('gallery-empty').textContent = 'Fehler beim Laden: ' + e;
  }}
}}

function renderGallery() {{
  const grid = document.getElementById('gallery-grid');
  const existing = {{}};
  grid.querySelectorAll('.card').forEach(c => existing[c.dataset.filename] = c);

  // Unbearbeitete + Fehler zuerst, KI-Vorschläge in der Mitte, Übernommene ans Ende
  const statusOrder = {{'unbearbeitet': 0, 'error': 1, 'pending': 2, 'done': 3}};
  const sorted = [...allImages].sort((a, b) =>
    (statusOrder[a.status] ?? 0) - (statusOrder[b.status] ?? 0)
  );

  sorted.forEach(img => {{
    const card = existing[img.filename]
      ? (updateCard(existing[img.filename], img), existing[img.filename])
      : createCard(img);
    grid.appendChild(card); // verschiebt bestehende Knoten, hängt neue an
  }});
  applyFilter(currentFilter);
  updateSelCount();
}}

function metaRow(label, value, highlight) {{
  if (!value) return null;
  const row = document.createElement('div');
  row.className = 'meta-row';
  const l = document.createElement('div'); l.className = 'meta-label'; l.textContent = label;
  const v = document.createElement('div'); v.className = 'meta-val' + (highlight ? ' highlight' : ''); v.textContent = value;
  row.appendChild(l); row.appendChild(v);
  return row;
}}

function createCard(img) {{
  const card = document.createElement('div');
  card.className = 'card';
  card.dataset.filename  = img.filename;
  card.dataset.status    = img.status;
  card.dataset.timestamp = img.timestamp || '';
  card.dataset.date      = img.date || '';
  card.dataset.rating    = img.rating || 0;
  card.dataset.folder    = img.filename.includes('/') ? img.filename.substring(0, img.filename.lastIndexOf('/')) : '';

  // ── Spalte 1: Bild ──────────────────────────────────────────────────────
  const left = document.createElement('div');
  left.className = 'card-left';

  // Bild-Bereich (wächst)
  const imgWrap = document.createElement('div');
  imgWrap.className = 'card-img-wrap';
  const thumb = document.createElement('img');
  thumb.src = '/thumbnail/' + encodeURIComponent(img.filename);
  thumb.alt = img.filename;
  thumb.loading = 'lazy';
  thumb.addEventListener('click', e => {{ e.stopPropagation(); openGalleryView(img.filename); }});
  imgWrap.appendChild(thumb);
  left.appendChild(imgWrap);

  // Footer: Dateiname + Badge + Checkbox
  const leftFooter = document.createElement('div');
  leftFooter.className = 'card-left-footer';

  const fn = document.createElement('div');
  fn.className = 'card-filename';
  fn.style.cssText = 'flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap';
  fn.textContent = img.filename.split('/').pop();
  leftFooter.appendChild(fn);

  const badge = document.createElement('span');
  badge.className = 'badge badge-' + img.status;
  badge.textContent = statusLabel(img.status);
  leftFooter.appendChild(badge);

  const selLabel = document.createElement('label');
  selLabel.className = 'card-select';
  const selBox = document.createElement('input');
  selBox.type = 'checkbox';
  selBox.checked = selected.has(img.filename);
  selBox.addEventListener('change', () => toggleSelect(img.filename, selBox.checked));
  selLabel.appendChild(selBox);
  selLabel.appendChild(document.createTextNode(' Keyword-Vorschlag'));
  leftFooter.appendChild(selLabel);

  left.appendChild(leftFooter);

  // ── Spalte 2: Metadaten ─────────────────────────────────────────────────
  const meta = document.createElement('div');
  meta.className = 'card-meta';

  const addMeta = (label, val, hi) => {{
    const r = metaRow(label, val, hi); if (r) meta.appendChild(r);
  }};
  const addHr = () => {{ const hr = document.createElement('hr'); hr.className = 'meta-divider'; meta.appendChild(hr); }};

  // ── Datei ──
  addMeta('Datei', img.filename.split('/').pop(), true);
  if (img.date) addMeta('Aufnahmedatum', img.date);
  const dims = [img.width && img.height ? img.width + '×' + img.height : '', img.megapixels ? img.megapixels + ' MP' : ''].filter(Boolean).join('  ·  ');
  if (dims) addMeta('Auflösung', dims);
  if (img.filesize) addMeta('Dateigröße', img.filesize);
  if (img.software) addMeta('Software', img.software);

  // ── Bewertung ──
  if (img.rating > 0) {{
    const rr = document.createElement('div'); rr.className = 'meta-row';
    const rl = document.createElement('div'); rl.className = 'meta-label'; rl.textContent = 'Bewertung';
    const rv = document.createElement('div'); rv.className = 'meta-rating';
    rv.textContent = '★'.repeat(img.rating) + '☆'.repeat(5 - img.rating);
    rr.appendChild(rl); rr.appendChild(rv); meta.appendChild(rr);
  }}

  // ── Kamera & Objektiv ──
  if (img.camera || img.lens || img.serial) {{
    addHr();
    if (img.camera)  addMeta('Kamera', img.camera, true);
    if (img.lens)    addMeta('Objektiv', img.lens);
    if (img.serial)  addMeta('Seriennummer', img.serial);
  }}

  // ── Belichtung ──
  if (img.focal || img.aperture || img.shutter || img.iso) {{
    addHr();
    const focal = [img.focal, img.focal35 ? '(35mm: ' + img.focal35 + ')' : ''].filter(Boolean).join(' ');
    if (focal) addMeta('Brennweite', focal);
    const exp = [
      img.aperture ? 'f/' + img.aperture : '',
      img.shutter  ? img.shutter + 's'   : '',
      img.iso      ? 'ISO ' + img.iso    : '',
      img.ev && img.ev !== '0' ? 'EV ' + img.ev : ''
    ].filter(Boolean).join('  ·  ');
    if (exp) addMeta('Belichtung', exp);
    if (img.program)  addMeta('Programm',  img.program);
    if (img.metering) addMeta('Messung',   img.metering);
    if (img.wb)       addMeta('Weißabgl.', img.wb);
    if (img.flash)    addMeta('Blitz',     img.flash);
  }}

  // ── GPS ──
  if (img.gps) {{
    addHr();
    const gpsRow = document.createElement('div'); gpsRow.className = 'meta-row';
    const gl = document.createElement('div'); gl.className = 'meta-label'; gl.textContent = 'GPS';
    const ga = document.createElement('a');
    ga.className = 'gps-link'; ga.href = img.gps.maps_url;
    ga.target = '_blank'; ga.textContent = img.gps.formatted;
    gpsRow.appendChild(gl); gpsRow.appendChild(ga); meta.appendChild(gpsRow);
  }}

  // ── Ort (IPTC) ──
  if (img.city || img.subloc || img.state || img.country) {{
    addHr();
    const loc = [img.subloc, img.city, img.state, img.country].filter(Boolean).join(', ');
    addMeta('Ort', loc);
  }}

  // ── Beschreibung & Copyright ──
  if (img.caption || img.copyright) {{
    addHr();
    if (img.caption)   addMeta('Beschreibung', img.caption);
    if (img.copyright) addMeta('Copyright', img.copyright);
  }}

  // ── In Datei gespeichert ──
  if (img.ex_title || (img.ex_kw && img.ex_kw.length > 0)) {{
    addHr();
    if (img.ex_title) addMeta('Titel in Datei', img.ex_title);
    if (img.ex_kw && img.ex_kw.length > 0) {{
      const kwRow = document.createElement('div'); kwRow.className = 'meta-row';
      const kl = document.createElement('div'); kl.className = 'meta-label';
      kl.textContent = 'Keywords in Datei (' + img.ex_kw.length + ')';
      kwRow.appendChild(kl);
      const kwWrap = document.createElement('div'); kwWrap.className = 'meta-exkw';
      img.ex_kw.slice(0, 10).forEach(k => {{
        const s = document.createElement('span'); s.textContent = k; kwWrap.appendChild(s);
      }});
      if (img.ex_kw.length > 10) {{
        const more = document.createElement('span'); more.textContent = '+' + (img.ex_kw.length - 10);
        more.style.color = '#555'; kwWrap.appendChild(more);
      }}
      kwRow.appendChild(kwWrap); meta.appendChild(kwRow);
    }}
  }}

  // ── Spalte 3: Titel + Keywords ─────────────────────────────────────────
  const right = document.createElement('div');
  right.className = 'card-right';

  const titleLabel = document.createElement('div');
  titleLabel.className = 'field-label'; titleLabel.textContent = 'Titel';
  right.appendChild(titleLabel);

  const titleInput = document.createElement('input');
  titleInput.className = 'title-input'; titleInput.type = 'text';
  titleInput.maxLength = 200; titleInput.value = img.title || '';
  const titleCounter = document.createElement('div');
  titleCounter.className = 'title-counter';
  titleInput.addEventListener('input', () => {{ updateTitleCounter(titleInput, titleCounter); scheduleAutoSave(card, badge); }});
  // Tab vom Titel-Feld springt direkt zum Keyword-Eingabefeld
  titleInput.addEventListener('keydown', e => {{
    if (e.key === 'Tab' && !e.shiftKey) {{ e.preventDefault(); kwInput.focus(); }}
  }});
  updateTitleCounter(titleInput, titleCounter);
  right.appendChild(titleInput);
  right.appendChild(titleCounter);

  const kwHead = document.createElement('div'); kwHead.className = 'kw-header';
  const kwLabel = document.createElement('div'); kwLabel.className = 'field-label'; kwLabel.textContent = 'Keywords';
  const kwCounter = document.createElement('span'); kwCounter.className = 'kw-counter';
  kwHead.appendChild(kwLabel); kwHead.appendChild(kwCounter);
  right.appendChild(kwHead);

  const tags = document.createElement('div'); tags.className = 'tags';
  (img.keywords || []).forEach(kw => appendTag(tags, kw));
  right.appendChild(tags);
  updateCounter(kwCounter, tags);

  const addRow = document.createElement('div'); addRow.className = 'add-row';
  const kwInput = document.createElement('input');
  kwInput.className = 'kw-input'; kwInput.type = 'text';
  kwInput.placeholder = 'Keywords hinzufügen, Komma-getrennt…';
  kwInput.addEventListener('keydown', e => handleKwKey(e, tags, kwCounter));
  // Shift+Tab vom Keyword-Feld zurück zum Titel
  kwInput.addEventListener('keydown', e => {{
    if (e.key === 'Tab' && e.shiftKey) {{ e.preventDefault(); titleInput.focus(); }}
  }});
  const addBtn = document.createElement('button');
  addBtn.className = 'btn-add'; addBtn.textContent = '+';
  addBtn.tabIndex = -1;  // aus Tab-Reihenfolge raus
  addBtn.addEventListener('click', () => addFromInput(kwInput, tags, kwCounter));
  addRow.appendChild(kwInput); addRow.appendChild(addBtn);
  right.appendChild(addRow);

  if (img.error_msg) {{
    const err = document.createElement('div');
    err.className = 'error-msg'; err.textContent = img.error_msg;
    right.appendChild(err);
  }}


  card.appendChild(left);
  card.appendChild(right);
  card.appendChild(meta);
  return card;
}}

function updateCard(card, img) {{
  card.dataset.status = img.status;
  const badge = card.querySelector('.badge');
  if (badge) {{
    badge.className = 'badge badge-' + img.status;
    badge.textContent = statusLabel(img.status);
  }}
  // Titel nur aktualisieren wenn nicht gerade fokussiert
  const ti = card.querySelector('.title-input');
  if (ti && document.activeElement !== ti) ti.value = img.title || '';
  // Keywords nur wenn nicht fokussiert und geändert
  const tags = card.querySelector('.tags');
  const kwInput = card.querySelector('.kw-input');
  if (tags && document.activeElement !== kwInput) {{
    const current = getTags(tags).join(',');
    const incoming = (img.keywords || []).join(',');
    if (current !== incoming) {{
      tags.innerHTML = '';
      (img.keywords || []).forEach(kw => appendTag(tags, kw));
      const counter = card.querySelector('.kw-counter');
      if (counter) updateCounter(counter, tags);
    }}
  }}
  applyCardVisibility(card, currentFilter);
}}

// ── Tag-Verwaltung ────────────────────────────────────────────────────────

function appendTag(container, kw) {{
  kw = String(kw).trim();
  if (!kw) return;
  const tag = document.createElement('span');
  tag.className = 'tag';
  const txt = document.createTextNode(kw);
  const btn = document.createElement('button');
  btn.className = 'tag-x';
  btn.textContent = '\u00d7';
  btn.addEventListener('click', () => {{
    tag.remove();
    const c = container.closest('.card');
    if (c) {{
      updateCounter(c.querySelector('.kw-counter'), container);
      scheduleAutoSave(c, c.querySelector('.badge'));
    }}
  }});
  tag.appendChild(txt);
  tag.appendChild(btn);
  container.appendChild(tag);
}}

function getTags(container) {{
  return Array.from(container.querySelectorAll('.tag'))
    .map(t => t.firstChild.textContent.trim())
    .filter(Boolean);
}}

function updateCounter(el, container) {{
  if (!el) return;
  const n = getTags(container).length;
  el.textContent = n + '/' + TARGET_KW;
  el.className = 'kw-counter ' + (n === TARGET_KW ? 'kw-ok' : 'kw-warn');
}}

function handleKwKey(e, container, counter) {{
  if (e.key === ',' ) {{
    e.preventDefault();
    const val = e.target.value.trim();
    if (val) {{ appendTag(container, val); e.target.value = ''; updateCounter(counter, container); }}
  }} else if (e.key === 'Enter' || e.key === 'Tab') {{
    e.preventDefault();
    addFromInput(e.target, container, counter);
  }}
}}

function addFromInput(input, container, counter) {{
  input.value.split(',').map(s => s.trim()).filter(Boolean).forEach(kw => {{
    if (!getTags(container).includes(kw)) appendTag(container, kw);
  }});
  input.value = '';
  updateCounter(counter, container);
  const c = container.closest('.card');
  if (c) scheduleAutoSave(c, c.querySelector('.badge'));
}}

// ── Speichern ─────────────────────────────────────────────────────────────

const _saveTimers = {{}};
function scheduleAutoSave(card, badge) {{
  const key = card.dataset.filename;
  clearTimeout(_saveTimers[key]);
  _saveTimers[key] = setTimeout(() => saveCard(card, badge), 1000);
}}

async function saveCard(card, badge) {{
  const filename = card.dataset.filename;
  const title    = card.querySelector('.title-input').value.trim();
  const keywords = getTags(card.querySelector('.tags'));
  try {{
    const r = await fetch('/api/save', {{
      method:'POST', headers:{{'Content-Type':'application/json'}},
      body: JSON.stringify({{filename, title, keywords}})
    }});
    const d = await r.json();
    if (d.ok) {{
      const isEmpty = !title && keywords.length === 0;
      const newStatus = isEmpty ? 'unbearbeitet' : 'done';
      card.dataset.status = newStatus;
      if (badge) {{
        if (isEmpty) {{ badge.className = 'badge badge-new'; badge.textContent = 'Unbearbeitet'; }}
        else {{ badge.className = 'badge badge-done'; badge.textContent = 'Übernommen'; }}
      }}
      updateHeaderStats();
    }} else {{
      toast('Fehler: ' + (d.error || 'Unbekannt'));
    }}
  }} catch(e) {{ toast('Netzwerkfehler: ' + e); }}
}}

// ── Auswahl ──────────────────────────────────────────────────────────────

function toggleSelect(filename, checked) {{
  if (checked) selected.add(filename); else selected.delete(filename);
  updateSelCount();
}}

function selectAll() {{
  allImages.forEach(img => {{
    if (!isCardHidden(img.filename)) {{
      selected.add(img.filename);
      const cb = document.querySelector(`[data-filename="${{img.filename}}"] input[type=checkbox]`);
      if (cb) cb.checked = true;
    }}
  }});
  updateSelCount();
}}

function select100() {{
  let count = 0;
  allImages.forEach(img => {{
    if (isCardHidden(img.filename)) return;
    const cb = document.querySelector(`[data-filename="${{CSS.escape(img.filename)}}"] input[type=checkbox]`);
    if (count < 100) {{
      selected.add(img.filename);
      if (cb) cb.checked = true;
      count++;
    }} else {{
      selected.delete(img.filename);
      if (cb) cb.checked = false;
    }}
  }});
  updateSelCount();
}}

function selectNone() {{
  selected.clear();
  document.querySelectorAll('.card input[type=checkbox]').forEach(cb => cb.checked = false);
  updateSelCount();
}}

function selectUnprocessed() {{
  allImages.filter(img => img.status === 'unbearbeitet').forEach(img => {{
    selected.add(img.filename);
    const cb = document.querySelector(`[data-filename="${{img.filename}}"] input[type=checkbox]`);
    if (cb) cb.checked = true;
  }});
  updateSelCount();
}}

function showConfirm(msg) {{
  return Promise.resolve(window.confirm(msg));
}}

let _autoSaveAfterAnalysis = false;

async function saveAllPending() {{
  const pending = allImages.filter(i => i.status === 'pending').length;
  // Keine pending-Bilder aber Bilder ausgewählt → Analyse starten + danach auto-speichern
  if (pending === 0) {{
    if (selected.size === 0) {{ toast('Keine Bilder ausgewählt und keine Vorschläge vorhanden.'); return; }}
    const ok = await showConfirm(`${{selected.size}} ausgewählte Bilder analysieren und Keywords direkt speichern (kein Review)?`);
    if (!ok) return;
    _autoSaveAfterAnalysis = true;
    await startAnalysis();
    return;
  }}
  const ok = await showConfirm(`${{pending}} KI-Vorschläge ohne Review direkt speichern?`);
  if (!ok) return;
  await _doSaveAllPending();
}}

async function _doSaveAllPending() {{
  const n = allImages.filter(i => i.status === 'pending').length;
  sbSet('Speichere ' + n + ' Bilder…', true);
  try {{
    const r = await fetch('/api/save-all-pending', {{method:'POST', headers:{{'Content-Type':'application/json'}}, body:'{{}}'}});
    const d = await r.json();
    if (d.ok) {{
      toast(`✓ ${{d.saved}} Bilder gespeichert` + (d.errors.length ? ` | ${{d.errors.length}} Fehler` : ''));
      sbIdle(d.saved + ' Bilder gespeichert');
      await loadImages();
    }} else {{
      toast('Fehler: ' + (d.error || 'Unbekannt'));
      sbIdle('Fehler beim Speichern');
    }}
  }} catch(e) {{ toast('Fehler: ' + e); sbIdle('Fehler'); }}
}}

async function resetErrors() {{
  const n = allImages.filter(i => i.status === 'error').length;
  if (n === 0) {{ toast('Keine Fehler vorhanden.'); return; }}
  if (!confirm(n + ' Fehler-Einträge zurücksetzen?')) return;
  await fetch('/api/reset', {{method:'POST',
    headers:{{'Content-Type':'application/json'}},
    body: JSON.stringify({{only_errors: true}})}});
  await loadImages();
  toast(n + ' Fehler zurückgesetzt.');
}}

function isCardHidden(filename) {{
  const card = document.querySelector(`[data-filename="${{CSS.escape(filename)}}"]`);
  return card ? card.classList.contains('hidden') : false;
}}

function updateSelCount() {{
  document.getElementById('sel-count').textContent = selected.size + ' ausgewählt';
  document.getElementById('ana-count').textContent = selected.size;
  updateCost();
}}

// ── Filter ───────────────────────────────────────────────────────────────

function setFilter(status, btn) {{
  currentFilter = status;
  document.querySelectorAll('.filter-btn').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
  const grid = document.getElementById('gallery-grid');
  // Bei "done": zuletzt bearbeitete Bilder oben
  if (status === 'done') {{
    const cards = Array.from(grid.querySelectorAll('.card'));
    cards.sort((a, b) => (b.dataset.timestamp || '').localeCompare(a.dataset.timestamp || ''));
    cards.forEach(c => grid.appendChild(c));
  }}
  applyAllFilters();
}}

function applyFilter(status) {{
  document.querySelectorAll('.card').forEach(c => applyCardVisibility(c, status));
}}

let _minRating = 0;

function applyCardVisibility(card, status) {{
  const s = card.dataset.status;
  const statusOk = status === 'all'
    || status === s
    || (status === 'mit'   && s === 'done')
    || (status === 'ohne'  && s !== 'done');
  const dateOk   = matchesDateFilter(card.dataset.date || '');
  const ratingOk = _minRating === 0 || parseInt(card.dataset.rating || 0) >= _minRating;
  const folderOk = matchesFolderFilter(card.dataset.folder || '');
  card.classList.toggle('hidden', !(statusOk && dateOk && ratingOk && folderOk));
}}

// ── Datumsfilter ─────────────────────────────────────────────────────────────
const _MONTHS = ['','Jan','Feb','Mär','Apr','Mai','Jun','Jul','Aug','Sep','Okt','Nov','Dez'];

function _fillSelect(sel, placeholder, values, labels, prevVal) {{
  while (sel.options.length) sel.remove(0);
  const o0 = document.createElement('option');
  o0.value = ''; o0.textContent = placeholder; sel.appendChild(o0);
  values.forEach((v, i) => {{
    const o = document.createElement('option');
    o.value = v; o.textContent = labels ? labels[i] : v;
    if (v === prevVal) o.selected = true;
    sel.appendChild(o);
  }});
}}

function buildDateFilter() {{
  const dates = new Set(allImages.map(i => i.date).filter(Boolean));
  const years = [...new Set([...dates].map(d => d.slice(0,4)))].sort();
  const sel = document.getElementById('df-year');
  const prev = sel.value;
  _fillSelect(sel, 'Alle Jahre', years, null, prev);
  dfYearChange(true);
}}

function _datesFor(year, month) {{
  return allImages.map(i => i.date).filter(d => {{
    if (!d) return false;
    if (year && !d.startsWith(year)) return false;
    if (month && d.slice(5,7) !== month.padStart(2,'0')) return false;
    return true;
  }});
}}

function dfYearChange(keepMonth) {{
  const year = document.getElementById('df-year').value;
  const msel = document.getElementById('df-month');
  const prev = keepMonth ? msel.value : '';
  const months = [...new Set(_datesFor(year,'').map(d => d.slice(5,7)))].sort();
  const labels = months.map(m => _MONTHS[parseInt(m)] || m);
  _fillSelect(msel, 'Alle Monate', months, labels, prev);
  dfMonthChange(keepMonth);
}}

function dfMonthChange(keepDay) {{
  const year  = document.getElementById('df-year').value;
  const month = document.getElementById('df-month').value;
  const dsel  = document.getElementById('df-day');
  const prev  = keepDay ? dsel.value : '';
  const days  = [...new Set(_datesFor(year, month).map(d => d.slice(8,10)))].sort((a,b)=>+a-+b);
  const labels = days.map(d => String(parseInt(d)));
  _fillSelect(dsel, 'Alle Tage', days, labels, prev);
  applyAllFilters();
}}

let _metaColVisible = true;
function toggleMetaCols() {{
  _metaColVisible = !_metaColVisible;
  document.querySelectorAll('.card-meta').forEach(m => m.classList.toggle('hidden', !_metaColVisible));
  document.querySelectorAll('.card').forEach(c => c.classList.toggle('meta-hidden', !_metaColVisible));
  document.getElementById('btn-meta-toggle').classList.toggle('active', _metaColVisible);
}}

function toggleRatingFilter() {{
  const bar = document.getElementById('rating-bar');
  const btn = document.getElementById('btn-rating-toggle');
  const isOpen = bar.classList.toggle('open');
  btn.classList.toggle('active', isOpen || _minRating > 0);
}}

function setRatingFilter(n, btn) {{
  _minRating = n;
  document.querySelectorAll('.rating-btn').forEach(b => b.classList.remove('active'));
  btn.classList.add('active');
  document.getElementById('btn-rating-toggle').classList.toggle('active', n > 0);
  applyAllFilters();
}}

function toggleDateFilter() {{
  const bar = document.getElementById('date-filter-bar');
  const btn = document.getElementById('btn-date-toggle');
  const isOpen = bar.classList.toggle('open');
  btn.classList.toggle('active', isOpen || !!document.getElementById('df-date').value);
  if (isOpen) document.getElementById('df-date').focus();
}}

function matchesDateFilter(date) {{
  const year  = document.getElementById('df-year')?.value  || '';
  const month = document.getElementById('df-month')?.value || '';
  const day   = document.getElementById('df-day')?.value   || '';
  if (!year && !month && !day) return true;
  if (!date) return false;
  if (year  && !date.startsWith(year)) return false;
  if (month && date.slice(5,7) !== month.padStart(2,'0')) return false;
  if (day   && date.slice(8,10) !== day.padStart(2,'0')) return false;
  return true;
}}

// ── Ordnerfilter ─────────────────────────────────────────────────────────────

function buildFolderFilter() {{
  const folders = new Set(allImages.map(i =>
    i.filename.includes('/') ? i.filename.substring(0, i.filename.lastIndexOf('/')) : ''
  ));
  _allFolders = [...folders].sort();
  _excludedFolders.clear();

  const container = document.getElementById('folder-btns');
  container.textContent = '';
  const toggleBtn = document.getElementById('btn-folder-toggle');

  if (_allFolders.length <= 1) {{
    toggleBtn.style.display = 'none';
    document.getElementById('folder-filter-bar').classList.remove('open');
    return;
  }}
  toggleBtn.style.display = '';

  _allFolders.forEach(f => {{
    const count = allImages.filter(i => {{
      const imgFolder = i.filename.includes('/')
        ? i.filename.substring(0, i.filename.lastIndexOf('/')) : '';
      return imgFolder === f;
    }}).length;
    const btn = document.createElement('button');
    btn.className = 'folder-btn active';
    btn.dataset.folder = f;
    const nameSpan = document.createTextNode(f || '(Stammordner)');
    const countSpan = document.createElement('span');
    countSpan.className = 'folder-count';
    countSpan.textContent = '(' + count + ')';
    btn.appendChild(nameSpan);
    btn.appendChild(document.createTextNode(' '));
    btn.appendChild(countSpan);
    btn.onclick = () => toggleFolder(f, btn);
    container.appendChild(btn);
  }});
}}

function toggleFolder(folder, btn) {{
  if (_excludedFolders.has(folder)) {{
    _excludedFolders.delete(folder);
    btn.classList.add('active');
  }} else {{
    _excludedFolders.add(folder);
    btn.classList.remove('active');
  }}
  document.getElementById('btn-folder-toggle').classList.toggle('active',
    _excludedFolders.size > 0 || document.getElementById('folder-filter-bar').classList.contains('open'));
  document.getElementById('folder-clear-btn').style.display =
    _excludedFolders.size > 0 ? 'inline-block' : 'none';
  applyAllFilters();
}}

function toggleFolderFilter() {{
  const bar = document.getElementById('folder-filter-bar');
  const btn = document.getElementById('btn-folder-toggle');
  const isOpen = bar.classList.toggle('open');
  btn.classList.toggle('active', isOpen || _excludedFolders.size > 0);
}}

function clearFolderFilter() {{
  _excludedFolders.clear();
  document.querySelectorAll('.folder-btn').forEach(b => b.classList.add('active'));
  document.getElementById('folder-clear-btn').style.display = 'none';
  document.getElementById('btn-folder-toggle').classList.toggle('active',
    document.getElementById('folder-filter-bar').classList.contains('open'));
  applyAllFilters();
}}

function matchesFolderFilter(folder) {{
  if (_excludedFolders.size === 0) return true;
  return !_excludedFolders.has(folder);
}}

function applyAllFilters() {{
  document.querySelectorAll('.card').forEach(c => applyCardVisibility(c, currentFilter));
  const active = !!(document.getElementById('df-year')?.value ||
                    document.getElementById('df-month')?.value ||
                    document.getElementById('df-day')?.value);
  document.getElementById('df-clear-btn').style.display = active ? 'inline-block' : 'none';
  document.getElementById('btn-date-toggle')?.classList.toggle('active', active);
  ['df-year','df-month','df-day'].forEach(id =>
    document.getElementById(id)?.classList.toggle('df-active', !!document.getElementById(id)?.value));
  const folderActive = _excludedFolders.size > 0;
  const anyFilter = active || folderActive;
  const visible = document.querySelectorAll('.card:not(.hidden)').length;
  const total   = document.querySelectorAll('.card').length;
  const countText = anyFilter ? visible + ' / ' + total + ' Bilder' : '';
  document.getElementById('df-count').textContent = active ? countText : '';
  document.getElementById('folder-count').textContent = folderActive ? countText : '';
}}

function clearDateFilter() {{
  ['df-year','df-month','df-day'].forEach(id => {{
    const el = document.getElementById(id);
    if (el) {{ el.value = ''; el.classList.remove('df-active'); }}
  }});
  dfYearChange(false);
}}

// ── Ordner wählen ────────────────────────────────────────────────────────

async function pickFolder() {{
  try {{
    const r = await fetch('/api/pick-folder', {{method:'POST',
      headers:{{'Content-Type':'application/json'}}, body:'{{}}'}});
    const d = await r.json();
    if (d.path) {{
      document.getElementById('folder-path').textContent = d.path;
      document.getElementById('folder-path').title = d.path;
      allImages = []; selected.clear();
      _excludedFolders.clear();
      document.getElementById('folder-filter-bar').classList.remove('open');
      document.getElementById('btn-folder-toggle').classList.remove('active');
      setFilter('all', document.querySelector('.filter-btn'));
      document.getElementById('gallery-grid').innerHTML =
        '<div class="empty-state" id="gallery-empty">Bilder werden geladen…</div>';
      await loadImages();
      toast('Ordner geladen: ' + d.name);
    }} else if (d.error && d.error !== 'Abgebrochen') {{
      toast('Fehler: ' + d.error);
    }}
  }} catch(e) {{ toast('Fehler: ' + e); }}
}}

// ── KI-Analyse ───────────────────────────────────────────────────────────

function goAnalysis() {{
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('.tab-content').forEach(t => t.classList.remove('active'));
  document.querySelector('.tab:nth-child(2)').classList.add('active');
  document.getElementById('tab-analysis').classList.add('active');
  updateCost();
}}

function updateCost() {{
  const model = document.getElementById('model-sel').value;
  const m = MODELS[model];
  const n = selected.size;
  const inCost  = (n * EST_IN  / 1e6) * m.input_price;
  const outCost = (n * EST_OUT / 1e6) * m.output_price;
  const total   = inCost + outCost;
  const box = document.getElementById('cost-box');
  if (n === 0) {{
    box.textContent = 'Bitte Bilder in der Galerie auswählen.';
  }} else {{
    box.innerHTML = '';
    const lines = [
      [n + ' Bilder', ''],
      ['Input (~' + (n*EST_IN/1000).toFixed(0) + 'k Tok)', '$' + inCost.toFixed(3)],
      ['Output (~' + (n*EST_OUT/1000).toFixed(0) + 'k Tok)', '$' + outCost.toFixed(3)],
    ];
    lines.forEach(([l, r]) => {{
      const row = document.createElement('div');
      row.style.cssText = 'display:flex;justify-content:space-between';
      const left = document.createElement('span'); left.textContent = l;
      const right = document.createElement('span'); right.textContent = r;
      row.appendChild(left); row.appendChild(right);
      box.appendChild(row);
    }});
    const sep = document.createElement('hr');
    sep.style.cssText = 'border-color:#333;margin:4px 0';
    box.appendChild(sep);
    const total_row = document.createElement('div');
    total_row.style.cssText = 'display:flex;justify-content:space-between;font-weight:700';
    const tl = document.createElement('span'); tl.textContent = 'Gesamt';
    const tr2 = document.createElement('strong'); tr2.textContent = '~$' + total.toFixed(2);
    tr2.style.color = '#fff'; tr2.style.fontSize = '15px';
    total_row.appendChild(tl); total_row.appendChild(tr2);
    box.appendChild(total_row);
  }}
}}

async function startAnalysis() {{
  if (selected.size === 0) {{ toast('Keine Bilder ausgewählt.'); return; }}
  const key = document.getElementById('api-key').value.trim();
  if (!key && !ENV_KEY_SET) {{ toast('Bitte API Key eingeben.'); return; }}

  // Warnung bei bereits analysierten oder keyword-reichen Bildern
  const warn = allImages.filter(img =>
    selected.has(img.filename) &&
    (img.status === 'pending' || img.status === 'done' || (img.keywords && img.keywords.length >= 10))
  );
  if (warn.length > 0) {{
    const choice = await _warnDialog(warn);
    if (choice === 'cancel') return;
    if (choice === 'skip') {{
      warn.forEach(img => selected.delete(img.filename));
      if (selected.size === 0) {{ toast('Keine neuen Bilder übrig.'); return; }}
      updateSelCount();
    }}
  }}
  const model = document.getElementById('model-sel').value;
  document.getElementById('btn-start').disabled = true;
  document.getElementById('btn-stop').style.display = 'block';
  document.getElementById('log-area').innerHTML = '';

  const r = await fetch('/api/analyze', {{
    method:'POST', headers:{{'Content-Type':'application/json'}},
    body: JSON.stringify({{
      api_key: key, model,
      filenames: Array.from(selected)
    }})
  }});
  const d = await r.json();
  if (!d.ok) {{ toast('Fehler: ' + d.error); resetAnaButtons(); sbIdle('Fehler beim Starten'); return; }}
  sbSet('KI-Analyse gestartet…', true);
  pollTimer = setInterval(pollStatus, 1500);
}}

async function stopAnalysis() {{
  await fetch('/api/stop', {{method:'POST',headers:{{'Content-Type':'application/json'}},body:'{{}}'}});
  clearInterval(pollTimer);
  resetAnaButtons();
  toast('Gestoppt.');
}}

async function pollStatus() {{
  try {{
    const r = await fetch('/api/status');
    const s = await r.json();
    const pct = s.total > 0 ? Math.round(s.done / s.total * 100) : 0;
    document.getElementById('prog-fill').style.width = pct + '%';
    document.getElementById('prog-text').textContent =
      s.running
        ? s.done + '/' + s.total + ' Bilder (' + pct + '%) – aktuell: ' + (s.current_file || '')
        : 'Fertig: ' + s.done + '/' + s.total + ' Bilder | ' +
          s.input_tokens.toLocaleString() + ' + ' + s.output_tokens.toLocaleString() +
          ' Tokens | $' + s.cost.toFixed(3);
    if (s.running) {{
      sbSet('KI-Analyse: ' + s.done + '/' + s.total + ' (' + pct + '%) – ' + (s.current_file || ''), true, '$' + s.cost.toFixed(3));
    }}

    // Log aktualisieren
    const area = document.getElementById('log-area');
    // Laufendes Bild anzeigen
    let runItem = area.querySelector('.log-run');
    if (s.running && s.current_file) {{
      if (!runItem) {{
        runItem = document.createElement('div');
        runItem.className = 'log-item log-run';
        area.prepend(runItem);
      }}
      runItem.textContent = '⏳ ' + s.current_file;
    }} else if (runItem) runItem.remove();

    // Abgeschlossene Einträge
    const logCount = area.querySelectorAll('.log-ok,.log-err').length;
    s.log.slice(logCount).forEach(entry => {{
      const item = document.createElement('div');
      if (entry.status === 'ok') {{
        item.className = 'log-item log-ok';
        const left = document.createElement('span');
        left.textContent = '\u2713 ' + entry.filename +
          ' (' + (entry.kw_count || 0) + ' KW)';
        const right = document.createElement('span');
        right.className = 'log-cost';
        right.textContent = (entry.in_tokens||0) + '+' + (entry.out_tokens||0) +
          ' Tok | $' + (entry.cost||0).toFixed(4);
        item.appendChild(left); item.appendChild(right);
      }} else {{
        item.className = 'log-item log-err';
        item.textContent = '\u2717 ' + entry.filename + ': ' + (entry.error||'');
      }}
      area.insertBefore(item, area.querySelector('.log-run'));
    }});

    if (!s.running) {{
      clearInterval(pollTimer);
      resetAnaButtons();
      toast('Analyse abgeschlossen: ' + s.done + ' Bilder | $' + s.cost.toFixed(3));
      sbIdle('Analyse abgeschlossen: ' + s.done + ' Bilder | $' + s.cost.toFixed(3));
      await loadImages();
      if (_autoSaveAfterAnalysis) {{
        _autoSaveAfterAnalysis = false;
        await _doSaveAllPending();
      }} else {{
        openReview(); // Review direkt starten
      }}
    }}
  }} catch(e) {{}}
}}

function resetAnaButtons() {{
  document.getElementById('btn-start').disabled = false;
  document.getElementById('btn-stop').style.display = 'none';
}}

// ── Auswertung ────────────────────────────────────────────────────────────

async function loadStats() {{
  const r = await fetch('/api/stats');
  const s = await r.json();

  const cards = document.getElementById('stats-cards');
  cards.innerHTML = '';
  [
    ['Übernommen', s.done, ''],
    ['KI-Vorschlag', s.pending, ''],
    ['Fehler', s.errors, ''],
    ['Input Tokens', s.total_input.toLocaleString(), 'gesamt'],
    ['Output Tokens', s.total_output.toLocaleString(), 'gesamt'],
    ['Gesamtkosten', '$' + s.total_cost.toFixed(4), 'USD'],
  ].forEach(([label, val, sub]) => {{
    const c = document.createElement('div');
    c.className = 'stat-card';
    const l = document.createElement('div'); l.className = 'label'; l.textContent = label;
    const v = document.createElement('div'); v.className = 'value'; v.textContent = val;
    const sb = document.createElement('div'); sb.className = 'sub'; sb.textContent = sub;
    c.appendChild(l); c.appendChild(v); c.appendChild(sb);
    cards.appendChild(c);
  }});

  const tbody = document.getElementById('stats-tbody');
  tbody.innerHTML = '';
  if (!s.per_image || s.per_image.length === 0) {{
    const tr = document.createElement('tr');
    const td = document.createElement('td');
    td.colSpan = 5; td.textContent = 'Noch keine API-Aufrufe.';
    td.style.color = 'var(--muted)'; td.style.padding = '20px';
    tr.appendChild(td); tbody.appendChild(tr);
    return;
  }}
  s.per_image.forEach(row => {{
    const tr = document.createElement('tr');
    [row.filename, statusLabel(row.status),
     row.input_tokens.toLocaleString(),
     row.output_tokens.toLocaleString(),
     '$' + row.cost.toFixed(4)
    ].forEach(val => {{
      const td = document.createElement('td');
      td.textContent = val;
      tr.appendChild(td);
    }});
    tbody.appendChild(tr);
  }});
}}

// ── Header-Stats ──────────────────────────────────────────────────────────

function updateHeaderStats() {{
  const done = allImages.filter(i => i.status === 'done').length;
  const pend = allImages.filter(i => i.status === 'pending').length;
  const el = document.getElementById('header-stats');
  el.innerHTML = '';
  const mk = (cls, txt) => {{
    const s = document.createElement('span');
    s.className = cls; s.textContent = txt;
    return s;
  }};
  el.appendChild(mk('hs-done', '\u2713 ' + done + ' übernommen'));
  el.appendChild(mk('hs-pend', '\u23f3 ' + pend + ' Vorschlag'));
  el.appendChild(mk('', allImages.length + ' Bilder gesamt'));
}}

// ── Hilfsfunktionen ───────────────────────────────────────────────────────

function statusLabel(s) {{
  return {{'done':'Übernommen','pending':'KI-Vorschlag',
           'unbearbeitet':'Unbearbeitet','error':'Fehler'}}[s] || s;
}}

function toast(msg) {{
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.display = 'block';
  setTimeout(() => t.style.display = 'none', 3000);
}}

// ── Statusbar ─────────────────────────────────────────────────────────────────
function sbSet(text, active=false, right='') {{
  const dot  = document.getElementById('sb-dot');
  const txt  = document.getElementById('sb-text');
  const rgt  = document.getElementById('sb-right');
  if (dot)  {{ dot.classList.toggle('active', active); }}
  if (txt)  txt.textContent = text;
  if (rgt)  rgt.textContent = right;
}}
function sbIdle(msg='Bereit') {{ sbSet(msg, false, new Date().toLocaleTimeString('de-DE', {{hour:'2-digit',minute:'2-digit'}})); }}

// ── Warn-Dialog ──────────────────────────────────────────────────────────────
let _warnResolve = null;

function _warnDialog(imgs) {{
  return new Promise(resolve => {{
    _warnResolve = choice => {{
      document.getElementById('warn-modal').classList.add('hidden');
      _warnResolve = null;
      resolve(choice);
    }};
    const title = document.getElementById('warn-title');
    title.textContent = imgs.length + ' Bild(er) wurden bereits analysiert oder haben schon Keywords:';
    const list = document.getElementById('warn-list');
    _rvClear(list);
    imgs.forEach(img => {{
      const li = document.createElement('li');
      li.textContent = img.filename;
      list.appendChild(li);
    }});
    document.getElementById('warn-modal').classList.remove('hidden');
  }});
}}

// ── Review-Modus ─────────────────────────────────────────────────────────────
let _rvQueue = [], _rvIdx = 0;

async function openReview() {{
  // Sicherstellen, dass allImages aktuell ist
  if (!allImages.some(i => i.status === 'pending')) await loadImages();
  _rvQueue = allImages.filter(i => i.status === 'pending');
  if (_rvQueue.length === 0) {{ toast('Keine KI-Vorschläge zum Überprüfen.'); return; }}
  _rvIdx = 0;
  document.getElementById('review-modal').classList.remove('hidden');
  _rvShow(0);
  document.addEventListener('keydown', _rvKey);
}}

function rvToggleMeta() {{
  const fields = document.getElementById('rv-fields');
  const btn = document.getElementById('rv-toggle-meta');
  const visible = !fields.classList.contains('hidden');
  fields.classList.toggle('hidden', visible);
  btn.style.color = visible ? '' : 'var(--accent)';
}}

function closeReview() {{
  document.getElementById('review-modal').classList.add('hidden');
  document.removeEventListener('keydown', _rvKey);
  loadImages();
}}

function _rvKey(e) {{
  if (e.key === 'Escape') {{ closeReview(); return; }}
  const inKw = document.activeElement && document.activeElement.id === 'rv-kwinput';
  if (e.key === 'ArrowRight' && !inKw) rvNav(1);
  if (e.key === 'ArrowLeft'  && !inKw) rvNav(-1);
  if (e.key === 'Enter'      && !inKw) {{ e.preventDefault(); rvSave(); }}
}}

function _rvClear(el) {{ while (el.firstChild) el.removeChild(el.firstChild); }}

function _rvShow(idx) {{
  const img = _rvQueue[idx];
  if (!img) return;
  document.getElementById('rv-prev').disabled = idx === 0;
  document.getElementById('rv-next').disabled = idx >= _rvQueue.length - 1;
  document.getElementById('rv-count').textContent = (idx+1) + ' / ' + _rvQueue.length;
  document.getElementById('rv-name').textContent  = img.filename;
  const el = document.getElementById('rv-img');
  const imgStatus = document.getElementById('rv-img-status');
  el.style.display = 'none';
  if (imgStatus) imgStatus.textContent = '⏳ Lade Bild…';
  sbSet('Lade Vorschau: ' + img.filename, true);
  el.onload  = () => {{
    el.style.display = 'block';
    if (imgStatus) imgStatus.style.display = 'none';
    sbIdle('Bereit');
  }};
  el.onerror = () => {{
    if (imgStatus) imgStatus.textContent = '⚠ Bild konnte nicht geladen werden';
    sbIdle('⚠ Vorschau fehlgeschlagen');
  }};
  el.src = '/preview/' + encodeURIComponent(img.filename);
  const rvTitle = document.getElementById('rv-title');
  rvTitle.value = img.title || '';
  updateTitleCounter(rvTitle, document.getElementById('rv-title-counter'));
  const tags = document.getElementById('rv-tags');
  _rvClear(tags);
  (img.keywords || []).forEach(kw => _rvTag(tags, kw));
  updateCounter(document.getElementById('rv-kwcount'), tags);
  document.getElementById('rv-kwinput').value = '';
  const gpsEl = document.getElementById('rv-gps');
  if (gpsEl) {{
    try {{
      if (img.gps && img.gps.formatted) {{
        _rvClear(gpsEl);
        const pin = document.createTextNode('📍 ');
        const link = document.createElement('a');
        link.href = img.gps.maps_url || '#';
        link.target = '_blank';
        link.textContent = img.gps.formatted;
        gpsEl.appendChild(pin);
        gpsEl.appendChild(link);
        gpsEl.style.display = '';
      }} else {{
        gpsEl.style.display = 'none';
      }}
    }} catch(e) {{ gpsEl.style.display = 'none'; }}
  }}
}}

let _dragTag = null;

function _rvTag(container, kw) {{
  kw = String(kw).trim(); if (!kw) return;
  const tag = document.createElement('span');
  tag.className = 'tag';
  tag.draggable = true;
  tag.appendChild(document.createTextNode(kw));
  const btn = document.createElement('button');
  btn.className = 'tag-x'; btn.textContent = '\u00d7';
  btn.onclick = () => {{ tag.remove(); updateCounter(document.getElementById('rv-kwcount'), container); }};
  tag.appendChild(btn);

  tag.addEventListener('dragstart', e => {{
    _dragTag = tag;
    tag.classList.add('dragging');
    e.dataTransfer.effectAllowed = 'move';
  }});
  tag.addEventListener('dragend', () => {{
    _dragTag = null;
    tag.classList.remove('dragging');
    container.querySelectorAll('.tag').forEach(t => t.classList.remove('drop-left','drop-right'));
  }});
  tag.addEventListener('dragover', e => {{
    e.preventDefault();
    if (!_dragTag || _dragTag === tag) return;
    e.dataTransfer.dropEffect = 'move';
    const mid = tag.getBoundingClientRect().left + tag.getBoundingClientRect().width / 2;
    container.querySelectorAll('.tag').forEach(t => t.classList.remove('drop-left','drop-right'));
    tag.classList.add(e.clientX < mid ? 'drop-left' : 'drop-right');
  }});
  tag.addEventListener('dragleave', () => {{
    tag.classList.remove('drop-left','drop-right');
  }});
  tag.addEventListener('drop', e => {{
    e.preventDefault();
    if (!_dragTag || _dragTag === tag) return;
    const mid = tag.getBoundingClientRect().left + tag.getBoundingClientRect().width / 2;
    tag.classList.remove('drop-left','drop-right');
    if (e.clientX < mid) container.insertBefore(_dragTag, tag);
    else container.insertBefore(_dragTag, tag.nextSibling);
    updateCounter(document.getElementById('rv-kwcount'), container);
  }});

  container.appendChild(tag);
}}

function rvAddKw() {{
  const input = document.getElementById('rv-kwinput');
  const tags  = document.getElementById('rv-tags');
  input.value.split(',').map(s => s.trim()).filter(Boolean).forEach(kw => {{
    if (!getTags(tags).includes(kw)) _rvTag(tags, kw);
  }});
  input.value = '';
  updateCounter(document.getElementById('rv-kwcount'), tags);
}}

function rvNav(dir) {{
  const next = _rvIdx + dir;
  if (next < 0 || next >= _rvQueue.length) return;
  _rvIdx = next; _rvShow(_rvIdx);
}}

async function rvSave() {{
  const img = _rvQueue[_rvIdx];
  if (!img) return;
  const title    = document.getElementById('rv-title').value.trim();
  const keywords = getTags(document.getElementById('rv-tags'));
  try {{
    const r = await fetch('/api/save', {{
      method:'POST', headers:{{'Content-Type':'application/json'}},
      body: JSON.stringify({{filename: img.filename, title, keywords}})
    }});
    const d = await r.json();
    if (d.ok) {{
      sbSet('Gespeichert: ' + img.filename, false);
      setTimeout(sbIdle, 2000);
      _rvQueue.splice(_rvIdx, 1);
      if (_rvQueue.length === 0) {{ closeReview(); toast('Alle Bilder überprüft ✓'); sbIdle('Review abgeschlossen'); return; }}
      if (_rvIdx >= _rvQueue.length) {{ closeReview(); toast('Alle Bilder überprüft ✓'); sbIdle('Review abgeschlossen'); return; }}
      _rvShow(_rvIdx);
    }} else {{ toast('Fehler: ' + (d.error || 'Unbekannt')); }}
  }} catch(e) {{ toast('Netzwerkfehler: ' + e); sbIdle('Netzwerkfehler'); }}
}}

function _rvUpdateButtons() {{
  const has = allImages.some(i => i.status === 'pending');
  ['btn-review-gallery','btn-review-ana'].forEach(id => {{
    const el = document.getElementById(id);
    if (el) el.style.display = has
      ? (id === 'btn-review-gallery' ? 'inline-block' : 'block') : 'none';
  }});
}}

// ── Titelzeichen-Zähler ───────────────────────────────────────────────────
function updateTitleCounter(input, el) {{
  if (!el) return;
  const n = input.value.length;
  el.textContent = n + '/200 Zeichen' + (n > 70 ? '  ⚠ Adobe zeigt ~70 Zeichen an' : '');
  el.className = 'title-counter' + (n > 70 ? ' warn' : '');
}}

// ── Keywords übertragen ───────────────────────────────────────────────────
let _transferSource = null;

function openTransfer() {{
  _transferSource = _rvQueue[_rvIdx];
  if (!_transferSource) return;
  const list = document.getElementById('transfer-list');
  _rvClear(list);
  const hint = document.getElementById('transfer-hint');
  hint.textContent = 'Quelle: ' + _transferSource.filename;

  allImages
    .filter(i => i.filename !== _transferSource.filename)
    .forEach(img => {{
      const item = document.createElement('div');
      item.className = 'transfer-item';
      item.dataset.filename = img.filename;
      item.addEventListener('click', () => item.classList.toggle('selected'));
      const th = document.createElement('img');
      th.src = '/thumbnail/' + encodeURIComponent(img.filename);
      th.loading = 'lazy';
      const nm = document.createElement('div');
      nm.className = 'transfer-item-name';
      nm.textContent = img.filename;
      item.appendChild(th); item.appendChild(nm);
      list.appendChild(item);
    }});
  document.getElementById('transfer-modal').classList.remove('hidden');
}}

function closeTransfer() {{
  document.getElementById('transfer-modal').classList.add('hidden');
}}

async function confirmTransfer() {{
  const targets = [...document.querySelectorAll('.transfer-item.selected')]
    .map(i => i.dataset.filename);
  if (targets.length === 0) {{ toast('Keine Bilder ausgewählt.'); return; }}
  closeTransfer();
  try {{
    const r = await fetch('/api/copy-meta', {{
      method:'POST', headers:{{'Content-Type':'application/json'}},
      body: JSON.stringify({{source: _transferSource.filename, targets}})
    }});
    const d = await r.json();
    if (d.ok) {{
      toast('Keywords auf ' + d.count + ' Bild(er) übertragen ✓');
      await loadImages();
    }} else {{ toast('Fehler: ' + (d.error || 'Unbekannt')); }}
  }} catch(e) {{ toast('Netzwerkfehler: ' + e); }}
}}

// ── Galerie-Bildansicht ───────────────────────────────────────────────────
function openGalleryView(filename) {{
  _rvQueue = allImages.filter(i => {{
    const card = document.querySelector(`[data-filename="${{CSS.escape(i.filename)}}"]`);
    return card && !card.classList.contains('hidden');
  }});
  _rvIdx = _rvQueue.findIndex(i => i.filename === filename);
  if (_rvIdx < 0) _rvIdx = 0;
  document.getElementById('review-modal').classList.remove('hidden');
  _rvShow(_rvIdx);
  document.addEventListener('keydown', _rvKey);
}}
</script>

<div id="transfer-modal" class="transfer-modal hidden">
  <div class="transfer-overlay" onclick="closeTransfer()"></div>
  <div class="transfer-dialog">
    <div class="transfer-head">
      <strong>&#x2197; Titel &amp; Keywords auf andere Bilder übertragen</strong>
      <button class="rv-hclose" onclick="closeTransfer()">&#x2715;</button>
    </div>
    <div class="transfer-actions">
      <button class="btn-rnav" onclick="document.querySelectorAll('.transfer-item').forEach(i=>i.classList.add('selected'))">Alle</button>
      <button class="btn-rnav" onclick="document.querySelectorAll('.transfer-item').forEach(i=>i.classList.remove('selected'))">Keine</button>
      <span id="transfer-hint" style="font-size:12px;color:var(--muted);margin-left:8px"></span>
    </div>
    <div id="transfer-list" class="transfer-list"></div>
    <div class="transfer-foot">
      <button class="btn-rnav" onclick="closeTransfer()">Abbrechen</button>
      <button class="btn-rsave" onclick="confirmTransfer()">&#x2197; Übertragen</button>
    </div>
  </div>
</div>

<div id="warn-modal" class="warn-modal hidden">
  <div class="warn-overlay" onclick="_warnResolve('cancel')"></div>
  <div class="warn-dialog">
    <div id="warn-title" class="warn-title"></div>
    <ul id="warn-list" class="warn-list"></ul>
    <div class="warn-btns">
      <button class="btn-wcancel" onclick="_warnResolve('cancel')">Abbrechen</button>
      <button class="btn-wskip"   onclick="_warnResolve('skip')">Diese nicht</button>
      <button class="btn-wall"    onclick="_warnResolve('all')">Alle analysieren</button>
    </div>
  </div>
</div>

<div id="review-modal" class="review-modal hidden">
  <div class="review-overlay" onclick="closeReview()"></div>
  <div class="review-dialog">
    <div class="rv-header">
      <span id="rv-count" class="rv-hcount"></span>
      <span id="rv-name"  class="rv-hname"></span>
      <button id="rv-toggle-meta" class="rv-hclose" onclick="rvToggleMeta()" title="Metadaten ein-/ausblenden" style="font-size:14px">&#x2139;</button>
      <button class="rv-hclose" onclick="closeReview()" title="Schließen (Esc)">&#x2715;</button>
    </div>
    <div class="rv-body">
      <div class="rv-imgwrap">
        <span class="img-status" id="rv-img-status">⏳ Lade Bild…</span>
        <img id="rv-img" src="" alt="" style="display:none">
      </div>
      <div class="rv-fields hidden" id="rv-fields">
        <div id="rv-gps" class="rv-gps" style="display:none"></div>
        <div class="field-label">Titel</div>
        <input id="rv-title" class="title-input" type="text" maxlength="200" style="width:100%"
               oninput="updateTitleCounter(this,document.getElementById('rv-title-counter'))">
        <div id="rv-title-counter" class="title-counter"></div>
        <div class="kw-header">
          <div class="field-label">Keywords</div>
          <span id="rv-kwcount" class="kw-counter"></span>
        </div>
        <div id="rv-tags" class="tags"></div>
        <div class="add-row">
          <input id="rv-kwinput" class="kw-input" type="text" placeholder="Keywords hinzufügen, Komma-getrennt&#x2026;"
                 onkeydown="if(event.key===','||event.key==='Tab'){{event.preventDefault();rvAddKw();}}">
          <button class="btn-add" onclick="rvAddKw()">+</button>
        </div>
      </div>
    </div>
    <div class="rv-footer">
      <button id="rv-prev" class="btn-rnav" onclick="rvNav(-1)">&#x25C4; Zur&#xFC;ck</button>
      <button id="rv-next" class="btn-rskip" onclick="rvNav(1)">Weiter &#x25BA;</button>
      <span style="flex:1;font-size:11px;color:var(--muted);text-align:center">
        &#x2190;&#x2192; Navigation &nbsp;&middot;&nbsp; Enter = Speichern &nbsp;&middot;&nbsp; Tab = Weiter &nbsp;&middot;&nbsp; Esc = Schlie&#xDF;en
      </span>
      <button class="btn-rnav" onclick="openTransfer()" title="Titel &amp; Keywords auf andere Bilder übertragen">&#x2197; Übertragen</button>
      <button class="btn-rsave" onclick="rvSave()">&#x2713; Speichern &amp; weiter</button>
    </div>
  </div>
</div>
</body>
</html>"""


# ─── Main ────────────────────────────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser(description="Picture Keyworder")
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--dir",  type=Path, default=Path(__file__).parent)
    args = ap.parse_args()

    et = find_et()
    if not et:
        print("⚠ exiftool nicht gefunden. GPS und IPTC-Prüfung deaktiviert.")
        print("  Installieren: ~/bin/exiftool")

    set_dir(args.dir.resolve())

    url = f"http://localhost:{args.port}"
    print(f"Picture Keyworder: {url}")
    print(f"Ordner: {_dir}")
    print("Mit Ctrl+C beenden.\n")

    threading.Thread(target=lambda: (time.sleep(0.8), webbrowser.open(url)),
                     daemon=True).start()

    try:
        ThreadedHTTPServer(("localhost", args.port), Handler).serve_forever()
    except KeyboardInterrupt:
        print("\nBeendet.")


if __name__ == "__main__":
    main()
