# 📸 Picture Keyworder

**AI-powered keywording tool for Adobe Stock photographers.**
Analyze your photos with Claude AI, generate optimized German titles & keywords, and write them directly into your JPEG files via ExifTool — all from a clean local web interface.

---

## ✨ Features

- **AI Analysis** — Uses Anthropic Claude (Sonnet) to generate titles and keywords tailored for Adobe Stock
- **Parallel Processing** — Analyzes up to 3 images simultaneously for fast batch processing
- **Gallery View** — Browse all images with live status indicators (green = done)
- **Review Mode** — Step through AI suggestions image by image, edit and save
- **Drag & Drop Keywords** — Reorder keywords by importance directly in the review modal
- **Direct Save** — Skip review and write all AI suggestions straight to files
- **Keyword Transfer** — Copy title & keywords from one image to similar shots
- **Subfolder Support** — Recursively scans nested folder structures
- **GPS Metadata** — Reads GPS coordinates and enriches keywords with location data
- **Resumable** — Interrupted analyses can be continued; already-processed images are skipped
- **Cost Tracking** — Live token usage and USD cost per image and in total
- **Status Bar** — Always-visible indicator showing what the app is currently doing
- **Favicon + Single File** — Entire app is one Python file, no framework needed

---

## 🖥 Requirements

| Dependency | Install |
|---|---|
| Python 3.9+ | [python.org](https://www.python.org) |
| [Anthropic Python SDK](https://github.com/anthropic-ai/anthropic-sdk-python) | `pip install anthropic` |
| [Pillow](https://pillow.readthedocs.io) | `pip install Pillow` |
| [ExifTool](https://exiftool.org) | `brew install exiftool` |
| Anthropic API Key | [console.anthropic.com](https://console.anthropic.com) |

---

## 🚀 Quick Start

```bash
# 1. Clone
git clone https://github.com/YOUR_USERNAME/picture-keyworder.git
cd picture-keyworder

# 2. Install dependencies
pip install anthropic Pillow

# 3. Install ExifTool (macOS)
brew install exiftool

# 4. Set your API key (optional – can also be entered in the UI)
export ANTHROPIC_API_KEY=sk-ant-...

# 5. Run
python keyword_stock.py
```

The app opens automatically at **http://localhost:8765**

### macOS Shortcut

Double-click `StockTagger.command` to launch directly from Finder.

---

## 🔧 Configuration

At the top of `keyword_stock.py`:

```python
TARGET_KW   = 40     # Number of keywords to generate (Adobe Stock max: 50)
MAX_SIDE    = 512    # Image resize before sending to API (saves tokens)
PORT        = 8765   # Local server port
PARALLEL_WORKERS = 3 # Simultaneous Claude API requests
```

---

## 📋 Workflow

1. **Open Folder** — Click "Ordner wählen" and select your JPEG folder
2. **Select Images** — Use "Alle", "Nur Neue" or "100" buttons to select images for analysis
3. **Analyze** — Switch to the "KI-Analyse" tab and click "Analyse starten"
4. **Review** — Step through AI suggestions, edit titles/keywords, save per image
   - Or use **"Analysieren & direkt speichern"** to skip review entirely
5. **Export** — Keywords and titles are written directly into the JPEG files via IPTC/XMP metadata

---

## 🤖 AI Prompt

The app instructs Claude to generate:
- **Title** (English, max 200 characters, descriptive)
- **Keywords** (German, exactly `TARGET_KW` keywords, sorted by relevance)
- Coverage: subject, mood, setting, time of day, photo style, conceptual themes, industry use cases
- GPS-aware: includes location keywords when GPS data is present in the image

---

## 📁 Data & Privacy

- All processing is **local** — only the resized image (max 512px) is sent to the Anthropic API
- Progress is saved to `~/.config/stock_tagger/<folder_hash>.json`
- No image data is stored remotely or logged

---

## 🛠 Tech Stack

- **Backend**: Python `http.server` (threaded), Anthropic SDK, Pillow, ExifTool subprocess
- **Frontend**: Vanilla JS + CSS (no frameworks), embedded in the Python file as an f-string
- **Metadata**: ExifTool writes IPTC `ObjectName` + `Keywords` and XMP `Title` + `Subject`

---

## 📄 License

MIT — do whatever you want with it.
