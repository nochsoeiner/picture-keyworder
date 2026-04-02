#!/bin/zsh
# StockTagger starten
cd "$(dirname "$0")"

# Abhängigkeiten prüfen
if ! python3 -c "import anthropic" &>/dev/null; then
  echo "Installiere anthropic..."
  pip3 install anthropic
fi

if ! python3 -c "from PIL import Image" &>/dev/null; then
  echo "Installiere Pillow..."
  pip3 install Pillow
fi

if [ -z "$(which exiftool 2>/dev/null)" ] && [ ! -f "$HOME/bin/exiftool" ]; then
  echo ""
  echo "⚠️  exiftool nicht gefunden."
  echo "Bitte installieren:"
  echo "  curl -L https://exiftool.org/Image-ExifTool-13.53.tar.gz -o /tmp/et.tar.gz"
  echo "  tar -xzf /tmp/et.tar.gz -C /tmp/"
  echo "  mkdir -p ~/bin && cp /tmp/Image-ExifTool-13.53/exiftool ~/bin/exiftool && chmod +x ~/bin/exiftool"
  echo "  cp -r /tmp/Image-ExifTool-13.53/lib ~/bin/lib"
  echo ""
  read -k1 "?Trotzdem starten? (j/n) "
  echo
  [[ $REPLY != [jJyY] ]] && exit 0
fi

echo ""
echo "┌─────────────────────────────────────┐"
echo "│          StockTagger                │"
echo "│  Adobe Stock Keywording mit KI      │"
echo "└─────────────────────────────────────┘"
echo ""

python3 keyword_stock.py "$@"
