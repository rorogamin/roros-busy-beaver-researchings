#!/bin/bash
i=$(basename "$1")
cd "C:/Users/Rowan/Documents/st/bbwork/vendor/busy-beaver/Code" || exit 1
../../../.venv/Scripts/python.exe Enumerate.py --infile "../../../runs25/$i" \
  --outfile "../../../runs25b/$i.pb" --force --max-loops=20000000 --time=240 \
  --exp-linear-rules --max-block-size=100 --block-mult=3 -r \
  > "../../../logs25b/$i.log" 2>&1
