#!/bin/bash
# run Enumerate.py on one machine file; arg is a path like runs25/h00
i=$(basename "$1")
cd "C:/Users/Rowan/Documents/st/bbwork/vendor/busy-beaver/Code" || exit 1
../../../.venv/Scripts/python.exe Enumerate.py --infile "../../../runs25/$i" \
  --outfile "../../../runs25/$i.pb" --force --max-loops=2000000 --time=45 \
  --exp-linear-rules --max-block-size=60 --block-mult=3 -r \
  > "../../../logs25/$i.log" 2>&1
