#!/bin/bash
loops="$1"; name="$2"; shift 2
cd "C:/Users/Rowan/Documents/st/bbwork/vendor/busy-beaver/Code" || exit 1
timeout 240 ../../../.venv/Scripts/python.exe Quick_Sim.py -r --exp-linear-rules --max-loops="$loops" "$@" > "../../../logs/q_$name.log" 2>&1
echo "exit $?" >> "../../../logs/q_$name.log"
