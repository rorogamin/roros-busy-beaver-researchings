#!/usr/bin/env bash
# usage: run_one.sh CORE N M
core="$(echo "$1" | tr -d '\r')"; n="$(echo "$2" | tr -d '\r')"; m="$(echo "$3" | tr -d '\r')"
NC=/c/Users/Rowan/Documents/findthatmachine/repos/roros-busy-beaver-researchings/newchampions
out=/c/Users/Rowan/Documents/findthatmachine/work/raw/${core}_${n}_${m}.txt
mkdir -p /c/Users/Rowan/Documents/findthatmachine/work/raw
[ -s "$out" ] && exit 0
"$NC/search/bbsearch_mc.exe" --core "$core" --cores-file "$NC/search/bbcores_plus.txt" \
  --states "$n" --symbols "$m" --cap 20000 --budget "${SWEEP_BUDGET:-120000000}" > "$out" 2>&1
