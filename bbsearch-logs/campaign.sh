#!/usr/bin/env bash
# Big-budget, extra-state searches on the cores that showed growth in run C.
cd "$(dirname "$0")" || exit 1

run() {  # tag core states symbols cap budget
  local tag="$1" core="$2" st="$3" sym="$4" cap="$5" bud="$6"
  {
    echo "== $tag: core=$core states=$st symbols=$sym cap=$cap budget=$bud"
    ./bbsearch.exe --core "$core" --states "$st" --symbols "$sym" --cap "$cap" --budget "$bud"
    echo "== $tag DONE"
  } > "$tag.log" 2>&1
}

run fw1_5_s7   fw1_5   7  5 200000 3e9 &
run fw3_5_s8   fw3_5   8  5 200000 3e9 &
run fwm21_5_s10 fwm21_5 10 5 200000 3e9 &
run fw1_6_s4   fw1_6   4  6 200000 3e9 &
wait
echo "CAMPAIGN DONE"
