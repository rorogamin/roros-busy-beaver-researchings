#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

files=(
  LibTactics.v
  Helper.v
  TM.v
  Compute.v
  Flip.v
  Permute.v
  Individual.v
  BB33.v
  Individual33.v
  BB33_494.v
  Check494.v
)

rm -f -- *.vo *.vos *.vok *.glob .*.aux .lia.cache .nia.cache
for f in "${files[@]}"; do
  echo "COQC $f"
  coqc -Q . BusyCoq "$f"
done
