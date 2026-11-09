#!/usr/bin/env bash
# Build the whole Rocq 9.1 development from scratch and audit it for axioms.
set -u
cd "$(dirname "$0")/rocq" || exit 1

rm -f ./*.vo ./*.vok ./*.vos ./*.glob

fail=0
allout=""
for f in TM.v Bounds.v Core.v Machine1.v Machine2.v Machine3.v Machine4.v Machine5.v StackPass.v ModuleK.v Tower.v Eps1.v Eps1Ladder.v Eps0Drive.v Eps1Tape.v Eps1Copy.v; do
  echo "== compiling $f"
  out=$(rocq compile -Q . Top "$f" 2>&1)
  status=$?
  allout="$allout$out"
  # drop the harmless "large numeral" warnings and their location lines
  echo "$out" | grep -v "abstract-large-number" | grep -v "large numbers in nat" \
    | grep -v '^File ".*", line .*:$' | grep -v "^$"
  if [ $status -ne 0 ]; then
    echo "!! $f FAILED"
    fail=1
  fi
done

echo "== axiom audit"
# count occurrences, not lines: a file whose last Print Assumptions has no
# trailing newline merges with the next file's first line
closed=$(printf '%s' "$allout" | grep -o "Closed under the global context" | wc -l | tr -d ' ')
echo "theorems closed under the global context: $closed (expected 156)"
if [ "$closed" -ne 156 ]; then
  echo "!! axiom audit failed"
  fail=1
fi
if grep -rn "admit\|Admitted\|Axiom\|Parameter" ./*.v; then
  echo "!! forbidden vernacular found"
  fail=1
fi

if [ $fail -eq 0 ]; then
  echo "ALL CHECKS PASSED"
else
  echo "CHECKS FAILED"
fi
exit $fail
