#!/usr/bin/env python3
"""Near-miss analysis for the target's A3 shield."""
from collections import Counter
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "logs/a3context_1e10.csv"
A = []
with open(path) as f:
    for line in f:
        p = line.rstrip("\n").split(" ", 5)
        if p and p[0] == "A3":
            A.append((int(p[1]), int(p[2]), int(p[3]), int(p[4]), p[5] if len(p) > 5 else ""))

margins = Counter(x[3] - x[2] for x in A)
print("margin counts (d1-d4):")
for m in sorted(margins):
    if m <= 12:
        print(f"  {m}: {margins[m]}")

print("near-miss events with margin <= 2:")
for st, pos, d4, d1, pre in A:
    if d1 - d4 <= 2:
        print(f"  t={st} d4={d4} d1={d1} m={d1-d4} pre={pre}")

mx = max(A, key=lambda x: x[2])
print("max-d4 event:")
print(f"  t={mx[0]} d4={mx[2]} d1={mx[3]} pre={mx[4]}")

after = Counter()
for _, _, d4, d1, pre in A:
    if 0 < d4 < len(pre):
        after[pre[d4]] += 1
print("cell immediately beyond the 4 (farther left):", after)
