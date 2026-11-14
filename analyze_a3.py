#!/usr/bin/env python3
"""Summarize a3context.py output."""
from collections import Counter
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "logs/a3context_1e10.csv"
A = []
B = []
with open(path) as f:
    for line in f:
        p = line.rstrip("\n").split(" ", 5)
        if not p:
            continue
        if p[0] == "A3":
            A.append((int(p[1]), int(p[2]), int(p[3]), int(p[4]), p[5] if len(p) > 5 else ""))
        elif p[0] == "B1":
            B.append((int(p[1]), int(p[2]), p[3] if len(p) > 3 else ""))

print("A3", len(A), "B1", len(B))
if not A:
    raise SystemExit
mx = max(A, key=lambda x: x[2])
print("max d4", mx[2], "at step", mx[0], "d1", mx[3], "prefix", mx[4][:20])
print("min d1", min(x[3] for x in A), "max d1", max(x[3] for x in A))
print("min d1-d4", min(x[3] - x[2] for x in A))
print("violations d1<=d4", sum(1 for x in A if x[3] <= x[2]))

for k in (2, 4, 6, 8, 10, 16):
    c = Counter(x[4][:k] for x in A)
    print("prefix", k, "unique", len(c), "top", c.most_common(8))

print("d4 ranges:")
for lo in range(0, 101, 10):
    n = sum(1 for x in A if lo <= x[2] < lo + 10)
    if n:
        print(f"  {lo:3d}-{lo+9:3d}: {n}")
print("last 12 A3:")
for x in A[-12:]:
    print(" ", x[0], "d4", x[2], "d1", x[3], x[4][:16])

bad = 0
deep_fail = 0
no4 = 0
for _, _, d4, d1, pre in A:
    if d4 <= 0:
        no4 += 1
        continue
    if d4 > len(pre) or pre[d4 - 1] != "4":
        bad += 1
    if d1 > 0 and d1 <= len(pre) and pre[d1 - 1] != "1":
        bad += 1
    if any(ch in "14" for ch in pre[: d4 - 1]):
        bad += 1
    # A deep 4 has some used-tape cell farther left.  All-zero suffix means
    # the 4 is the leftmost used cell in the 80-cell window.
    if not any(ch != "0" for ch in pre[d4:]):
        deep_fail += 1
print("prefix/distance consistency failures", bad, "no4", no4, "deep_fail", deep_fail)
print("d1-d4 min/max", min(x[3]-x[2] for x in A), max(x[3]-x[2] for x in A))
print("d1-d4 <= 2:", sum(1 for x in A if x[3]-x[2] <= 2))
