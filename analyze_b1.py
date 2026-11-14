#!/usr/bin/env python3
"""Summarize B1 left contexts from a3context output."""
from collections import Counter
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "logs/a3context_1e10.csv"
B = []
with open(path) as f:
    for line in f:
        p = line.rstrip("\n").split(" ", 3)
        if p and p[0] == "B1":
            B.append((int(p[1]), int(p[2]), p[3] if len(p) > 3 else ""))

print("B1", len(B))
leading1 = 0
no4 = 0
shield = 0
top = Counter()
for st, pos, pre in B:
    if pre.startswith("1"):
        leading1 += 1
    d4 = pre.find("4")
    d1 = pre.find("1")
    if d4 < 0:
        no4 += 1
    elif d1 < 0 or d4 < d1:
        shield += 1
    top[pre[:8]] += 1
print("leading 1", leading1, "no 4 in prefix", no4, "4 before 1", shield)
print("top prefixes", top.most_common(12))
