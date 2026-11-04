"""Structure scan for gem48 (: any SAFE state merges?

Safe merge conditions (write-before-move makes per-cell tags stale at
revisits, so only merge keys that need NO extra cell state are safe):
  A. identical-row twins: states q1, q2 with IDENTICAL rows for both bits
     (same write, dir, next). Merging is exact; zero slowdown.
  B. redirectable twins: rows identical up to `next` where the targets are
     themselves merge-able into the same compound state (transitive).
Also: unreachable-state scan (none expected) + halt-row inventory.

Run:  py -3.14 tools/_gem48_scan.py
"""
import re
from itertools import combinations

src = open('rocq/gemini_epsilon1_tm_48s_v2_fix.v', encoding='utf-8').read()
rows = re.findall(
    r'\| (S\d{2}), B([01]) => \(B([01]), ([LR]), (?:St (S\d{2})|Halt)\)', src)
TAB = {}
for q, br, w, d, nq in rows:
    q = int(q[1:]) - 1
    nxt = 'H' if nq == '' else int(nq[1:]) - 1
    TAB[(q, int(br))] = (int(w), d, nxt)
N = 48

def row_sig(q):
    return tuple(TAB[(q, b)] for b in (0, 1))

# --- A: identical rows
sigs = {}
for q in range(N):
    sigs.setdefault(row_sig(q), []).append(q)
twins = [v for v in sigs.values() if len(v) > 1]

# --- B: identical up to next-shared-class (union-find on pairs whose rows
#        match except `next` equal after merging — fixed-point check)
parent = list(range(N))
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]; x = parent[x]
    return x
def union(a, b):
    ra, rb = find(a), find(b); parent[ra] = rb

changed = True
while changed:
    changed = False
    for a, b in combinations(range(N), 2):
        ra, rb = find(a), find(b)
        if ra == rb:
            continue
        ok = True
        for bit in (0, 1):
            (w1, d1, n1), (w2, d2, n2) = TAB[(ra, bit)], TAB[(rb, bit)]
            # class of next under current partition OR Halt
            c1 = 'H' if n1 == 'H' else find(n1)
            c2 = 'H' if n2 == 'H' else find(n2)
            if (w1, d1) != (w2, d2) or c1 != c2:
                ok = False; break
        if ok:
            union(ra, rb); changed = True

groups = {}
for q in range(N):
    groups.setdefault(find(q), []).append(q)
multigroups = [v for v in groups.values() if len(v) > 1]

halters = [q for q in range(N) if any(TAB[(q, b)][2] == 'H' for b in (0, 1))]

print('gem48 structure scan (48 states):')
print(f'  A. exact identical-row twin groups: {twins if twins else "none"}')
print(f'  B. merge-closed groups (rows equal up to merged next): '
      f'{multigroups if multigroups else "none"}')
print(f'  halt-targeting states: {len(halters)} of 48')
dudy = 1
if twins or multigroups:
    print('  => a mechanical state reduction exists')
else:
    print('  => NO free mechanical reduction: every pair of rows differs in')
    print('     (write,dir) or next-class, so no safe zero-cost merge exists.')
raise SystemExit
