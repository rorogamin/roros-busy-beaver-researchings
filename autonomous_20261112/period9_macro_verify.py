"""Macro verification for the period-9 CET pair.

Two local facts are checked:

1. The post-erase wall-crossing time for Agent 1 on
       (zeros up to W-1) 1^inf,  head C at -2
   is
       T_cross(W) = 2^(W+3) - (W+3).
   This is checked exactly for W = 4..12 in this script and was checked in C
   for W = 4..26.  For the actual wall W=69 it predicts 2^72 - 72 steps.

2. After the crossing, Agent 1 is B on a long one-run.  It approaches the
   period-9 glider from the left, cannot collide, and leaves Agent 2 in state
   C on an all-one run.  From there A2's C1 transition moves right one cell
   per step forever, while Agent 1 is to the left.  This is the escape.

The script is a macro check, not a full formal proof: the symbolic W=69
crossing is extrapolated from the exact finite formula and the local encounter
is checked at one representative distance.
"""

A1 = [
    [(1, -1, 1), None],
    [(1, -1, 2), (1, +1, 1)],
    [(0, +1, 1), (0, -1, 2)],
]
A2 = [
    [(1, +1, 1), (0, -1, 0)],
    [(0, +1, 2), (0, -1, 0)],
    [(1, -1, 1), (1, +1, 2)],
]


def cross_time(W, cap=2_000_000):
    tape = {x: 0 for x in range(-10, 200)}
    for x in range(W, 200):
        tape[x] = 1
    p, s = -2, 2
    for k in range(1, cap + 1):
        w, d, ns = A1[s][tape[p]]
        tape[p] = w
        p += d
        s = ns
        if p > W:
            return k
    return None


print("wall-crossing formula:")
for W in range(4, 13):
    got = cross_time(W)
    want = 2 ** (W + 3) - (W + 3)
    print(f"  W={W:2d}: got={got} want={want}")
    assert got == want, (W, got, want)
print("  W=69 predicted:", 2 ** 72 - 72)

# Local encounter: Agent 1 B on a one-run, Agent 2 phase-5 glider far right.
P = 100_000
tape = {x: 1 for x in range(-10_000, 200_000)}
for z, v in [(-2, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]:
    tape[P + z] = v
p1, s1 = P - 1000, 1
p2, s2 = P, 1
min_dist = p2 - p1
escaped = False
for k in range(1, 200_000):
    x = A1[s1][tape[p1]]
    y = A2[s2][tape[p2]]
    tape[p1] = x[0]
    tape[p2] = y[0]
    p1 += x[1]
    s1 = x[2]
    p2 += y[1]
    s2 = y[2]
    assert p1 != p2, ("collision", k)
    min_dist = min(min_dist, p2 - p1)
    if s2 == 2 and tape[p2] == 1 and all(tape[p2 + z] == 1 for z in range(-3, 4)):
        escaped = True
        print(f"encounter: step={k} p1={p1 - P} p2={p2 - P} "
              f"state2=C, distance={p2 - p1}")
        break
assert escaped
assert p1 < p2
# From C on a one, C1 = 1RC runs right at one cell per step.
q2, t2 = p2, s2
for _ in range(1000):
    y = A2[t2][tape[q2]]
    tape[q2] = y[0]
    q2 += y[1]
    t2 = y[2]
assert q2 == p2 + 1000 and t2 == 2
print("Agent 2 C-escape: 1000 steps at +1/step VERIFIED")

# Agent 1 cannot use its halt row.
assert all(tr is None or tr[2] in (1, 2) for row in A1[1:] for tr in row)
print("Agent 1 halt row A unreachable: VERIFIED")
print("RESULT: non-halting macro verified; W=69 crossing uses the exact "
      "finite formula and remains a symbolic extrapolation.")
