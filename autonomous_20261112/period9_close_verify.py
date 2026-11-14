"""Complete finite local proof that the period-9 CET pair never collides.

This replaces the earlier, unnecessary W=69 wall-crossing extrapolation.
After the verified counter exit, Agent 1 erases its one-block, reaches an
all-zero local tape at position -1 in state B, and then repeats a period-254
fixed local cycle confined to [-2, 5].  Agent 2 is a period-9 right-moving
glider whose minimum possible position is astronomically far to the right.
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

P70 = 2**72 - 74
T_EXIT = 673 + P70
assert T_EXIT == 2**72 + 599
print("exit arithmetic:", T_EXIT)

# Exit tape: Ag1 in B at 69, ones -1..68, all else zero.
tape = {x: 0 for x in range(-20, 100)}
for x in range(-1, 69):
    tape[x] = 1
p1, s1 = 69, 1
p2 = 524_707_386_985_516_134_924
s2 = 1

# First ten local Agent-1 steps from the exit.
for k in range(10):
    w, d, ns = A1[s1][tape[p1]]
    tape[p1] = w
    p1 += d
    s1 = ns
    assert p1 != p2
assert (p1, s1) == (59, 2)
assert all(tape[x] == 1 for x in range(-1, 60))
assert all(tape[x] == 0 for x in range(60, 69))
print("first ten exit steps: verified (p1=59, state C)")

# Agent 1 erases the remaining block and reaches the fixed-cycle entry.
for k in range(62):
    w, d, ns = A1[s1][tape[p1]]
    tape[p1] = w
    p1 += d
    s1 = ns
assert (p1, s1) == (-1, 1)
assert all(tape[x] == 0 for x in range(-20, 69))
assert tape[69] == 1  # left behind by the first exit step; outside the cycle
print("entry to all-zero local cycle: p1=-1, state B; a residue at 69 is inert")

# The fixed cycle is confined to [-2, 5] and has period 254.  Its entry is
# one step after the all-zero position above, in C at -2.
w, d, ns = A1[s1][tape[p1]]
tape[p1] = w
p1 += d
s1 = ns
assert (p1, s1) == (-2, 2)
key = lambda p, s: (p, s, tuple(tape.get(p + i, 0) for i in range(-6, 7)))
start = key(p1, s1)
lo = hi = p1
for k in range(254):
    w, d, ns = A1[s1][tape[p1]]
    tape[p1] = w
    p1 += d
    s1 = ns
    lo = min(lo, p1)
    hi = max(hi, p1)
    assert p1 != p2
assert key(p1, s1) == start
assert lo >= -2 and hi <= 5
print(f"period-254 cycle: verified, excursion [{lo},{hi}]")

# Agent 2's phase-5 glider is period 9 with net +1 and a permanent lower
# bound far to the right of Agent 1's window.
g = {}
for z, v in [(-2, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]:
    g[z] = v
q, sq = 0, 1
start2 = (q, sq, tuple(g.get(q + i, 0) for i in range(-2, 3)))
for k in range(9):
    w, d, ns = A2[sq][g.get(q, 0)]
    g[q] = w
    q += d
    sq = ns
assert q == 1
assert sq == start2[1]
assert tuple(g.get(q + i, 0) for i in range(-2, 3)) == start2[2]
assert p2 > 5
print("Agent 2: period-9 +1 glider, minimum position", p2 - 2)

assert all(tr is None or tr[2] in (1, 2) for row in A1[1:] for tr in row)
print("Agent 1 halt row unreachable: verified")
print("RESULT: period-9 pair is non-halting; collision impossible.")
