"""Finite local analysis of the period-9 CET pair.

Tables:
    A1 = 1LB---_1LC1RB_0RB0LC
    A2 = 1RB0LA_0RC0LA_1LB1RC

This script checks:
  * the first ten Agent-1 steps from the exact counter exit;
  * the local shape after those steps;
  * the first 5,000,000 post-exit steps for Agent 1 (finite evidence only);
  * that Agent 1 cannot reach its halt row A;
  * that Agent 2's phase-5 local pattern is a period-9 right-moving glider.

It does NOT prove that Agent 1 remains bounded forever.  The earlier
"two-zero barrier" argument was wrong: Agent 1 can enter and write through a
zero gap.  A completed non-halting proof still needs a support lemma for
Agent 1.  Do not read the finite run below as that lemma.
"""

A1 = [
    [(1, -1, 1), None],          # A: 1LB, ---
    [(1, -1, 2), (1, +1, 1)],    # B: 1LC, 1RB
    [(0, +1, 1), (0, -1, 2)],    # C: 0RB, 0LC
]
A2 = [
    [(1, +1, 1), (0, -1, 0)],    # A: 1RB, 0LA
    [(0, +1, 2), (0, -1, 0)],    # B: 0RC, 0LA
    [(1, -1, 1), (1, +1, 2)],    # C: 1LB, 1RC
]

# 1. Exact exit tape: ones on [-1..68], zero at 69, ones to the right.
tape = {x: 1 for x in range(-1, 69)}
tape[-1] = 1
tape[69] = 0
for x in range(70, 100):
    tape[x] = 1
tape[-2] = 0
p, s = 69, 1
print("exit: pos=69 state=B, tape[-1..68]=1, tape[69]=0")

# 2. First ten deterministic steps.
maxpos = p
for k in range(1, 11):
    w, d, ns = A1[s][tape[p]]
    tape[p] = w
    p += d
    s = ns
    maxpos = max(maxpos, p)
    print(f"step {k:2d}: pos={p:3d} state={'ABC'[s]} "
          f"tape[57..70]={''.join(str(tape.get(x, 0)) for x in range(57, 71))}")
assert (p, s) == (59, 2), (p, s)
assert [tape[x] for x in range(60, 69)] == [0] * 9
assert [tape[x] for x in range(-1, 60)] == [1] * 61
print("first ten steps: VERIFIED")

# 3. Finite post-exit support check.  This is evidence, not a proof.
for x in range(-2, 70):
    if x not in tape:
        tape[x] = 0
for x in range(70, 100):
    tape[x] = 1
p, s = 59, 2
mx = p
for k in range(1, 5_000_001):
    w, d, ns = A1[s][tape[p]]
    tape[p] = w
    p += d
    s = ns
    mx = max(mx, p)
print(f"5,000,000 post-exit steps: final pos={p} state={'ABC'[s]} "
      f"max={mx} (finite check only)")
assert mx <= 69
print("bounded support over the finite horizon: OBSERVED (not proved)")

# 4. Agent 1 cannot reach A.
assert all(tr is None or tr[2] in (1, 2) for row in A1[1:] for tr in row)
print("Agent 1 halt row A unreachable: VERIFIED")

# 5. Agent 2 at exit is the right-moving phase observed in the scaled run:
#    head B on 1 with local ...0,1,1,1,0.  Its local pattern repeats every 9
#    steps, translated one cell right.
tp = {x: 0 for x in range(-20, 100)}
tp[-2] = 0
tp[-1] = 1
tp[0] = 1
tp[1] = 1
tp[2] = 0
p2 = 524707386985516134924
for z, v in tp.items():
    tape[p2 + z] = v
pos = p2
state = 1
minpos = pos
seen = {}
for k in range(0, 1000):
    key = (state, tuple(tape.get(pos + z, 0) for z in range(-10, 11)))
    if key in seen:
        t0, pos0 = seen[key]
        period = k - t0
        net = pos - pos0
        print(f"Agent 2 glider cycle: period={period}, net={net}, "
              f"start={pos0}, end={pos}, min={minpos}")
        assert period == 9, period
        assert net == 1, net
        break
    seen[key] = (k, pos)
    w, d, ns = A2[state][tape[pos]]
    tape[pos] = w
    pos += d
    state = ns
    minpos = min(minpos, pos)
else:
    raise AssertionError("glider did not cycle")
assert minpos > 66
print("Agent 2 period-9 right glider: VERIFIED")

print("RESULT: exact exit/local trace and glider verified; "
      "Agent 1 confinement remains an open proof obligation.")
