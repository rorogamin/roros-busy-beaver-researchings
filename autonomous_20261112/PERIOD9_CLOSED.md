# Period-9 CET pair: closed non-halting proof

Date: 2026-11-12.

Tables:

    A1 = 1LB---_1LC1RB_0RB0LC
    A2 = 1RB0LA_0RC0LA_1LB1RC

The earlier wall-crossing argument is no longer needed.  The post-exit tape
has no wall of ones at W=69: the only right-hand one is the remote Agent-2
glider.  Agent 1 erases its finite block, enters a fixed local cycle, and can
never meet Agent 2.

## 1. Exit

The verified counter exit is

    P(70) = 2^72 - 74
    t_exit = 673 + P(70) = 2^72 + 599
           = 4,722,366,482,869,645,214,295

with

    pos1 = 69, state1 = B
    tape[-1..68] = 1, tape[-2] = 0, tape[69] = 0
    pos2 = 524,707,386,985,516,134,924, phase q = 5.

## 2. Agent 1 reaches a fixed cycle

The first ten steps from the exit are deterministic.  After step 10:

    pos1 = 59, state1 = C
    tape[-1..59] = 1, tape[60..68] = 0, tape[69] = 1.

Then 62 further steps erase the remaining block and leave

    pos1 = -1, state1 = B
    tape[x] = 0 for every x in [-20,68];

the lone one at 69 is left behind and is outside all later head excursions.

One more step gives the cycle entry

    pos1 = -2, state1 = C.

From there the local configuration repeats with period **254**, and during
the whole period the head stays in

    [-2, 5].

The repeating window is the radius-6 window around the head; the period-254
return is exact.  The inert one at 69 is never read.

## 3. Agent 2 escapes

At the exit Agent 2 is the phase-5 period-9 glider

    head B, tape[-2..2] = 0,1,1,1,0,

which repeats every 9 steps with net displacement +1.  Its minimum possible
position is

    524,707,386,985,516,134,922,

far to the right of Agent 1's window [-2,5].  It moves only right, so the
distance never closes.

## 4. Halt row

Agent 1's rows B and C only target B and C; row A is the only undefined row
and is unreachable.  Agent 1 cannot halt individually, and the CET halt event
is a collision.

## 5. Conclusion

Agent 1 is permanently confined to [-2,5], Agent 2 remains at position at
least 524,707,386,985,516,134,922, and neither can reach the other.  The
period-9 pair is **non-halting**.

This is a finite local certificate, not a Rocq theorem: the exit arithmetic
is the previously verified counter lemma, and the post-exit 62+1+254 steps
plus the period-9 glider are checked by `period9_close_verify.py`.

Verifier:

    python bbwork/autonomous_20261112/period9_close_verify.py

It exits 0 with:

    RESULT: period-9 pair is non-halting; collision impossible.
