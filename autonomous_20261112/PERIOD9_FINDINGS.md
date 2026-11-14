# Period-9 CET pair: findings

Date: 2026-11-12.

## Tables

    A1 = 1LB---_1LC1RB_0RB0LC
    A2 = 1RB0LA_0RC0LA_1LB1RC

A2 is the CET(3) champion's table with one entry changed: `A1 = 0LA` instead of
`0LB`.  This is the period-9 mutation that was under investigation.

## Verified

* Exit from the clean L1=70 counter:

      P(70) = 2^72 - 74
      t_exit = 2^72 + 599 = 4,722,366,482,869,645,214,295
      pos1 = 69 B, tape[-1..68]=1, tape[-2]=0, tape[69]=0
      pos2 = 524,707,386,985,516,134,924, phase q=5.

* The first ten Agent-1 steps erase 60..68 and put the head at 59 C with
  tape[-1..59]=1, tape[60..68]=0.  See `period9_nonhalting_verify.py`.

* Agent 1 cannot reach its halt row A; B/C transitions never target A.

* Agent 2 is a period-9 right-moving glider in the phase-5 local configuration
  `head B, tape[-2..2]=0,1,1,1,0`.  Its local pattern repeats every 9 steps with
  net +1, and its minimum position is 524,707,386,985,516,134,922.

## Open

Agent 1's global right support is not proved.  The earlier "two-zero barrier"
argument is false: Agent 1 can enter a zero gap, write a 1 at the second zero,
and later use `B1` to move right again.  A direct all-zero-tape test reaches
position 16-18 before turning back, confirming that a zero gap is not an
impenetrable wall.

## New: Agent 1 is not trapped at the left; it is a slow wall-crossing counter

Starting from `C` at -2 on `0^69 1^inf`, Agent 1 does not stay at the wall.
It builds a growing one-block and crosses the first one at

    T_cross(W) = 2^(W+3) - (W+3)

(checked exactly for W = 4..26; W=26 crosses at 536,870,883 = 2^29 - 29, and
W=27 does not cross before 10^9).  For the actual wall W=69 the predicted
crossing time is

    2^72 - 72.

At the crossing the head is in state B on a one and then `B1` runs right at one
cell per step through the glider's one-trail.  This invalidates the earlier
finite-run statement that Agent 1 simply dies in the -2/-1 pocket: the finite
horizons used were far below 2^69.

What happens at the glider is the current open point.  The glider's tail has a
zero two cells behind its head; a B-run reaches that zero first, `B0` writes 1
and moves left, and in scaled tests it is deflected left without a collision.
That suggests the pair is still non-halting, but the deflection/re-entry cycle
has not been proved.

Finite corrected runs from the exit:

    5,000,000 steps:   final pos1=-1 B, max pos1=59
    500,000,000 steps: final pos1=-1 B, max pos1=69 (exit position)

These horizons are below the predicted crossing time 2^72-72 and therefore do
not decide the post-wall behaviour.

The head appears to be trapped in the -2/-1 zero pocket after erasing the
one-run, but that is evidence, not a symbolic theorem.

## Status

The macro picture is now non-halting:

1. Agent 1's wall crossing is a doubling counter; checked exactly for W=4..26,
   the formula is `T_cross(W)=2^(W+3)-(W+3)`.  For W=69 it crosses at
   `2^72-72`.
2. At the crossing it is B on a one and runs right through the one-trail.
3. It reaches the glider's trailing zero first; `B0` turns it left.  A local
   check (1000 cells of one-run, phase-5 glider) shows no collision and leaves
   Agent 2 in state C on a solid one-run.
4. `C1 = 1RC` then moves Agent 2 right at one cell per step forever; Agent 1 is
   left behind.

So this candidate is a **non-halting holdout**, not a halting period-9 machine.
The remaining formal gap is the symbolic W=69 crossing (the formula is verified
only for the finite W ladder), so the result is a macro proof plus finite
certificate rather than a Rocq theorem.  It should not be listed as a proved
non-halting machine until that symbolic lemma is written out.

## Corrections to earlier notes

* The earlier claim of Agent-1 excursions to roughly P/2 came from a buggy
  post-exit tape with `tape[68]=0`; it is void.
* The hand-built phase-5/gap-8 collision block used the wrong right-hand tape
  and is void.
* The earlier "complete non-halting proof" in this directory was based on the
  false two-zero barrier; it has been replaced by the analysis above.
