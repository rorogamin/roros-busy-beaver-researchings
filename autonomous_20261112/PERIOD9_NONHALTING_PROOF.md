# Period-9 CET(3) pair: post-exit analysis

Date: 2026-11-12.

Tables:

    A1 = 1LB---_1LC1RB_0RB0LC
    A2 = 1RB0LA_0RC0LA_1LB1RC

The pair is a one-transition mutation of the verified CET(3) champion: A2's
`A1` entry is `0LA` here, versus `0LB` in the champion.  It was investigated as
a possible period-9 halting target.  The post-exit local trace and the period-9
glider are now checked exactly; a complete non-halting proof is **not** claimed,
because the needed Agent-1 support lemma is still open.

The executable check is

    python bbwork/autonomous_20261112/period9_nonhalting_verify.py

It exits 0 after printing `RESULT: exact exit/local trace and glider verified;
Agent 1 confinement remains an open proof obligation.`

## 1. Exit configuration

The verified counter lemma for L1 = 70 gives

    P(70) = 2^72 - 74
    t_exit = 673 + P(70) = 2^72 + 599
           = 4,722,366,482,869,645,214,295

with

    pos1 = 69, state1 = B
    tape[-1..68] = 1, tape[-2] = 0, tape[69] = 0
    pos2 = 524,707,386,985,516,134,924, phase q = 5.

The first ten Agent-1 transitions are deterministic and local:

| step | head after | state | written |
|---|---|---|---|
| 1 | 68 | C | tape[69]=1 |
| 2 | 67 | C | tape[68]=0 |
| 3 | 66 | C | tape[67]=0 |
| 4 | 65 | C | tape[66]=0 |
| 5 | 64 | C | tape[65]=0 |
| 6 | 63 | C | tape[64]=0 |
| 7 | 62 | C | tape[63]=0 |
| 8 | 61 | C | tape[62]=0 |
| 9 | 60 | C | tape[61]=0 |
| 10 | 59 | C | tape[60]=0 |

After step 10:

    pos1 = 59, state1 = C
    tape[-1..59] = 1
    tape[60..68] = 0
    tape[-2] = 0.

This much is a finite computation and is checked by the verifier.

## 2. Agent 1's halt row

Rows B and C of A1 never target A:

    B0 -> C, B1 -> B, C0 -> B, C1 -> C.

So A1, the only undefined entry, is unreachable once Agent 1 is in B or C.
Agent 1 cannot halt through its own table; the pair can only halt by a head
collision.

## 3. Agent 2: period-9 right-moving glider

Agent 2 at exit is at the huge position

    pos2 = 524,707,386,985,516,134,924

in the right-moving phase-5 configuration

    head B at 0, tape[-2..2] = 0,1,1,1,0.

Its local configuration repeats every 9 steps, translated one cell to the
right:

    period = 9, net displacement = +1,

with a left excursion of at most two cells.  The verifier finds the cycle and
confirms

    min pos2 = 524,707,386,985,516,134,922 > 66.

This is a complete local proof that Agent 2 stays far to the right of 66,
independent of Agent 1.

## 4. The missing Agent-1 support lemma

What is not proved is that Agent 1 stays to the left of Agent 2 forever.  The
natural first attempt -- a "two-zero barrier" -- is **false** and is retracted:

* on a zero, `C0` moves right into the second zero in state B;
* `B0` there writes 1 and moves back left;
* but a later `C0` can enter that 1 in B and `B1` can then move right again.

A zero gap is therefore not an impenetrable wall.  A direct simulation from the
all-zero tape confirms that Agent 1 can write through an infinite zero region
(it reached position 16-18 before turning back in 10^6 steps).

### New macro result: the wall is crossed, but Agent 2 escapes

Agent 1 is not trapped at the left.  On a wall of zeros with the first 1 at
position W, the crossing time is exactly

    T_cross(W) = 2^(W+3) - (W+3),

checked for W = 4..26 (C) and W = 4..12 (Python macro verifier).  For the
actual wall W=69 this is

    2^72 - 72 = 4,722,366,482,869,645,213,624

steps from the post-erase start.  At the crossing Agent 1 is in state B on a
one and `B1` runs right through the glider's one-trail at one cell per step.

It reaches the trailing zero of the glider before the head:

    ... 1 1 0 [B] 1 ...

so `B0` writes 1 and moves left.  In the local encounter check (1000-cell
one-run, phase-5 glider) there is no collision; Agent 1 is deflected left and
Agent 2 ends in state C on a solid one-run.  `C1 = 1RC` then moves Agent 2
right one cell per step forever.  Agent 1 cannot catch a target moving at the
maximum speed to the right.

This is the macro non-halting picture.  The formula above is verified only on
the finite W ladder, so the W=69 instance is an extrapolation; a full symbolic
crossing lemma is still the formal gap.

What the corrected simulations do show is much weaker than a proof:

    post-exit horizon     final pos1     max pos1
    5,000,000             -1 (B)         59
    500,000,000           -1 (B)         69 (the exit position)

After step 10 the head goes left, erases the one-run down to -1, and appears to
be trapped in the two-cell zero pocket at -2/-1.  It never returns to 59 in the
finite runs.  This is strong evidence that the pair is non-halting, but it is
not a symbolic confinement theorem.

## 5. Status

**Update (2026-11-12): closed.**  The wall-crossing branch is unnecessary.
After the exit block is erased, Agent 1 reaches position -1 in state B on an
all-zero local tape, enters a period-254 fixed cycle confined to [-2,5], and
leaves the lone residue at 69 inert.  Agent 2 is the period-9 +1 glider with
minimum position 524,707,386,985,516,134,922.  See
`PERIOD9_CLOSED.md` and `period9_close_verify.py` (exit 0).

* Exact exit arithmetic and the first ten local steps: verified.
* Agent 1 cannot enter its halt row: verified.
* Agent 2 is a period-9 right-moving glider with a permanent lower bound:
  verified locally.
* Agent 1's global right support: **open**.
* Halting proof: **none**.
* Completed non-halting proof: **macro/certificate, not Rocq**.

The correct conclusion for now is that this candidate behaves like a
non-halting holdout, not like the period-9 halting machine that was originally
sought.  Any claim of a completed proof would need the support lemma in
Section 4, which is exactly where the earlier barrier argument failed.
