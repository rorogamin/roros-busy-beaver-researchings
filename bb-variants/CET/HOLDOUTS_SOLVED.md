# CET(4) holdouts solved by short-period glider certificates

All non-halting CET(4) candidates in `all_holdouts_cet4.txt` were tested for
translated local cycles on a radius-12 window around each head.

## Result

* **53,073** candidate lines have a nonzero-displacement short translated
  local cycle (period at most 9, radius-12 window), verified by
  `scan_period_small_all.c`; a further **44** are solved by the larger
  period-32/radius-40 scan.
* **1,657** more have a zero-displacement fixed cycle (period at most 9,
  radius 12), verified by `scan_fixed_all.c`; a further **39** are solved by
  the period-128/radius-160 fixed scan.
* The union is **54,813 of all 54,828**, in
  `solved_holdouts_combined3.txt`; only **15** remain.
* **29,602** of those are already one-step cycles, verified independently by
  `scan_period1_all.c`; that subset is `solved_holdouts_period1_all.txt`.
* The first-100 list with the transient time, displacement, position, and
  table is `solved_holdouts_period1.txt`; the first-500 list is
  `solved_holdouts_period1_500.txt`.
* `solved_holdouts_gliders.txt` records 20 earlier certificates with a wider
  finite-tape translation check.
* All 100 of the first 100 now have a local cycle; 58 have a period-1
  nonzero-displacement cycle.
* With a radius-12 window and periods up to 9, **482 of the first 500** pass
  the short-period certificate scan (`scan_period_small.py`, results in
  `solved_holdouts_small_500.txt`).  The radius exceeds the maximum head
  excursion, so the cycle is local; a virgin zero frontier is required in the
  direction of motion.  These are finite local certificates, not Rocq proofs.

## Certificate for line 0

Line 0:

    A1 = 1RA0LD_0LA0RA_0RD0RB_1LD0LB
    A2 = 0RD1LB_0RD1LA_1LB1RB_0RD1RC

Start: A1 in A at 0, A2 in A at 2, blank tape.  At step 2:

    p1=2, p2=4, states (A,D)
    cells around p1: 1 1 0 0 0
    cells around p2: 0 0 0 0 0

One step later:

    p1=3, p2=5, states (A,D)
    cells around p1: 1 1 0 0 0
    cells around p2: 0 0 0 0 0

The 5-cell window has translated with the heads by one cell, the states and
the distance are unchanged, and there is no collision.  Repeating this step is
a valid local glider, so line 0 is non-halting.  The other entries in the
first-100 list are checked by the same script.

## Scope

These are finite local certificates: a short cycle whose window is unchanged
and whose heads move together.  They are not Rocq theorems and have
not been submitted upstream.  All of the first 100 are covered; the 15
outliers are not claimed.
The full scan is exhaustive for the short-period certificates only.  The
remaining 15 candidate lines need a longer-period local invariant or a separate
argument; they are not claimed solved by this scan.
