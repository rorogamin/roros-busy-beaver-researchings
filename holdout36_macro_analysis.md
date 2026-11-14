# BB(2,5) holdout `1RB2LA1LA4RA2LA_0LA3RB3LB2RB---` — macro structure and invariant test

Position in the lists: index 36 (0-based) of `Bb2x5_informalLast37.txt`; row 35 of
`audit36_likely_halting.md` ("no decisive local note; 10^10 survival only"). The
local wiki snapshot `corpus/knowledge/wiki/pages/Main/BB(2,5).wiki` lists it as
`undecided`, "1D CA-like". It is not one of the 22 machines with unofficial Lean
proofs. No halt is known up to ~10^10 raw steps (`deep_37_1e10/summary.txt`).

## The machine

```
     0      1      2      3      4
A   1RB    2LA    1LA    4RA    2LA
B   0LA    3RB    3LB    2RB    ---
```

`B4` is the only undefined transition, so **the machine halts iff a B-state head
ever reads a 4**.

## Local structure: a one-dimensional billiard

Both states move in a direction determined by the symbol read, and rewrite the
symbol they leave behind:

| state | moves right on | moves left on | writes |
|---|---|---|---|
| A | 0, 3 | 1, 2, 4 | 0→1, 1→2, 2→1, 3→4, 4→2 |
| B | 1, 3 | 0, 2 | 0→0, 1→3, 2→3, 3→2, 4→halt |

So the head is a particle in a fixed "direction field", and each visit rewrites
the cell, changing the field for later visits. This is the 1D-CA character the
wiki records.

Three consequences drive everything:

1. **4s have exactly one source and one sink.** A on a 3 writes 4 and moves
   right (`A3`); A on a 4 writes 2 and moves left (`A4`). B never writes a 4.
2. **A's rightward motion is a run over 3s.** `A3` leaves 4s behind and keeps
   going right. If the run ends on a 3 it continues; if it ends on 1, 2 or 4, A
   turns left and immediately eats the 4-run it just made; if it ends on 0, A
   writes 1 and hands over to B, and only then does a 4-block survive.
3. **B is a pure reader of 4s.** Its rightward runs pass 1s and 3s (writing 3, 2)
   and are turned by 2 or 0; its leftward runs pass 2s (writing 3) and are turned
   by 1 or 3. A 4 anywhere on a B path halts the machine.

## Growth law

The tape span grows like the square root of the step count, i.e. the machine
behaves like a two-sided sweep that costs O(span) per new cell (quadratic total
runtime):

| steps | span | 4/3·√steps |
|---:|---:|---:|
| 200 000 | 590 | 594 |
| 500 000 | 939 | 940 |
| 2 000 000 | 1 887 | 1 881 |
| 20 000 000 | 5 984 | 5 948 |

This is measured, not assumed; it matches the "bouncer with a growing middle"
picture and rules out a small cycle.

## Candidate invariant, and the empirical test

For a halting proof it is enough to show that a B-state head never sits on a 4:

```
Inv: state A at p  =>  every 4 is at a position <= p
     state B at p  =>  every 4 is at a position <  p
```

(zipier form: A has no 4 strictly right of the head; B has no 4 at or right of
the head.)

`tools/invariant25.py` checks this at every step. Over 20 000 000 steps
(11 443 393 A-steps, 8 556 607 B-steps) it held with no violation and no halt.
A second run over 5 000 000 steps measured the shape of the dynamics:

* at most **2** 4s exist simultaneously at any time;
* A never moves right twice in a row (longest rightward run = 1);
* B's longest rightward run is 49;
* B makes 374 296 leftward moves, of which 25 957 are chained (preceded by a
  leftward move);
* B leftward steps landing on a cell whose left neighbour is a 4: **0**.

So the invariant is true along the orbit, and the safety condition is exactly
"B never walks left into a 4".

## Why the obvious induction fails

`Inv` is **not inductive**. The smallest counterexample (found by exhaustive
search over configurations of tape length 1; `Inv` holds, the step breaks it):

```
lft = [4], hd = 2, rgt = [], mode = B
  --B2-->  lft = [], hd = 4, rgt = [3], mode = B      (next read halts)
```

`B2` reads a 2, writes 3 and steps **left**; the new head comes from the left
stack, which the invariant does not constrain (4s are allowed to the left of a
B head). So `Inv` alone cannot be preserved by `B2` (or by `B0`, which also steps
left). This is exactly the 1D-CA difficulty: the safety of B's leftward move
depends on how the 2-chain it is walking along was built, not on the current
invariant.

The protection is dynamical, not local: a surviving 4 is always created at the
end of an A rightward run that terminated on a blank, so the 4 is immediately
left of a 1 written by `A0`; B bounces off that 1 (`B1` moves right) and off the
3 it becomes (`B3` moves right), and only a chain of 2s reaching the 4 could
carry B onto it. Chained 2s do occur (25 957 times), but never adjacent to a 4
in 5 000 000 steps. Proving that needs an invariant coupling the A-phase (which
4-block is alive) with the B-run trail — the natural next target.

## Status

Open. This pass establishes the exact macro rules, the √t growth law, the
candidate invariant and its empirical validity, and a concrete refutation of its
inductiveness. No non-halting proof is claimed, and nothing here should be
recorded as solved.

An earlier Rocq file in this pass encoded `A3` as `4RB` and `B2` as `3LA`
(misreading `<write><move><state>` as `<write><state>`); its `Eval` cross-check
disagreed with the reference simulator, so the file and its `.vo` were deleted.
The corrected rules are the table above. Rocq 9.1 and Lean 4 are both installed,
so a formalization is feasible once a strengthened invariant is found.

## Tools added

* `tools/trace_extremes.py` — head-at-new-extreme tracer.
* `tools/macro25.py` — run-length tape dump at extremes, with run-level diffs.
* `tools/sweep25.py` — turnaround census and L-event suffix (stack) test.
* `tools/invariant25.py` — prints the parsed table and checks `Inv` per step.
