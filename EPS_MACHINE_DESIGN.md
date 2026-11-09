# Building our own eps-machine

A 2-symbol machine assembled from the analysis in `EPSILON_ANALYSIS.md`, with the
first module implemented and checked. The design goal is not a record — it is a
machine whose every part is understood well enough to state a loop invariant for.

## What has to be true for the rung

From the analysis, the rungs are separated by *where the iteration count comes
from*:

* count in the control → fixed level;
* count read off the tape → one rung up;
* **the length of a block re-read as the number of rounds of an inner engine** →
  the eps mechanism.

So the machine needs one primitive: **copy a block, with an append count**. With
append 2 it doubles; with append 1 it copies. Everything else is bookkeeping.

## Module K (built and checked)

`tools/eps_machine.py`, 7 states, operates on

```
    1^x 0 1        source block, one blank, a seeded destination of one mark
```

and halts on

```
    0^x 0 1^(2x+1)
```

Checked for x = 1…6 by exact tape comparison, not by counting:

```
x=1 steps=10 marks=[2,3,4]          x=4 steps=73 marks=[5..13]
x=2 steps=25 marks=[3..7]           x=5 steps=106 marks=[6..16]
x=3 steps=46 marks=[4..10]          x=6 steps=145 marks=[7..19]
```

The step count is `2x^2 + 5x + 3`-ish (measured 10, 25, 46, 73, 106, 145 —
differences 15, 21, 27, 33, 39, so quadratic, as expected for a walk that
re-traverses the growing destination once per source mark).

Two lessons already paid for:

* **the destination must be seeded.** With an empty destination, "skip blanks to
  the destination" has no stopping point. One seed mark costs one mark and one
  bookkeeping step on read-back.
* **append before erasing.** The first version erased, then tested, so the last
  source mark was destroyed uncopied and every answer was `2x-1` instead of
  `2x+1`. The current table appends, erases, *then* tests.

## The drive: c rounds read off the tape

Lay out `1^c 0 1^x 0 1` (rounds, value, seed) and consume one `c` mark per round:

```
round:  erase one c mark; run K on (x, seed)
halt:   when the c block is empty
value:  x * 2^c
```

State cost: K (7) + drive (about 6: erase, walk to the source, test, return) +
boot (about 6) ≈ 19 states. This is the "the tape's length drives the rounds"
rung — still `f_2`-shaped, but with the count genuinely on the tape.

## The feedback: re-read the block (the eps step)

After the rounds, the value block is `2^c`-ish. The eps move is to **copy the
value block into the `c` field**, so the next phase's round count is the previous
phase's output:

```
x_{k+1} = 2^{x_k}        -> towers, i.e. omega^^
```

Copying is K with append 1 (same walk, one fewer append state). Cost ≈ 8 states,
so the tower machine is ≈ 27 states. Adding a second counter that counts the
feedback rounds gives `omega^^k` for a k read from the tape; letting *that*
counter be re-read as well is the step to eps_0.

## What is designed, and what is checked

| piece | status |
|---|---|
| K: append-2 copy, source consumed | **checked**, x = 1…6, exact tapes |
| drive: c rounds | designed (table sketched above) |
| feedback: value -> round count | designed (K with append 1) |
| tower machine (~27 states) | designed, not built |
| eps machine (feedback on the feedback) | designed, not built |
| loop lemma / descent proof | not started; needs `tools/eps_engine.py` |

Honest calibration: the census reaches `omega^^6` in 33 states, so a ~27-state
tower machine is not competitive — it is *legible*. That is the point: the
census's machines are analysed after the fact, and this one is meant to be
provable from the start. Until the drive and feedback are built and checked, the
claim is "module K works", not "we have a tower machine".

## Next concrete step

Implement the drive on top of K: boot `1^c 0 1 0 1`, one mark of `c` consumed per
round, halt when `c` is empty, and check that the value block is `2^c` for
c = 1…5 by exact tape comparison. That is a small, decisive test: it exercises
every state transition except the feedback copy.

## Rocq status

`rocq/ModuleK.v` now carries the symbolic half: the gap walk, the destination
sweep (both directions) are proved for every length, and the file compiles with
three `Print Assumptions` clean.  The append composition and the gap-and-erase
walk are written out in the file as comment statements but not proved, so the
round is *checked numerically* (`tools/kcheck.py`: `rounds: PASS`,
`totals: PASS` for x = 1..7) and *not yet* closed symbolically.  Calling that a
proof of the module would be wrong.

## The tower machine, running

`tools/tower_machine.py` is the drive layer, built and checked: 12 drive states
plus module K's 7, no boot.  On `1(wall) 1^c 0 1^v 0 1` it consumes one c mark
per round and doubles-plus-one the value, so after c rounds the value is
`(v+1)*2^c - 1`.  `c=1..3, v=1..3` all halt with the exact count (33, 55, 83,
122, 220, 348, 393, 765, 1263 steps).

Two design facts the build paid for:

* the seed must sit one blank beyond the block.  Adjacent, the next round's walk
  runs over it and takes block+seed as the source, turning `v -> 2v+1` into
  `v -> 2v+3` -- the count came out short and the trace looked fine otherwise;
* the return walk needs a wall.  With `c = 1` the c block empties, and without
  the wall the head walks off into blank tape and never halts.

A trailing seed is written after the last round, so the value is read as
`marks - wall - seed`.  Still a `2^c` machine: the eps_0 rung needs the value
block re-read as the round count, which this drive does not do.
