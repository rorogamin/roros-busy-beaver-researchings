# Machine 15: the 42-bit block and the H..O outer carry

Status 2026-11-11.  This is a **decode of the continuation variant**, not the
`f_{w*2}(13)` value proof.
The local H..O rules are read off the literal table, checked on the run, and
verified in `rocq/Machine15Outer.v`; the parametric and exact 42-bit rounds
are in `rocq/Machine15Round.v`.  The global FGH layer is still open; see the
last section.

## 1. The 42-bit block

At 2,000,000 steps the non-blank tape is

```
1^2440 0 1^755 0 1^32 0 1 0 (11 0)^10 11 0^2
1^40 0 1 0 (11 0)^11 11 0
```

with the runs

```
output 1^2440, fuel 1^755, level 1^32,
[1, 2^11]  0^2  40  0  1  0  [1, 2^12]
```

so the two 13-field blocks are `[level,1,2^11]` (level 32 at 2M, 34 at the
start) and
`[1,2^12]`, separated by the 40-run.  At 50,000,000 steps the same structure
is present with level 31 and `output = 12960`, `fuel = 2221`; the run is
still the base level.

The **42-bit block** is the 42 cells

```
1^40 0 1
```

at indices `[-76,-35]`: forty ones, the separator 0 at `-36`, and the 1 at
`-35`.  Its **last four bits** are `1101 = 13`; its first four are `1111`.
The earlier note that the code "begins" with 1101 is corrected: 1101 is the
**suffix**, the binary 13 at the block boundary.  The twelve `11` pairs
after the block are the remaining twelve fields of the second 13-field block;
the 1 at `-35` is the first of the thirteen, and the twelve `11` pairs are
the remaining twelve.

## 2. The H..O instruction table

States: A=0, ..., H=7, I=8, ..., O=14.  The H..O rows are

| state | read | write | move | next | role |
|---|---|---|---|---|---|
| H (7) | 0 | 1 | R | F (5) | end of carry, return to the inner loop |
| H (7) | 1 | 0 | R | O (14) | start the loop: write the separator 0 |
| O (14) | 0 | 1 | R | H (7) | write 1, move right, continue into next field |
| O (14) | 1 | 1 | R | M (12) | write the prefix 1, enter the triple |
| M (12) | 0 | 0 | L | A (0) | end of a run |
| M (12) | 1 | 0 | R | N (13) | triple cell 1: write 0 |
| N (13) | 0 | 0 | L | A (0) | end of a run |
| N (13) | 1 | 1 | R | O (14) | triple cell 2: write 1 |
| O (14) | 1 | 1 | R | M (12) | triple cell 3: write 1, repeat |

The return states are

| state | read | write | move | next |
|---|---|---|---|---|
| A (0) | 0 | 1 | L | H (7) |
| A (0) | 1 | 0 | L | G (6) |
| G (6) | 0 | 1 | L | A (0) |
| G (6) | 1 | 1 | L | G (6) |
| F (5) | 0 | 1 | R | B (1) |
| F (5) | 1 | 1 | R | F (5) |

The key point: the machine does not "read" the 42 bits as a stored program
in a separate instruction stream.  The **40 ones themselves are the loop
body**; the 0 is the continuation cell; the 1 is the first result cell.

The I..L states (8..11) are the inner counter's left-side pair; they do not
appear in the 40-block writer, which runs H/O/M/N with A/G/F.

## 3. The macro rules

Written as rewrites on the local tape, with the head at the leftmost cell of
the pattern:

```
H on 1, next 1:       1 1        ->  0 1        (head +2, state M)
M/N/O on 1 1 1:       1 1 1      ->  0 1 1      (head +3, state M)
H on 1^(3k+2):        1^(3k+2)   ->  0 1 (0 1 1)^k
M on 1^(3k):          1^(3k)     ->  (0 1 1)^k
```

The first rule is the entry: H consumes the first 1 and writes 0, O consumes
the second and writes 1, and M starts the triple.  The second is the loop:
each group of three ones becomes one `11` token with a 0 separator to its
left.  The third is the closed form of the entry; the fourth is the closed
form of the loop from M.

The **40** is `2 + 3*12 + 2`.  The entry consumes two cells (`0 1`), twelve
triples consume thirty-six, and the last two cells are the boundary pair
`0 1`; the output is `0 1 (0 1 1)^12 0 1`.  The 0 of the final pair is the
continuation cell; the 1 is the first cell of the next block.  The twelve `11`
pairs plus that 1 are the thirteen fields of the second block.  The 40-run
is therefore the **unary loop count 13** in the form `3*13+1`, and the
binary 13 is its last four bits.

The first field of the first block is the level counter: 34 at the start,
32 at 2M, 31 at 50M.  It is decremented once per level and is not a second
copy of the 40.  Its 13 fields are the counter, the 1, and the eleven `11`
pairs; the counter's own unary length is not a fixed token block.

## 4. Evidence

**The entry, from the level-1 tape.**  The natural 50M run never reaches the
outer boundary; it is still at level 31.  To exercise the boundary I ran to
2M, shortened the level field from 32 to 1 (a valid configuration, not a
blank-tape run), and traced the writer.  The first H..O entries are at
absolute step 8,004,939:

```
t=8004939  H h=-5608 r=1 -> 0 R O
t=8004940  O h=-5607 r=1 -> 1 R M
t=8004941  M h=-5606 r=1 -> 0 R N
t=8004942  N h=-5605 r=1 -> 1 R O
t=8004943  O h=-5604 r=1 -> 1 R M
t=8004944  M h=-5603 r=1 -> 0 R N
...
```

so the local tape becomes `0 1 0 1 1 0 1 1 0 ...` as the head moves right.
In the 20,000-step window there are 5,607 H..O entries, of which **1,839**
are the exact M(1)/N(1)/O(1) triple at heads `h, h+1, h+2` with writes
`0,1,1`; the three non-triples are the end-of-run cases M(1)/N(0), the
boundary, not errors.  The same window reaches the level cell at `-144` and
the A/G return at `-145`.

**The synthetic checks** (`tools/_decode15_semantics.py`):

```
single 1 at H:        after 2 steps, bits 01, head 2; O0 enters H
triple 111:           after 3 steps, bits 011, head 3, state M
1^3k -> (011)^k:      k = 1,2,3,13 all exact
H on 1^(3k+2):        k = 1,2,3,12 gives 01(011)^k, state M
H on 1^40:            the 40-cell rewrite is exact; the continuation row
                      then enters H on the following cell
```

The 40 result is the exact boundary form: twelve triples and the final
`0 1` pair, then the continuation.  The 0 is the program's continuation cell;
the row writes 1 there, moves onto the 1 after it, and enters state H.  That
1 is the first field of the next block.

## 5. Rocq

`rocq/Machine15Outer.v` verifies on the literal `tbl`:

* the eight single-cell H/O/M/N transitions;
* `triple_111`: `1 1 1 -> 0 1 1`, head +3, state M;
* `writer_13`: 39 ones (13 triples) become `(011)^13`;
* `entry_12`: H on 38 ones becomes `0 1 (011)^12`.

All are `vm_compute; reflexivity` and `Print Assumptions` is closed under the
global context.  These are local instruction lemmas, not the FGH value
theorem.

### 5.1 The symbolic round

`rocq/Machine15Round.v` proves the parametric form on the same literal `tbl`.
With `tok = 0 1 1` and `chain k = tok^k`:

* `writer_ctx`: for every `k` and left context `clft`, the run of `3*S k`
  steps from state `M` on `1^(3*S k)` ends in state `M` with left context
  `rev (chain (S k)) ++ clft`, head blank, right empty.  That is, `M` on
  `1^(3(k+1))` writes `(0 1 1)^(k+1)` in `3(k+1)` steps.
* `entry_ctx`: for every `k` and `clft`, the run of `3*k + 2` steps from
  state `H` on `1^(3*k + 2)` ends in state `M` with left context
  `rev ([0;1] ++ chain k) ++ clft`, head blank, right empty.  That is, `H` on
  `1^(3k+2)` writes `0 1 (0 1 1)^k` in `3k+2` steps.
* `round_13`: the 38-cell instance (`H` on `1^38`) writes
  `0 1 (0 1 1)^12` in 38 steps and leaves state `M`.
* `round_40`: `H` on `1^40` writes `0 1 (0 1 1)^12 0 1` in 40 steps and
  leaves state `O` on the next cell; `round_40_next` applies the
  continuation row, writing 1 and entering state H (7).
* `writer_ctx_suffix` / `entry_ctx_suffix`: the same two parametric results
  for an arbitrary left context `clft` and an arbitrary untouched suffix
  `crgt` after the written run.  The head ends on `hd bl crgt`, the suffix
  remains `tl crgt`, and the written cells are prepended to `clft`.
* `round_40_suffix`: for every left context `clft` and trailing tape `crgt`,
  `H` on `1^40 ++ crgt` writes `0 1 (0 1 1)^12 0 1`, ends in state `O` on
  `hd bl crgt`, leaves `tl crgt` untouched, and prepends the written cells
  to `clft`.  It splits `40 = 38 + 2` and uses the 38-cell entry plus the
  final `M 1`/`N 1` pair.
* `round_42`: for every left context `clft` and right field-stack context
  `crgt`, the exact 42-bit block `1^40 0 1` (`ones 39 ++ [0;1]` after the
  first head cell) followed by `crgt`.  After 40 steps the head is `O` on
  the 0 separator, the written 40 cells are prepended to `clft`, and the
  right context is `[1] ++ crgt`; `round_42_next` writes the separator 1 and
  enters H on the trailing 1, and `round_42_next_run` reaches that
  configuration in 41 steps.  `round_42_enter_field` crosses the next 0 and
  reaches the first 1 of the following field in 43 steps; the remaining
  fields stay in `rest`.  This is the complete local entry into the next
  13-field stack, with both surrounding stacks preserved.
* `output_growth_phase`: for every remaining field stack `rest`, 62 steps
  from the `round_42_enter_field` target finish the first field, sweep left
  through the 40-cell output with the A/G pass, and lay down the first new
  left block with F/B/C/D.  It ends in state H on the new blank, with an
  empty left context and the 52-cell `output_growth_prefix` followed by the
  untouched `rest`.  This is the complete first leftward output-growth
  phase; it is not an iteration over the remaining fields.

The parametric inductions use only the concrete `pair_ctx`/`triple_ctx` steps
and list arithmetic; the suffix round is symbolic, while the original
isolated `round_40` remains a concrete 40-step `vm_compute` check.  All 13
`Print Assumptions` are closed under the global context.  These are still
local writer lemmas: the initial tape is the block with arbitrary left and
right field-stack contexts, not the blank-tape orbit.

**Continuation variant.**  The original candidate row `14 0 1 R H` is a halt
(where `H` is the halt symbol).  The current candidate uses `14 0 1 R 7`, so
the same write/move enters state H; `Machine15.v`'s table matches it.  All 30
transitions are defined.  The 50M theorem remains closed; the local round
reaches H on the trailing 1 at 41 and the first field of the next stack at
43.  The original halt convention and its sentinel encoding are no longer
used.

## 6. What this does not prove

The decode is local and structural.  It does **not** establish
`f_{w*2}(13)`:

* the 50M natural run is still the base level; the outer boundary was
  reached only by the level-1 forcing, which is a valid machine
  configuration but not the blank-tape orbit;
* the 40's loop count 13 is read structurally; the `13^13` f_w-iterates are
  not generated or counted;
* there are still no `f_w` / `f_{w*2}` definitions or fundamental-sequence
  lemmas in `rocq/`; the exact 42-bit H..O round, including its continuation
  into the next field, is now local (`Machine15Round.v`), but it does not
  connect to the FGH value layer; `StackPass.v` is for Machine 5 and remains
  open.  Full processing of the remaining 12 fields of the next stack is not
  proved: a 5,000,000-step trace from the post-42 target never revisits the
  right stack after step 10 (the head is at most -31 after step 100), so the
  remaining fields stay untouched in that phase.  `output_growth_phase`
  proves only the first 62-step leftward sweep; it does not iterate the
  phase or consume those remaining fields.

The local round now exists (`writer_ctx`, `entry_ctx`, `round_13`, `round_40`,
`round_40_suffix`, `round_42`, `round_42_next`, `round_42_next_run`,
`round_42_enter_field`, `output_growth_phase`).  It starts at the 42-bit block with arbitrary left
and right field-stack contexts, not the blank-tape orbit.  The remaining gap
is
the full-machine/FGH value layer: definitions of `f_w` and `f_{w*2}`, the
fundamental-sequence lemmas, and the connection from this local pass to the
actual blank-tape orbit.
Until that exists, no ledger row.

## Files

* `tools/_decode15_outer.py` -- shortens the level field and traces the
  boundary.
* `tools/_decode15_outer_trace.py` -- H..O entry/exit window.
* `tools/_decode15_outer_writer.py` -- the 20k writer trace and triple
  counter.
* `tools/_decode15_semantics.py` -- the synthetic pair/triple/40 checks.
* `rocq/Machine15Outer.v` -- the local Rocq lemmas.
* `rocq/Machine15Round.v` -- the parametric and suffix writer/entry rounds,
  the 38-, 40-, and exact 42-bit block results, the continuation into the
  next field, and the first leftward output-growth phase.
