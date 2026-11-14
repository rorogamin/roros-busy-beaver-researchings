# Machine 14: raw bridge and stronger-invariant search

Target: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`.

## Raw-to-block bridge

The gap-aware Python checker (`machine14_block_bridge_gap.py`) verifies the
first 5,000 macro steps against the raw five-symbol machine, with all 19 block
rules exercised and gaps in `{0,1}`.  The raw prefix is exact from the start:

```text
step 0  < L U Q | R      raw 110111, offset 4
step 1  < L U   | P R    raw 110121, offset 3
step 2  > L W   | P R    raw 111121, offset 4
step 3  w> L W  | R      raw 111101, offset 5
...
```

This remains a finite empirical bridge, not a universal simulation theorem.
`Machine14.lean` now contains a raw zipper model (`RState`, `rawStep`), the
start configuration `rawStart`, and a proof that 14 raw steps reach `initRaw`
(`raw_prefix_14`, a finite `native_decide` certificate).  It also proves the
first raw macro rule, `raw_first_macro` (`Q < -> < P`), with no axioms.  The
full raw-to-block induction is still open.

## Stronger invariant search

`AvoidsGtR` is not inductive: `> V R` steps to `> R`
(`avoids_not_inductive`).  A finite right-context abstraction was searched:

- abstract state: head, left-head token or unknown, first two right tokens,
  and a `more` flag;
- 2,120 abstract states;
- bad language candidates:
  - `BadR = (V | C2)* R` for a `>` head;
  - `BadW = (V | X | C2)* (C | C1 | P) BadR` for a `w>` head.

After correcting the `w> C` and `w> C1` moves to the left side, the bad-state
closure check has **0** outgoing violations across the 308 bad abstract
states.  The actual 10⁶-step block run has **0** occurrences of either bad
language.  This makes the pair a concrete candidate for a stronger inductive
invariant.  `Machine14.lean` now defines `badR`, `badW`, and `safeB`, and
proves `safe_checked_million`: a machine-checked certificate that the block
run stays safe for 10⁶ steps.  That theorem uses a generated `native_decide`
axiom.  It is **not** the universal safe-set invariant: the bounded
left-stack search still has counterexamples, so the all-time closure remains
to be proved and the abstraction is not yet connected to the raw machine.

## Status

- `AvoidsGtR` non-inductive: proved.
- Finite raw bridge 5,000 macro steps: checked externally.
- Stronger `BadR`/`BadW` candidate: search evidence and bad-state closure only.
- No nonhalting proof for machine 14.

## 2026-11-07 continuation: invariant candidates fail

I rechecked the block invariant against exhaustive small right words and all
three heads.  The finite run is safe, but no simple state-independent
invariant closes:

1. `>` avoids `badR`, `w>` avoids `badW`, `<` avoids both:
   `> C R` is not `badR` but is `badW`, and steps to `< C1 R`, which is
   `badW`.  So `>` must avoid both languages; `w>` is allowed to carry a
   `badR` suffix because it consumes `V`/`C2` and repairs at `R`.
2. X-sentinel (`right` ends `X R`, or `w> R`):
   `> X R` steps to `< C1 P R`, which loses the X sentinel; `w> X R`
   steps to `w> R`, a safe transient.  Neither is a counterexample on the
   actual run, but they break the proposed induction.
3. The regular language `L (U|W|F|Y|Q)*` / `(V|C|C1|C2|P)* X* R`:
   `< Y` with right `V R` inserts `X`, producing `X V R`, so requiring the
   X to be at the right end is false.  Allowing X anywhere makes the
   language too weak to exclude other dead ends.

The actual block run was checked for 2,000,000 steps with zero occurrence of
`badR`/`badW`, but that remains finite evidence.  No closed invariant, Lean
theorem, or Rocq theorem was obtained.  A complete block proof now needs a
left-stack-sensitive invariant; a raw proof additionally needs the bridge,
and the block `> R` state is not literally the raw halt (`B3`): the raw rule
`A1 -> 2LA` continues through that boundary.

## 2026-11-07 later: the 2026-table parity invariant is not a halting proof

The regrouped 2026 table has a genuine `GF(2)` invariant

```text
#214 + #224 + #221 + #(2>)  is even.
```

It is preserved by every non-halting table rule.  The halt rule
`2> 21$ -> ---` consumes one `2>` and one `21$`, so its active pair has odd
parity.  That does **not** exclude the halt: the rest of the word may also have
odd parity.  In a 1,000,000-step finite-stack run, the parities of the left and
right parts took all four combinations, and the total parity changed whenever a
new control was popped from the finite stack.  Thus this parity is a useful
local fact about the table, not a nonhalting invariant for the machine.

A direct raw-tape analogue,
`#214 + #224 + #221 + [state B on 2] (mod 2)`, fails at raw step 3
(`A/1 -> 2LA`), so it is not a raw substring invariant either.

A targeted FAR run on this one machine with valid parameters
(`n * log2(5) <= 32`, so `n <= 13`) returned no certificate.  The public
BB(2,5) wiki still lists this machine under “Unsolved”; the “Dekaheptoid”
entries are different machines.

Status unchanged: no complete block invariant, no raw bridge theorem, and no
Lean/Rocq nonhalting theorem for machine 14.

## 2026-11-08: two-sided block invariant formalized

`bbwork/lean/Machine14TwoSided.lean` formalizes the block-level reading of
mxdys's left/right language:

- `LeftOK l`: `l = pre ++ [L]`, with no `L` in `pre`;
- `RightOK r`: `r = pre ++ [R]`, with no `R` in `pre`;
- `Inv2 s := LeftOK s.left ∧ RightOK s.right`.

Proved in Lean 4:

- `initB_inv2`: the block start satisfies `Inv2`;
- `stepB_inv2`: every one of the 19 defined block rules preserves `Inv2`;
- `runB_inv2`: every defined state of the block run satisfies `Inv2`;
- `inv2_implies_inv`: `Inv2` implies the old partition invariant;
- `inv2_contains_gtR` / `inv2_not_avoids`: the language still contains the
  block-level dead end `> R`, so this is not a nonhalting proof.

`#print axioms` reports only `propext` for `stepB_inv2`, `runB_inv2`, and
`inv2_implies_inv`; the initialization and counterexample theorems use no
axioms. The file is checked with:

```text
LEAN_PATH=. lean Machine14TwoSided.lean
```

## 2026-11-08: conditional assembly layer

`bbwork/lean/Machine14Assembly.lean` now connects the completed raw bridge to
the exact shape a block nonhalting proof must have.  It defines

```text
TotalOn P  :=  P initB  ∧  ∀ s, P s -> ∃ s', stepB s = some s' ∧ P s'
```

and proves:

- `runB_total_and_inv_of_totalOn`: a `TotalOn P` predicate makes the block run
  total while preserving `P` at every stage;
- `runB_total_of_totalOn`: consequently `runB n` is defined for every `n`;
- `raw_stage_bridge_of_totalOn`: every such block stage is reached by the
  actual raw machine through `rawRun_bridges_runB`;
- `exists_totalOn_iff_block_total`: existence of any `TotalOn P` is equivalent
  to totality of `runB`, so the premise is not a hidden extra assumption.

This is **not** a machine 14 nonhalting proof.  No predicate satisfying
`TotalOn` has been found.  `Inv2` still admits `> R`, where `stepB` is `none`,
and the attempted suffix, finite-window, linear-token, and monotone-size
invariants all failed.  The remaining obligation is therefore exactly the
block-totality statement; the raw bridge is complete and waiting on it.

`#print axioms` for all four assembly theorems reports only `propext`.  The
file contains no `sorry`, `admit`, or `native_decide`, and is checked with:

```text
LEAN_PATH=. lean Machine14Assembly.lean
```

## 2026-11-08: fixed-window search corrected and refuted

The earlier `machine14_abs3.py`/`abs4.py`/`abs5.py` scripts used a
right-window completion that enumerated **left** tokens, so their `missing`
counts were not a sound test.  Re-running the abstraction with the correct
alphabet gives the following.

- A 4-window exact-prefix abstraction reaches a bad abstract state with head
  `>` and first right token `R`.  One such state is
  `> | left = Q U Y Q ... | right = R V C C2 ...`; the hidden tails make it an
  over-approximation, not an actual run.  Since it reaches `> R`, no
  fixed-window invariant of size 4 can work.
- The corrected 5-window BFS did not finish within 180 seconds, so no claim
  is made for size 5.  It is not a proof either way.

A separate 2,000,000-step structural check found:

- deleting every `Q` and `Y` from the left stack always leaves
  `L (U|W|F)*`;
- every `Q`/`Y` occurrence was within five positions of the head in that run;
- every `>` state whose left stack contains `U` had at least one `X` on the
  right.

These are finite observations, not an inductive invariant.  In particular the
first two do not say where future `Q`/`Y` tokens may be pushed, and the third
is not preserved by the `> X` transition when the last `X` is consumed.

No block predicate excluding `> R` and closed under all 19 rules was found, and
no `TotalOn P` theorem was added.  The raw bridge and conditional assembly from
`Machine14Assembly.lean` remain the completed formal work; a machine 14
nonhalting proof is still open.

## 2026-11-08: clean counter formalized; no cval/X-count relation

`bbwork/lean/Machine14Counter.lean` formalizes the clean left language and the
mixed-radix value:

- `CleanL l`: `l = (U|W|F)* ++ [L]` in nearest-first order;
- `stripQY l`: delete the transient `Q`/`Y` tokens;
- `cval l`: `U -> 2v+1`, `W -> 2v`, `F -> v/2`, with `L` the zero base;
- `xcount r`: the number of `X` tokens on the right.

Proved in Lean:

- `clean_init_core`: the stripped initial left stack is clean;
- `cvalB_init = 1`, `xcountB_init = 0`;
- `runB_four`: four block steps reach
  `< W L | X R`;
- `cvalB_s4 = 0`, `xcountB_s4 = 1`;
- `cval_ge_xcount_fails`, `zero_cval_zero_x_fails`, `parity_fails`, and
  `cval_ge_two_x_fails`: the obvious relations fail on actual reachable states.

`#print axioms` reports only `propext` for the concrete reachability theorems;
the file contains no `sorry`, `admit`, or `native_decide`.

`bbwork/machine14_counter_relation.py` checks the candidate relations over
1,000,000 block steps.  Every nontrivial candidate fails:

| candidate | first counterexample |
|---|---|
| `cval >= xcount` | step 4, `cval=0`, `xcount=1` |
| `cval <= xcount` | step 0, `cval=1`, `xcount=0` |
| `cval == xcount` | step 0 |
| `cval >= 2*xcount` | step 4 |
| `cval <= 2*xcount` | step 0 |
| `cval = 0 iff xcount = 0` | step 0 |
| `cval = 0 implies xcount = 0` | step 4 |
| `xcount <= 6` | step 113,778, `xcount=7` |
| `(cval +/- xcount) even` | step 0 |

The only congruences `a*cval + b*xcount = c (mod m)` surviving the run for
`m <= 8` are the trivial `0 = 0` ones.  The observed ranges are also strongly
overlapping: at 1,000,000 steps `cval` ranges from 0 to 4,193,985 and `xcount`
from 0 to 7, with every head mode seeing several values of each.  Thus there is
no simple one-sided, equality, parity, or small-modulus relation between the
clean counter and the right `X` buffer on this run.

This does not rule out a relation involving additional left/right tokens or a
transition phase.  It does rule out the specific `cval`/`xcount` family as the
missing `TotalOn` predicate, and no such predicate has been proved total.

## 2026-11-08: phase windows and the right-buffer grammar

`bbwork/machine14_phase_game.py` searches fixed phase windows.  A window is
`(head, at most KL nearest left tokens, at most KR nearest right tokens)`, with
hidden tails enumerated nondeterministically whenever a rule consumes the last
visible token.  The forward abstraction starts at the real initial window and
stops at any window with head `>` and first right token `R`.

| window | result |
|---|---|
| 2 left / 3 right | reaches `> R` at depth 11 |
| 3 left / 3 right | reaches `> R` at depth 18 |
| 4 left / 3 right | reaches `> R` at depth 18 |
| 4 left / 4 right | reaches `> R` at depth 19 |
| 5 left / 5 right | reaches `> R` at depth 52 |

These are **abstract** counterexamples, not states of the real run, but they are
sound refutations of any invariant whose decision depends only on that window:
each is reachable from the initial window under the 19-rule transition
relation.  In particular, no phase invariant based on a fixed 5-left/5-right
window exists.  The 5-left/5-right search visited 327,121 windows before
finding the bad path.

The real run suggests a stronger structural language.  For 1,000,000 block
steps, every right buffer has the form

```text
(V | C | C1 | C2 | P)* X* R
```

with **zero** violations, and no `V/C/C1/C2/P` token occurs after the first
`X`.  The only zero-`X` right words are `R` (42 times) and `P R` (2 times).
This is a genuine phase grammar candidate, unlike the numeric `cval` relations.

`bbwork/machine14_phase_grammar.py` combines that grammar with the local
no-bad conditions

- `>` never has first right token `R`;
- `w>` never has `C`, `C1`, or `P` immediately followed by `R`;
- `< L` and `< U` have the corresponding exclusions;
- `< Y` never has a phase token on the right.

On 1,000,000 real steps the grammar has 0 violations and this predicate has 0
violations.  It is still **not inductive**.  The closure check over all
grammar-conforming right words of length at most 7 and all left-head tokens
checked 2,075,136 states and found 48,898 violations.  The first failures are
actual one-step predecessors of the dead end:

```text
> V R   ->  > U R      (then > R)
> C R   ->  < L C1 R   (then w> C1 R -> > Q U R)
> C2 R  ->  > F R      (then > R)
> P C R ->  w> L C R   (then w> C R -> > Q F R)
```

The zero-`X` restriction `R` or `P R` also fails as an induction: `< W R`
produces `< V R`, `< F R` produces `< C R`, `< Q P R` produces `< P P R`, and
`> X R` produces `< C1 P R`.  These are abstract transitions; their sources
are not observed in the real run, but excluding them requires more left/right
context than the local phase predicate currently carries.

### Machine-checked non-inductiveness

`bbwork/lean/Machine14Phase.lean` formalizes the grammar as
`PhasePrefix p ∧ XRun x` with right buffer `p ++ x ++ [R]`, plus the local
`badPhase` predicate.  The four checked patterns are:

| theorem | source | target |
|---|---|---|
| `phase_failure_VR` | `> V R` | `> U R` |
| `phase_failure_CR` | `> C R` | `< L C1 R` |
| `phase_failure_C2R` | `> C2 R` | `> F R` |
| `phase_failure_PCR` | `> P C R` | `w> L C R` |

Each theorem proves that the source satisfies `PhaseOK`, the block step is the
listed one, the target still satisfies `RightPhase`, and the target does **not**
satisfy `PhaseOK`.  `phase_not_inductive` packages all four; `PhaseOK` therefore
cannot be an invariant.  `phaseOK_excludes_gtR` separately checks that the
predicate would exclude the original dead end.  The file compiles with Lean
4.35.0, and the printed results depend only on `propext`.

### Left-context gate and left-phase exclusions

`machine14_phase_left.py` adds the checked gate

```text
left word is L (U|W|F|Y|Q)*   and   head = >  =>  at least two left blocks
```

(`L` is the far end; the Python block model stores the left buffer
far-to-near).  This excludes all four bare-left sources above.  On the first
1,000,000 actual block steps the combined phase-plus-gate predicate has 0
violations; the same count remains 0 after adding all checked `<` exclusions.

The first bounded closure test, over valid left words of length at most 5 and
grammar-conforming right words of length at most 4, checked 2,128,848 states
and found **160,415** violations.  Its first failures were

```text
< F R  ->  < C R          (left L F, far-to-near)
< Q R  ->  < P R          (left L Q, far-to-near)
```

These are `⟨<, [F,L], [R]⟩` and `⟨<, [Q,L], [R]⟩` in the nearest-first Lean
representation.  The second failure appeared in the earlier bounded search;
both sources are now rejected by the local `badLeftPhaseFQ` exclusion.

After adding the checked `< L F R`/`< L Q R` exclusion, the same bounded
closure search checked 2,128,846 states and found **160,413** violations.  The
first remaining failure is

```text
< Y W R  ->  < Y V R        (left L Y W, far-to-near)
```

which is `⟨<, [W,Y,L], [R]⟩ -> ⟨<, [Y,L], [V,R]⟩` nearest-first.  The target
violates the local `< Y`/phase exclusion.  This is checked by
`phaseL2_failure_YWR` for the intermediate predicate `PhaseOKL1`.

The `< Y W` pattern does not depend on the right buffer.  Once `<` reads `W`
after `Y`, the step produces `< Y V ...`, and `< Y` followed by a phase token
is already locally excluded.  The checked `badLeftPhaseYW` therefore rejects
any valid left word ending in `Y W`, for every grammar-conforming right word.
After that exclusion, the bounded closure search checked 2,098,621 states and
found **159,951** violations.  The first remaining failure is

```text
< Y F R  ->  < Y C R        (left L Y F, far-to-near)
```

which is `⟨<, [F,Y,L], [R]⟩ -> ⟨<, [Y,L], [C,R]⟩` nearest-first.  The target
again violates the `< Y`/phase exclusion.  This is checked by
`phaseL3_failure_YFR` for the intermediate predicate `PhaseOKL2`.

The `< Y F` pattern is bad for the same reason and also does not depend on the
right buffer: `F < -> < C`, so the target is `< Y C ...`.  The checked
`badLeftPhaseYF` rejects any valid left word ending in `Y F`.  After that
exclusion, the bounded closure search checked 2,068,396 states and found
**159,489** violations.  The first remaining failure is

```text
< Y Q R  ->  < Y P R        (left L Y Q, far-to-near)
```

which is `⟨<, [Q,Y,L], [R]⟩ -> ⟨<, [Y,L], [P,R]⟩` nearest-first.  The target
again violates the `< Y`/phase exclusion.  This is checked by
`phaseL4_failure_YQR` for `PhaseOKL3`.

The `< Y Q` pattern is the last of the three nearest-suffix cases:
`Q < -> < P`, so the target is `< Y P ...`.  The checked `badLeftPhaseYQ`
rejects any valid left word ending in `Y Q`.  After that exclusion, the
bounded closure search checked 2,038,171 states and found **159,027**
violations.  The first remaining failure is

```text
< Y W W R  ->  < Y W V R      (left L Y W W, far-to-near)
```

which is `⟨<, [W,W,Y,L], [R]⟩ -> ⟨<, [W,Y,L], [V,R]⟩` nearest-first.  The
target is rejected by the earlier `< Y W` exclusion, so this is a backward
cascade rather than a new local `< Y` target.  It is checked by
`phaseL5_failure_YWW` for `PhaseOKL4`.

Instead of adding a one-off `Y W W` rule, the next step closes the whole
`< Y` family backwards.  `badLeftPhaseY` scans the nearest run of `W/F/Q/Y`
tokens and rejects it if it contains `W Y`, `F Y`, or `Q Y`.  This is exactly
the set of left words that can reach one of the three forbidden `< Y`
patterns by `<` steps.  The predicate `PhaseOKL5` adds this family to
`PhaseOKL4`.

On the first 1,000,000 actual block steps the unified predicate still has 0
violations.  The bounded closure search now checked 1,959,046 states and found
**138,150** violations.  The first remaining failure is a `>`-head source:

```text
> V R  ->  > U R        (left L U, far-to-near)
```

which is `⟨>, [U,L], [V,R]⟩ -> ⟨>, [U,U,L], [R]⟩` nearest-first.  The target
is the `> R` dead end with an extra left block.  This is checked by
`phaseL6_failure_UV` for `PhaseOKL5`.

The `> V R` source is now rejected directly by `badRightVR`.  The current
`PhaseOKL` adds that rule to `PhaseOKL5`.  On the same 1,000,000 actual steps
it still has 0 violations.  The bounded closure search checked 1,958,266
states and found **141,429** violations.  The first remaining failure is the
`< U` predecessor of the newly excluded source:

```text
< U V R  ->  > W V R      (left L U, far-to-near)
```

which is `⟨<, [U,L], [V,R]⟩ -> ⟨>, [W,L], [V,R]⟩` nearest-first.  The target
is rejected by `badRightVR`, so this is another backward cascade rather than
a new local dead end.  It is checked by `phaseL7_failure_UVR`.

The Lean file records the staged predicates and their witnesses:

- `leftGate_excludes_four` proves the four old sources are rejected;
- `phaseOKL_init` checks the initial block state for the current predicate;
- `phaseL0_failure_FR` and `phaseL0_not_inductive` preserve the checked
  `< F R -> < C R` counterexample for the gate-only predicate `PhaseOKL0`;
- `leftPhase_excludes_FR_QR` proves the two F/Q sources are rejected by
  `PhaseOKL1`;
- `phaseL2_failure_YWR` proves the next counterexample for `PhaseOKL1`;
- `leftPhase_excludes_YW` proves the `< Y W` source is rejected;
- `phaseL3_failure_YFR` proves the next counterexample, for `PhaseOKL2`;
- `leftPhase_excludes_YF` proves the `< Y F` source is rejected;
- `phaseL4_failure_YQR` proves the next counterexample, for `PhaseOKL3`;
- `leftPhase_excludes_YQ` proves the `< Y Q` source is rejected;
- `phaseL5_failure_YWW` proves the cascade counterexample for `PhaseOKL4`;
- `leftPhase_excludes_YWW` proves the unified family rejects that cascade;
- `phaseL6_failure_UV` proves the `> V R` counterexample for `PhaseOKL5`;
- `rightPhase_excludes_VR` proves the current predicate rejects `> V R`;
- `phaseL7_failure_UVR` proves the next `< U V R` cascade;
- `phaseL7_not_inductive` packages the resulting non-inductiveness.

The closure search is bounded, not an exhaustive proof about unbounded left
words, but the checked `< U V R` counterexample is enough to show that the
current predicate still does not close.  The file compiles with Lean 4.35.0
and the printed results depend only on `propext`.

Thus the phase search found a strong empirical grammar but **no closed phase
invariant**.  It does not yield a `TotalOn` predicate, and no total/nonhalting
theorem was added.
