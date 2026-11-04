# Why a machine is "epsilon-level"

An analysis of the ε₀ rung: the census machines at f_{ω↑↑4}, f_{ε₀}, f_{ε₀+1}, the
stack engine in this repo, and the f_lim(BMS)(10^^15) machine in `limbms.txt`.

Nothing here is a theorem about any machine's runtime. It is an analysis of the
*structure* that forces a level, written so that each step is either a definition,
an arithmetic fact, or a measured property of a concrete table. The last section
lists what would have to be proved to turn any of it into a claim.

---

## 1. What "level" means, and what it is not

"Machine M halts in f_α(n) steps" means: the step count is bounded below by the
fast-growing hierarchy at index α, evaluated at the machine's input size. The
ordinal is a property of the *termination ordering of the machine's loop
structure*, not of the tape's alphabet or of how the tape encodes numbers.

Two consequences that the measurements in this repo make vivid:

* **Tape contents do not determine the level.** BB(19,5) and a tower machine both
  produce roughly 1500 ones in the first 400 000 steps (handbook §8). At those
  budgets a tower and an ε₀ engine are indistinguishable by looking at the tape.
* **State count does not determine the level either.** BB(29) is already above
  f_{ω^ω}(3) and BB(31) above f_{ω↑↑4}(3) — two states per tetration level — while
  this repo's 250-state stack engine is at ω^ω. The ordinals are cheap; what is
  expensive is the *control* that makes the descent real.

So the question "why is this machine ε₀" is the question: *what is the order type
of the relation along which its rounds decrease?*

---

## 2. The ladder, as measured by the census

| machine | states | symbols | claimed level | source |
|---|---|---|---|---|
| BB(29) | 29 | 2 | > f_{ω^ω}(3) | census row |
| BB(31) | 31 | 2 | > f_{ω↑↑4}(3) | census row |
| BB(33) | 33 | 2 | > f_{ω↑↑6}(3) | census row |
| BB(19,5) | 19 | 5 | f_{ε₀}(1.7·10³⁵²) | census row |
| BB(51) | 51 | 2 | f_{ε₀+1}(8) | census row, disputed (see §6) |
| BB(56,7) | 56 | 7 | (f_{ε₀})^F, F read from the tape | census row |
| BB(94,5) | 94 | 5 | f_{ψ₀(Ω₂)}(1.7·10³⁵²) | census row |
| `limbms.txt` | 150 | 2 | > f_lim(BMS)(10^^15) | the file's own header |

The first three rows are the important ones for this analysis, because they are a
*controlled* sequence: 29, 31, 33 states, two states per rung, ω^ω → ω↑↑4 → ω↑↑6.

---

## 3. The arithmetic that separates the towers from ε₀

Write ω↑↑0 = 1, ω↑↑(k+1) = ω^(ω↑↑k). Then:

**Claim.** For every finite k, ω↑↑k < ε₀.

*Proof.* ω↑↑1 = ω < ε₀. If ω↑↑k < ε₀ then ω↑↑(k+1) = ω^(ω↑↑k) < ω^ε₀ = ε₀,
using that ω^· is strictly increasing on the ordinals and that ε₀ is by definition
the least α with ω^α = α. ∎

ε₀ is exactly the *supremum* of the towers: ε₀ = sup{ω, ω^ω, ω^{ω^ω}, …}. That
single line is the whole reason the census's "two states per tetration level"
scaling can never reach ε₀: raising the tower raises k, and every finite k is still
below the supremum. Crossing into the ε family requires a change of *data
structure*, not one more level.

This is the same statement the census notes make informally ("ω↑↑k < ε₀ for every
finite k"), and the reason BB(51) = f_{ε₀+1}(8) cannot be explained by the
tetration ladder.

---

## 4. A usable criterion

For a 2-symbol machine whose run decomposes into nested rounds, define the
**descent type** as the order type of the well-founded relation "this round's
arguments are smaller than the enclosing round's". Then:

| descent type | what the machine can do | example |
|---|---|---|
| ω^k, fixed k | k nested counters, all bounded by tape data | machine 1–2 here (doubling, tower) |
| ω^ω | digits are unbounded in *number*, each digit a count | machine 5 (250 states, this repo) |
| ω↑↑k, fixed k | k nested *levels*, each level's height a counter | BB(31) (k=4), BB(33) (k=6) |
| ε₀ | a numeral whose *digits are themselves numerals* — the height is data | BB(19,5), BB(51) |
| ε₀+1 | an outer loop around an ε₀ descent | BB(51) (claims), BB(56,7) |
| beyond | the matrix dimension itself is data | BB(94,5), `limbms.txt` |

The distinguishing question is always the same: **where does the iteration count
come from?** (handbook §9.4). If the count is a constant baked into the control,
the level is fixed by the control. If the count is read off the tape, the machine
climbs one rung. If the *height of the stack that holds the counts* is read off the
tape, the level is ε₀.

---

## 5. The three ε-shaped mechanisms, in order of strength

### 5.1 Machine 5 here: ω^ω, and why it is not ε₀

The 250-state stack engine writes `[C 1^c] 00 [11 1^s 0..0 11] … [11 1^s 11]`, with
digits `[2,2,2,2]` giving the numeral ω³·2 + ω²·2 + ω·2 + 2. Each pass doubles the
counter and erases one digit of the stack.

This is genuinely data-driven depth — the number of digits is on the tape, not in
the control — and that is what buys ω^ω rather than ω^k. It is nevertheless below
ε₀, because the *digits are counts*: the numeral is a finite sum Σ ω^{k_i}·c_i with
k_i < ω, and every such numeral is below ω^ω. The stack never contains a stack.

That is exactly the boundary. To pass it, a field must be re-readable as a program:
the machine must be able to take the *length of a block* and use it as the number
of rounds of an inner engine, so that the exponent itself is a numeral.

### 5.2 BB(19,5): ε₀ by re-reading a field as a program

The census's canonical ε₀ engine is 19 states on 5 symbols and reaches
f_{ε₀}(1.7·10³⁵²). The mechanism is the one named in the handbook: **a counter
whose height is a counter.** Structurally, one field of the tape is used twice —
once as data (the number of rounds to run), and once as a program (the block that
says how those rounds are structured). Because the block can be re-read at
successively larger sizes, the induced descent has order type ε₀ = sup of the
towers; no fixed k bounds the nesting, so the machine escapes the ω↑↑k class.

Implementation-wise nothing in the *alphabet* changes: 5 symbols are used because
the engine needs a few distinguished markers, not because ε₀ needs 5 symbols.
BB(18,7) is the same machine re-encoded, and BB(56,7) is that engine glued to a
connector (handbook §10.4).

### 5.3 BB(51,2): ε₀+1, by iteration

The +1 is not a new data structure; it is an outer loop. A numeral form for ε₀
already needs "a list whose elements are lists" (borrow, push, re-read). ε₀+1 adds
a *count of how many times the whole ε₀ descent is run*, i.e. one more axis above
the tree. That is why the handbook's cost table prices ε₀+1 as "list whose elements
are lists: borrow + push + re-read" at 51 states, and why the census's BB(56,7)
is described as `(f_ε₀)^F` — the same idea with the iteration count read off the
tape rather than fixed.

A caution this repo already records: BB(51) = f_{ε₀+1}(8) is a 2024 per-machine
analysis, it sits 18 states above the f_{ω↑↑6} machine, and monotonicity plus
ω↑↑k < ε₀ means it tells us nothing about the ε₀ rung's true state cost.

---

## 6. The BMS machine in `limbms.txt`

Measured, with `tools/morphet.py` (Morphet syntax: `_`/`1`, `r`/`l`/`*`, labels):

```
150 states (excluding the uncounted alias 0), 283 rows, 2 symbols
19 undefined (state, symbol) pairs  <- these are the halt conditions
rows per module: A:13 B:10 C:12 D:18 E:24 F:18 G:11 H:16 I:27 J:24 K:15 L:12 M:17 N:15 S:25 T:6 d:6 e:12
```

### 6.1 The five stages

1. **Boot (A–F).** This is Sligocki's BB(6) champion, embedded verbatim; the file
   says its output is `S(>1, 10^^15)` when it exits D into d0. A 3 000 000-step run
   is still in this stage (1401 ones), which is the point: the boot alone is a
   `10^^15`-step computation, so *no* claim about this machine can be established
   by running it.
2. **Squaring (d0–e6).** Doubles the left number while draining the right one, then
   cleans up, giving `A > B² > 10^^15`. This is the "argument" of the later engine.
3. **Array building (S1–S13, T1–T3).** Converts `1^A 0 1^B` into
   `S(1, n, 0, n, n, …, n)` — a header and a block of `n`s, i.e. the
   `(0,0,0)(1,1,1)(2,2,2)…` shape that RFPMS expands.
4. **RFPMS engine (A1–N8).** The whole point of the file: a *reverse flattened
   pointer matrix system*. Columns of `R` entries are flattened into a run of
   numbers, the array is reversed, entries store **the distance to their parent**
   instead of running BMS's parent search, and `Order`/`Coorder` encode the
   position inside the current column (`Order + Coorder = Rows + 1`).
5. **Halt.** The engine halts when the `(child+1)`-th element does not exist — the
   file's own "System C" reformulation of BMS's empty-matrix halt condition.

### 6.2 Why this is far above ε₀

Three structural facts, all visible in the table:

* **The number of rows is data.** `Order` and `Coorder` are stored on the tape and
  add to `Rows + 1`; the header `S(1,n,0,n,…,n)` has `n` of them. In a fixed
  dimension `R` you get a fixed finite tower of `R` "axes" — that is the ω↑↑k
  regime. Here `R` changes as the array grows, so the machine is not at any fixed
  dimension at all.
* **Pointers encode a well-founded relation, not a counter.** An entry stores its
  distance to its parent. The ascension rule (`E ≥ threshold → prepend E+child`)
  copies a whole subtree with the pointers shifted; that is the BMS ascension
  matrix, and the termination argument is *the pointer distances decreasing*, not a
  numeral reaching zero.
* **Expansion is self-similar.** Each cycle expands one entry using the child's
  value as the number of copies, so the recursion feeds its own output back as the
  iteration count — the same "re-read a field as a program" move that makes §5.2
  ε₀-shaped, but applied to a matrix ordering rather than to a numeral.

BMS's limit is far beyond ε₀ (`lim(BMS)`; the file's own remark is that the
slow-growing/hardy mismatch is repaired at ψ(Ω_ω)-scale, and BB(94,5) is quoted at
f_{ψ₀(Ω₂)}). So if the correspondence holds, the machine is not "ε-level" at all —
it is several fixed points above it.

### 6.3 What is *claimed* rather than established

The file is candid about its own reductions, and they matter:

* RFPMS expands with an [m=1]-ish rule and uses the **slow-growing** hierarchy,
  where BMS uses Hardy; the file argues the gap closes and that
  `RFPMS[n+2] > BMS[n]`.
* The halt condition is changed (halt when the target element is missing, rather
  than when the matrix is empty), with a "System A/B/C" argument that the two are
  equivalent after adding a root column.
* The engine loses two columns relative to BMS (the file's own "RFPMS nerf").
* **Most load-bearing of all:** the engine needs at least 3 BMS rows, and
  termination of BMS at 3+ rows is *not proved* — it is the standing conjecture
  that makes "lim(BMS)" a meaningful ordinal at all. The file cites arXiv 2307.04606
  for the termination/power correspondence; the claim "outputs > f_lim(BMS)(10^^15)"
  is therefore conditional on that, and is stated by the file as a claim, not a
  theorem.

So: 150 states, 2 symbols, a verified table, a plausible reduction to RFPMS, and a
level claim that inherits an open conjecture. That is a very different epistemic
object from BB(19,5) = f_{ε₀}(1.7·10³⁵²), which is also an analysis, but of a
concrete run regime that the census has measured over hundreds of runs.

---

## 7. What it would take to prove any of this

Ordered by increasing difficulty, and stated against what this repo already has:

1. **ω^ω rung (machine 5).** A loop invariant whose parameters are the two counts,
   plus the pass lemma. *Status: half done.* `round`, `pass_loop`, `pass_run`,
   `carry_front`, `carry_exit`, `walk_E9`, `exit_sweep`, `exit_run` are
   machine-checked (15 audited theorems, `rocq/StackPass.v`). Missing: the `E7`
   re-entry branch and the `D0` descent through the stack fields.
2. **ω↑↑k rungs (BB(31), BB(33)).** A *family* of invariants indexed by the level,
   with a proof that level k+1's invariant is the level k engine applied to itself.
   Nothing in this repo attempts this; machine 5 is the k=1 case.
3. **ε₀.** The invariant must range over the hereditary numeral (a tree), and the
   measure must be a *well-founded* order on trees — a Goodstein-style descent
   engine. This is the piece that does not exist here, and the reason no ε claim
   can currently be made symbolically.  *(Update: the pieces either side of it now exist -- `ModuleK.v`
composes module K's round into a run with its exact cost, and `Eps1.v`
proves the value rule of the feedback that leaves the tower class.  The
hereditary-numeral invariant is still the missing middle.)* The census file says it outright: such a
   claim "cannot be checked by evaluating a run".
4. **ε₀+1.** Add an outer iteration counter to (3) and prove the composite; the
   BB(56,7) `(f_ε₀)^F` form is the clean statement of what that means.
5. **BMS.** A proof would need (a) well-foundedness of the matrix order at the
   relevant dimension, (b) that RFPMS's expansion is a fundamental sequence for it,
   (c) that the machine implements RFPMS faithfully. (a) is open mathematics for
   3+ rows, so the honest endpoint for `limbms.txt` is: **a candidate at an
   unproved level**, which is exactly the status §6.3 describes.

---

## 8. Summary

* Towers do not reach ε₀: ω↑↑k < ε₀ for every finite k, so the census's
  two-states-per-level ladder is asymptotic to ε₀ but never at it.
* ε₀ appears when the machine can **re-read a field as a program**, making the
  height of its stack data rather than control. That is BB(19,5), and that is what
  machine 5 here deliberately stops short of (its digits are counts, so it is ω^ω).
* ε₀+1 is one outer loop around that, priced at a numeral form ("list whose
  elements are lists") — the +1 is cheap conceptually and expensive in states.
* The BMS machine goes further by making **the matrix dimension itself data** and
  replacing counters with a well-founded pointer relation; its level claim is
  conditional on BMS termination, which is open at the row count it needs.
* The gap between "the machine is at level α" and "we can prove it" is, for
  everything above ω^ω, a missing *descent engine* — not a missing machine.

## eps_1: the second feedback

`tools/eps1.py` is the notation layer above eps_0.  The point it records is
structural: no finite CNF term names eps_0, because eps_0 is the least fixed
point of w^.  So a system that reaches *above* eps_0 needs a new atom, with

    eps_0[n] = tower of n omegas          (1, w, w^w, w^(w^w), ...)

and the ordinary rules on top of it.  That is the rung eps_1 is built from: the
descent engine's parameter is no longer a number read off the tape, it is an
ordinal notation whose fundamental sequence is itself a computation.  A machine
there must re-read its own count field as a program, twice over -- the first
feedback is module K at the eps_0 scale, the second is the descent on the
exponent.

Checked in `tools/eps1.py`: eps_0's sequence is the tower (n = 0..3);
eps_0 is a limit above every finite tower; eps_0+1 is a successor and has no
fundamental sequence; eps_0*w has (eps_0*w)[n] = eps_0*(n+1); eps_0*2 has
(eps_0*2)[n] = eps_0 + tower(n); and for a set of terms, a[n] < a and
a[n] <= a[n+1].  No machine at this scale exists.  What *is* now proved at this rung
is the value rule of the first feedback: `rocq/Eps1.v`, at the end of
this file.

## eps_0: buying rounds from the value

The tower machine only shows multiplication by `2^c` with `c` written on the
tape by hand.  For eps_0 the round count has to come from the machine's own
output, and the model for that is `tools/eps0_fuel.py`.  A stage spends marks
out of the value block as counter marks, then runs the tower machine's round
that many times:

    c <- v // 2;   v <- v - c;   v <- (v+1)*2^c - 1

The block regrows past what it spent, so each stage's fuel is roughly half of
the previous stage's value -- one stage is one exponentiation, and n stages is
the n-th rung.  With `v0 = 3` the fuels run `1, 2, 7, 575` and the bit counts
`3, 5, 11, 585`: that jump is the tower, not linear growth.

The first version of that file let the value decide its own stage count and did
not halt: `v` grew as `2^(v/2)` per stage, so the next stage always bought more
rounds than the last.  The stage count must be fixed by the input.  That is a
design constraint on the hardware, not a detail: the fuel region and the stage
counter must be separate blocks, or the machine is a non-halting construction
and cannot compute `f_eps_0(n)` at all.

Cost, in states, from the modules that exist:

| piece | states | status |
|---|---|---|
| tower drive + module K | 19 | built, checked `c=1..3, v=1..3` |
| fuel move (half the block to the counter) | ~9 | spec below, not built |
| stage counter and branch | ~4 | not built |
| total | ~32 | target, no machine yet |

The fuel move is the easy half of what a copy would cost: marks are *moved*,
not duplicated.  Walk out to the block's tail, erase one mark, carry it back to
the counter region and write it one blank past the counter, so the two blocks
stay separable; repeat while the counter is short of `v//2`.  Measured round
cost on the built tower machine is about 400 steps, which is the constant the
step estimates in `eps0_fuel.py` use -- an estimate, not a measurement of
anything that exists.

So: eps_0 is a 32-state target with its recurrence checked and its modules
budgeted, not a machine.  The eps_1 rung needs the eps_0 layer as an atom, which
is why the 35-state eps_1 ask stays refused until an eps_0 machine actually
halts.

## eps_0 machine: 33 states, halting

`tools/eps0_machine.py` builds the eps_0 machine (26 drive states plus module
K's 7).  From `1^n 0 1(wall) 0 1^v 0 1(seed)` it computes `v -> 2^(v+1) - 1`
per stage, n stages, and halts:

    n=1 v=1: 47 steps -> 3        n=2 v=1: 490 steps   -> 15
    n=1 v=2: 139 steps -> 7       n=2 v=2: 68264 steps -> 255
    n=1 v=3: 413 steps -> 15

So `1 -> 3 -> 15 -> 255 -> 65535`: the rounds of each stage are the value the
previous stage produced, which is the eps_0 growth.  What is *not* established
is that the machine computes `f_eps_0(n)` for all n -- only `n<=2, v<=3` is
checked, and a rung claim needs a symbolic argument, not a run.

Three defects the build surfaced, all fixed:

* fuel taken from the value's tail is unsound.  Once the counter grows up
  against the value, the cell left of the tail is a counter mark, so the drive
  believes the value still has marks to move (the take had to move to the front);
* the new value must be placed one gap left of the destination seed, or K takes
  `value + seed` as its source and the recurrence silently changes;
* after writing the next seed the return walk must step back across the gap onto
  the block.  Otherwise the walk starts inside the gap, reaches the block's marks
  and the round entry reads one as leftover fuel -- that was the non-halting
  version.

The stage count must come from an input block.  This is a correctness
constraint, not a convenience: with the value setting its own stage count the
machine does not halt, because each stage multiplies the value by about
`2^(v/2)` (see `tools/eps0_fuel.py`).

## Rocq: the round rule, and what it does not say

`rocq/Tower.v` compiles with `coqc -Q . Top Tower.v` (status 0), and every
`Print Assumptions` in it reports "Closed under the global context".

What it proves, for the rule the eps_0 machine's round loop implements:

    round v          = 2*v + 1                       (one round: seed + two per mark)
    rounds c v       = round applied c times
    rounds_closed    : rounds c v + 1 = (v + 1) * 2^c
    rounds_ge        : v <= rounds c v
    rounds_ge_pow2   : 2^c <= rounds c v + 1
    tower n          = rounds n 1                    (n stages from one mark)
    tower_is_rounds  : tower n = rounds n 1
    tower_succ       : tower (n+1) = 2 * tower n + 1
    tower_dominates_pow2 : 2^n <= tower n + 1
    tower_strict     : tower n < tower (n+1)

So the machine's value rule is proved symbolically, for all counts, not sampled.

What it does *not* say, and what this project must not claim: that the machine
halts in f_eps_0(n) steps.  It cannot.  The stage count is a plain input row, so
after n stages the value is a tower of 2s of height n -- `tower`, above.  That
is f_omega-scale growth.  f_eps_0(n) is f_{eps_0[n]}(n) with eps_0[n] a tower of
omegas, which dominates every fixed-height tower of 2s.  Reaching eps_0 needs
the *stage count* to decay from a tower (the nested engine style loader3229
uses), not a bigger argument at one level.  No step-count theorem exists here
either: `Tower.v` proves the value rule, not the number of steps the drive takes
to reach it.

## eps_0's round, composed: ModuleK.v

`rocq/ModuleK.v` used to stop at one-step lemmas and un-spliced phases.  The
phases are now composed into the module's own cycle, as a run:

    mark_cycle
      run (2*G + 2*d + 9)
          (K2, source 1^(S (S s)), head on a blank, gap 0^G, destination 1^(S d))
      = (K2, source 1^(S s), head on a blank, gap 0^(S G), destination 1^(S (S (S d))))

One source mark costs `2G + 2d + 9`; the destination grows by two marks and the
gap by one.  The two configurations that look like separate cases -- a gap of
zero and a gap of at least one -- cost the same, because with no gap the turn
lands the head on the source's last mark and the erase is a single step instead
of a walk over blanks.

`tools/kcheck.py` reports the same cycle at `2g + 2d + 7`.  That is the same
number in its indices, where the source is `s` marks and the destination `d`
rather than `S s` and `S d`; the two statements agree mark for mark.

Iterating, with the cost defined by the same recursion the run follows:

    cycles n G d = 0                                               if n = 0
                 = (2*G + 2*d + 9) + cycles (n - 1) (S G) (d + 2)  otherwise
    cycles_closed : cycles n G d = 2*n*G + 2*n*d + 3*n*n + 6*n

The `3n^2 + 6n` is growth, not a constant per cycle: both the gap and the
destination widen as marks are consumed, so every cycle is dearer than the last.
`cycles_run` spends `cycles n G d` steps and turns `n + 3` source marks into `3`.

The halt is a theorem, not an observation: `walk_k6_last` erases the final mark,
`k_halt_step` states that `step` of the resulting configuration is `None`, and
`module_k_halt` composes them into `run ktbl (g + 3) ... = None`.

The block is closed as well: `k_block` consumes a source block of any length
and the run is literally `None` -- the module halts on every source size, not
just on the sizes a simulator reaches.  The last mark is special because its
erase walk steps onto a blank instead of onto another mark, so it gets its own
cost (`last_cost`): `2d + 9` with an empty gap, `2G + 2d + 9` without, and the
two agree because with no gap the turn lands the head on that mark and the
erase is a single step.  `k_cost` is the whole-block cost, the same recursion
the run follows.

What is still missing on this rung: the drive's loop around module K -- the
counter decrement, the fuel move and the stage branch.  The last section below
records how far that has got: the stage cost is proved, the splice into the
33-state table is proved, the loop's cost law is checked on the real trace, and
the two walk inductions that would make it a theorem are still owed.  With no
step count for the 33-state table, the f_eps_0 claim stays refused for the
reason above (the stage count is an input row).

## eps_1's first feedback, in Rocq

`rocq/Eps1.v` (13 closed theorems, in `verify.sh`) formalises the one change
that leaves the tower class, stated on values rather than on control:

    nest v = rounds v v

The number of rounds is the value, not a count handed in.  Proved:

    nest_closed          nest v + 1 = (v + 1) * 2^v
    nest_mono            v <= v' -> nest v <= nest v'
    nest_strict          nest v < nest (S v)
    nest_escapes_fixed   rounds c v < nest (S (S (c + v)))    for every c and v
    tower_le_nest        tower k <= nest (S k)
    tower_lt_nest        tower k < nest (S (S k))
    eps0_fs_strict       tower n < tower (S n)
    eps0_fs_below_nest   tower n < nest (S (S n))

resting on the monotonicity lemmas `round_mono`, `round_strict`,
`rounds_mono_v`, `rounds_lt_v`, `rounds_succ_c` and `rounds_mono_c`.

`nest_escapes_fixed` is the honest content of "one rung up": for every fixed
stage count `c` and every value `v` there is a value at which the diagonal
strictly beats it.  A fixed height cannot reach the diagonal -- which is exactly
why the eps_0 machine's stage count being an input row caps it at f_omega, and
why "more stages" is not the move that changes the rung.

Still missing for eps_1 as a *machine*: the second feedback, where the exponent
is itself a numeral whose fundamental sequence is a computation.  `tools/eps1.py`
is that notation, with `eps_0[n]` the tower and the descent rules checked on a
set of terms, but no machine implements it.  So `Eps1.v` proves a rule about
values; it is not a step count, and nothing in this repository claims f_eps_1.

## The eps_0 drive: a defect, a repair, and the splice into Rocq

### The defect

Writing down what the drive must do exposed a real bug in `tools/eps0_machine.py`
-- my own machine, not a census row.  The stage branch spent a stage mark by
erasing the block's *rightmost* mark, which left a hole between the remaining
marks and the one-blank gap that separates the block from the counter.  The next
stage's walk looked for a mark across that gap, found the hole, and took the halt
branch.  The symptom was exact and wrong: for every stage block of length n >= 2
the machine halted after two stages, so n = 3 gave 15 -- the second stage's value
-- instead of 255.

The repair keeps the state count at 33 and spends the block's *leftmost* mark
instead (states S0..S4: `(21,on) -> (on,L,21)`, `(21,bl) -> (bl,R,22)`,
`(22,on) -> (bl,R,23)`), so the right end of the block stays flush with the gap
and there is never a hole for the next walk to fall into.  The branch is tested
*after* the erase, so k marks give exactly k stages.  Measured after the repair:
n = 1 -> 3 in 46 steps, n = 2 -> 15 in 490 steps, and the value after k stages is
2^k (v+1) - 1.  n >= 3 now genuinely runs; it was not run to completion (the
value passes 2000 within 4e6 steps, and the cost is a product of stages times
rounds, of order 10^8).

### Module K's pre-block (the cost of one stage)

`k_pre` is the cost of the module's block *ending on the cell where the module
would halt*.  `k_pre_block` proves that from the K2 entry a source of `S x` marks
becomes `2x+1` marks, the gap grows from `G` to `G+x+2`, the destination grows by
2 per cycle, and the run lands on K7 over a blank in exactly `k_pre (S x) G d`
steps.  `k_pre_is` ties it to the halt cost already proved:
`k_cost (S x) G d = k_pre (S x) G d + 1`, so `cycles_closed` covers the block and
`k_pre` is that minus the halt step.

### The splice: `rocq/Eps0Drive.v`

The drive's table has 33 states; module K's seven states sit at 26..32.
`rocq/Eps0Drive.v` (six closed theorems, axiom-free, in `verify.sh`) proves the
splice:

* `row_K`, `row_K7_on`: the drive's rows for the module's states are the module's
  rows with the target shifted by 26.  Exactly one row disagrees, and it is the
  row the module never takes: `ktbl K7 bl = None` is the module's halt, while the
  drive sends it to A5.  `run_ren` therefore needs no extra hypothesis -- a
  *running* module never sits on its halting cell, because it has no row there.
* `k_block_ren`, `k_block_drive`: the module's pre-block run lifted into the
  drive, in `k_pre (S x) G d` steps.
* `k_block_drive_exit`: the block plus the handover step the module does not
  have.  K7 over a blank spends one step and turns the drive round into A5 on the
  erased count.  This is what makes one stage a single run with an exact cost.

### The round, and what is still only measured

One round of the drive -- erase one counter mark, run module K once, walk back to
the decision state -- enters as

    R1, on, on :: zeros m ++ ones v ++ bl :: on :: []

(m holes between the counter and the value, v marks of value) and leaves as

    R1, L, on, on :: zeros (m+v+2) ++ ones (2v+1) ++ bl :: on :: []

with the same L: the counter is one mark shorter, the gap is m+v+2, the value is
2v+1.  `tools/round_cost.py` cuts the real trace into rounds, reads m and v off
the tape at each entry -- so the parameters are measured, not assumed -- and
checks

    cost = 2*m + 7*v + 14 + k_pre v 0 0

against `k_pre` transcribed from `rocq/ModuleK.v`.  It checks 40 pure rounds --
every round whose trace never touches the stage branch or the fuel phase -- for
counter sizes n = 1..4 and two values, with m up to 85 and v up to 63: all 40
agree.  Rounds that straddle a stage transition do not satisfy the law and are
counted separately, which is the honest shape of the claim: the law is about the
loop, not about the whole machine.

The loop is now partly a theorem.  `Eps0Drive.v` carries the walks, each proved
by induction on the length of the run it crosses, with a concrete instance beside
it so that the evaluator arbitrates the shape:

    walk_bl_R4      m blanks then the first mark, from R4        m+2 steps, exit R5
    walk_hit_R4     the mark already under R4                    1 step,  exit R5
    walk_on_R5      k marks walked over, from R5                 k+2,     exit R6
    walk_bl_R5      the wall mark under R5                       1,       exit R6
    walk_bl_A5      m blanks then the mark, from A5              m+2,     exit A6
    walk_on_A6      the 2v+1 counter marks, from A6              k+2,     exit A7
    walk_A9         the 2v+2 index marks, from A9                k+2,     exit AA
    walk_AA         m+v+1 gaps crossed, from AA                  k+2,     exit R1

and four "phase" lemmas built on them, all parametric in the value length v:
`walk_R4_phase` (m+1 steps to R5), `walk_A5_phase` (v+3), `walk_A6_phase` (2v+3)
and `walk_A9_phase` (2v+4).  `round_v0` then assembles one whole round --
R1, R2, R4, R5, R6, the K block, A5, A6, A7, A8, A9, AA, back to R1 -- in
`round_sum m 0` steps for a value of length one, with the counter short by one,
the gap m+3 and the value 3, exactly as the measurement says for v = 0.

Still owed is the general v.  The return side is already parametric, so what
remains is the R5/R6 splice for v >= 1: the v passed marks each take one step,
the K entry absorbs them as `ones (S v)`, and the assembled statement must carry
`ones (S v)` where `round_v0` carries `ones 1`.  Until that is written, a round
of arbitrary value length is a checked measurement (40 of them, 0 mismatches)
plus proved phase lemmas, not a theorem.
