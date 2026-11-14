# Longitudinal analysis of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`

This note records what has been established about the 2-state, 5-symbol Turing machine

| state | 0     | 1     | 2     | 3     | 4     |
|-------|-------|-------|-------|-------|-------|
| `A`   | `1RB` | `2LA` | `3LB` | `4LB` | halt  |
| `B`   | `0LA` | `4LB` | `3RA` | `4LA` | `0RB` |

started on the all-blank tape, and which parts of the argument are machine-checked in the
accompanying Lean development.

The only halting transition is `A` reading `4`, so "never halts" is the statement that the
machine is never in state `A` on a cell containing `4`.

## 1. The longitudinal (per-column) picture

Reading the space-time diagram *column by column* rather than row by row, an
extremely regular pattern appears.  After a short transient, **every** tape cell is
visited in a period-`6` pattern of (state, read, write) triples

```
A:0→1 , A:1→2 , B:2→3 , A:3→4 , B:4→0 , B:0→0 ,  A:0→1 , …
```

so each cell runs through the value cycle `0 → 1 → 2 → 3 → 4 → 0 → 0 → 1 → …`.
In particular a cell holding `4` is always read next *in state `B`* — which is precisely
why the machine does not halt, as long as every cell stays in this regime.

Two numbers describe a cell at a given time: its *phase* (how far it has advanced in the
`6`-cycle) and, comparing neighbours, the *phase gradient*.  Two kinds of region occur:

* **Bulk**: the phase drops by `2` per cell as one moves right.  The tape contents are
  then `3`-periodic in space; the six possible `3`-cell blocks are
  `042`, `103`, `204`, `310`, `420`, `031`.
* **Walls**: the phase is constant over a run of cells.  On the tape these show up as
  runs of a single symbol, most often long runs of `2`.

## 2. The bulk: six sweep rules  *(proved — `RequestProject/Blocks.lean`)*

A bulk region is crossed by the head in a single sweep, `3` steps per block, without any
change of state.  Each sweep advances every cell by one place in the `6`-cycle:

```
042  --(A, rightwards)-->  103
103  --(A, leftwards) -->  204
204  --(B, rightwards)-->  310
310  --(B, leftwards) -->  420
420  --(B, rightwards)-->  031
031  --(A, leftwards) -->  042
```

`sweep_042`, `sweep_103`, `sweep_204`, `sweep_310`, `sweep_420`, `sweep_031` prove these
for every number `k` of blocks: the sweep takes exactly `3k` steps, the head ends just
outside the region, and nothing outside the region is touched.  They are derived from six
`3`-step block rules (`blockR_042`, …) by the generic induction lemmas `chainR`/`chainL`
in `RequestProject/Sweeps.lean`.

## 3. The blank right end  *(proved — `RequestProject/RightEnd.lean`)*

At the blank right end the six sweeps turn around in three different ways:

* `turn_A_blank`: `A` at `0 0` writes a single `2` and reverses (3 steps);
* `turn_B_two`: `B` at `2 0 0` leaves `4 2 0` and reverses (5 steps);
* `turn_B_four`: `B` at `4 2 0 0` leaves `0 4 2 0` and reverses into state `A` (7 steps).

Composing these with the sweeps gives `bounce_042`, `bounce_204`, `bounce_420`, which are
unconditional (they constrain only the tape to the right of the region).  Their net
effect is that **one full `6`-sweep cycle extends the bulk by exactly one `3`-cell block
on the right**: the `0 4 2` produced by `turn_B_four` is a brand new bulk block already in
the correct phase.  The right end therefore contributes `18k + 15` steps per cycle for a
bulk of `k` blocks, and grows linearly in the number of cycles.

## 4. Walls  *(proved — `RequestProject/Walls.lean`)*

A run of `2`s is *not* crossed in one sweep.  Instead a marker `0 3` travels through the
wall two cells at a time, leaving `1`s behind, in a period-`8` ping-pong:

```
… 0 3 [A]2 2 …   --8 steps-->   … 1 1 0 3 [A]…
```

(`wall_step`), and hence `wall_chain`: the marker crosses `2n` wall cells in `8n` steps.

What happens at the far end of the wall depends on the parity of its length.

* **Even length.**  The marker consumes the whole wall and the head continues rightwards
  as an ordinary `A` sweep.  The net effect is that the wall moves one block to the left
  (and is re-created one phase earlier, as a run of `1`s).
* **Odd length.**  One `2` is left over.  `wall_odd_end` (10 steps) turns the last three
  cells `0 3 2` into `1 1 1`, after which the head runs back leftwards over the whole run
  of `1`s turning them into `2`s (`ones_left`, one step per cell).  The combined theorem
  `wall_odd` states: a wall of `2n+1` cells preceded by a bulk block `1 0 3` and followed
  by a `0` becomes a wall of `2n+4` cells in exactly `10n + 14` steps, with the head
  emerging to the left in state `A`.

So a wall of odd length **eats one bulk block per visit** — this is the mechanism that
creates the nested triangular structures visible in the space-time diagram.

## 5. The left end: what is still missing

One left-end rule is proved (`left_blank_extend`, `RequestProject/LeftEnd.lean`): when the
head in state `A` steps onto a blank cell with blanks on both sides, it writes `1 3` to
its left and moves one cell right in `5` steps, still in state `A` reading the same
symbol.  This is how the tape grows on the left.

Apart from that, the irregular region at the *left* end of the tape — where new walls are
created — is the remaining gap.

Empirically (the observations below come from direct simulation and are **not** part of
the Lean development):

* Let `E_n` be the `n`-th time at which the head stands on a blank cell with only blanks
  to its left, in state `A`.  These events occur every `3` cells: the head at `E_n` is at
  position `-3n`, so the left end grows by three cells per event.
* The tape word to the right of the head at `E_n` always begins `0 4 4 2`, and the
  next few symbols cycle with period `3` in `n` through the three shapes
  `0442 0 4444 …`, `0442 2 04204 …`, `0442 2 43 204204 …`.
* The gaps `T_{n+1} - T_n` are exactly `31` whenever `n ≡ 2 (mod 3)`; among the remaining
  gaps, every third one is `99`; and so on.  The gap sequence has a clear `3`-adic
  (odometer-like) hierarchy, and stretches of length `27` of it recur verbatim.
* Written in terms of the regions of §1, the tape at `E_n` is a short left prefix followed
  by an alternating sequence of bulk regions and `2`-walls.  The prefix evolves through a
  fixed sequence of shapes while a suffix stays frozen; when the prefix sequence "runs
  out", a piece of it is absorbed into the frozen suffix and the same sequence of shapes
  restarts.  Earlier words re-appear verbatim as factors of later ones — this is the
  self-similarity that makes the space-time diagram look fractal.

A complete proof needs a set of configuration shapes (with a list of counters, since the
number of walls is unbounded) that contains the initial configuration and is closed under
the macro-steps of §§2–4.  The theorems proved here supply the closure rules for
everything except the left-end region.

## 6. Contents of the Lean development

| file | contents |
|------|----------|
| `RequestProject/Machine.lean`    | states, symbols, configurations, the transition function, `run`, `Halted` |
| `RequestProject/Sweeps.lean`     | `3`-periodic patterns and the generic sweep-induction lemmas `chainR`, `chainL` |
| `RequestProject/Blocks.lean`     | the six block rules and the six sweep theorems; the right-end turn-arounds `turn_A_blank`, `turn_B_two` |
| `RequestProject/RightEnd.lean`   | `turn_B_four` and the three bounce theorems |
| `RequestProject/Walls.lean`      | `wall_step`, `wall_chain`, `wall_odd_end`, `ones_left`, `wall_odd` |
| `RequestProject/LeftEnd.lean`    | `left_blank_extend` |
| `RequestProject/NonHalting.lean` | `Halted` is absorbing; a kernel-checked `500`-step run; the statement `never_halts` (still open) |

Every theorem listed above is proved without `sorry` except `never_halts`, which is
explicitly left open.

---

# Part II — the block ("generalized longitudinal") description

The analysis above describes the tape as a `3`-periodic bulk interrupted by walls of `2`s.
There is a better coordinate system, which makes *all* the regions instances of one
family and which is what the second round of work is based on.

## 7. The tape is a sequence of blocks `0 4^j 2`

Look at what the head can do while moving **rightwards**.  The only transitions that move
right are `A:0 → 1RB`, `B:2 → 3RA` and `B:4 → 0RB`.  So a rightward excursion starting in
state `A` reads exactly the words

```
0 4^{j₁} 2 · 0 4^{j₂} 2 · … · 0 4^{jₘ} 2
```

and it rewrites each block `0 4^j 2` as `1 0^j 3`, taking `j + 2` steps per block and
staying in state `A` at every block boundary.  Direct simulation confirms that at the
start of every long rightward excursion the tape really is such a word, with arbitrary
exponents; e.g. at step `1065` the head reads

```
0 2 · 0 4 2 · 0 4 2 · 0 4^10 2 · (0 4 2)^8 · 0 0
```

In this language the two kinds of region of §1 are simply

* **bulk** = a block with `j = 1`;
* **wall** = a block with `j ≥ 2` (the run of `4`s, which becomes a run of `0`s after the
  sweep and a run of `2`s and then of `1`s in later phases).

The block exponents are what the space-time diagram is made of: the fractal picture is the
evolution of the *exponent sequence*.

## 8. The complete local rule set

After a rightward sweep the tape reads `1 0^{j} 3` per block, and the head comes back
leftwards.  The leftward pass depends on `j`, and that is where all the structure is:

| block | rule | steps | result | after |
|-------|------|-------|--------|-------|
| `1 3`       (`j=0`) | `blockL_13`   | `2` | `4 4`     | head continues left in state `B` |
| `1 0 3`     (`j=1`) | `sweepL_103`  | `3` | `2 0 4`   | head continues left in state `A` |
| `1 0 0 3`   (`j=2`) | `blockL_1003` | `6` | `2 2 0 4` | head continues left in state `A` |
| `0 0 0 3` (`j≥3`, right end of a wall) | `turn_wall` | `9` | `1 3 1 0` | head **turns around**, state `B` |

So a leftward sweep crosses every small block and is *reflected* by the first block with
`j ≥ 3`, eating two cells of it.  This is the mechanism behind the triangles of the
space-time diagram, and `bounce_wall_bulk` proves the whole triangle at once: for every
`k`, a wall end followed by `k` bulk blocks is entered on the right in state `A` and left
again on the right in state `B` after exactly `6k + 9` steps.

Together with the *chain rules* — a run of `1`s crossed leftwards in state `A` (becoming
`2`s) or `B` (becoming `4`s), a run of `4`s crossed rightwards in state `B` (becoming
`0`s), a run of `3`s crossed leftwards (becoming `4`s) — and the two end rules
(`left_blank_extend` on the left, the turn-arounds of `RightEnd.lean` on the right), this
is an essentially complete description of the machine's behaviour.

**Coverage experiment** (simulation, `sim/cover2.py`; *not* machine-checked).  Simulating
the machine and applying, at every step, whichever of the proved macro rules matches:

| steps | covered by macro rules | distinct contexts with no matching rule |
|-------|-----------------------|------------------------------------------|
| `50 000` | `94.06 %` | `75` |
| `200 000` | `95.85 %` | `75` |
| `1 000 000` | `97.79 %` | `75` |
| `3 000 000` | `98.33 %` | `75` |

The remaining steps are single steps at the junctions between regions; the set of local
situations in which they occur does not grow, which is evidence that the rule set above is
complete.

## 9. What a proof still needs, and one thing that is ruled out

Non-halting means the machine never reads a `4` in state `A`.  Unwinding the transition
table, that happens only if one of the four local patterns

```
[B]2 4        4 [A]1        4 [B]0        4 [B]3
```

ever occurs.  None of them occurs in `2 000 000` simulated steps (the set of triples
`(state, tape[p-1], tape[p], tape[p+1])` that occur has only `41` elements), but that is
of course not a proof.

*Purely local invariants do not suffice.*  `sim/ctl.py` runs the saturation of the
strongest invariant of the form "every tape word of length `w` belongs to `P`, and the
`(state, width-(2k+1) window)` view of the head belongs to `H`", starting from the blank
tape.  For every sound parameter pair (`2k+1 ≥ 2w-1`, which is needed for the abstraction
to be an over-approximation) up to `w = 6` the saturation reaches a configuration with `A`
reading `4`; so no invariant of this shape can prove non-halting, and the argument must
use the *sequence* of regions and not just a bounded window.

What is still missing is exactly this global bookkeeping: a description of which sequences
of block exponents can occur, closed under the rules of §8.  The exponent sequence at the
left-end events is highly structured (the left end is always `0 2 · 0 4 4 2 · 0 4^4 2 …`
and the head moves `9` cells further left between consecutive full sweeps) and it has a
clear self-similar hierarchy, but a closed description of it has not been found.

## 10. Contents added in Part II

| file | contents |
|------|----------|
| `RequestProject/Words.lean`     | words on the tape (`Seg`), the macro-rule predicates `SweepR`, `SweepL`, `Bounce`, and their composition lemmas |
| `RequestProject/Chains.lean`    | the one-cell rules, repetition of rules, the run rules (`run_fours`, `run_ones_A`, `run_ones_B`, `run_threes`), the block rule `blockR` for an arbitrary exponent, the sweep `sweepR_blocks` of an arbitrary *list* of blocks, and `sweepL_103`/`sweepL_bulk` |
| `RequestProject/Bounces.lean`   | the six bulk sweeps in the new framework, `blockL_13`, `blockL_1003`, the wall turn-around `turn_wall`, and the triangle `bounce_wall_bulk` |
| `RequestProject/Excursion.lean` | macro rules certify non-halting over their duration (`SweepR.no_halt`, …) and the complete left-end excursion `left_end_sweep` |

Everything listed there is proved without `sorry`; `never_halts` is still open.

## 11. The crossing sequences (the longitudinal picture proper)

The most compact form of the longitudinal picture is the *crossing sequence* `X_i`: the
sequence of states in which the head crosses the boundary between the cells `i-1` and `i`
(crossings at a fixed boundary alternate in direction, so the word over `{A, B}` carries
all the information).  Simulation gives a very clean answer (`sim/cross.py`, again *not*
machine-checked):

* for every column `i ≥ 1`, `X_i = B (AAABBB)^ω` exactly — **no** transient at all;
* for every column `i ≤ 0`, `X_i = P_i · (AAABBB)^ω` with a finite transient `P_i`.

The transients are genuinely finite: running to `500 000`, `2 000 000` and `8 000 000`
steps leaves the measured transient lengths unchanged (`|P_0| = 9`, `|P_{-10}| = 39`,
`|P_{-20}| = 93`, `|P_{-30}| = 95`, `|P_{-40}| = 121`), while the crossing sequences
themselves keep growing.

The periodic word `(AAABBB)^ω` with alternating crossing directions is exactly the
period-`6` visit pattern `A:0, A:1, B:2, A:3, B:4, B:0` of §1 — the state `B` is the one
that reads the `4`, which is why a cell in this regime never halts the machine.  So the
whole question is the behaviour of the finite transients `P_i` as `i → -∞`: they are the
image of one another under the (deterministic) column transducer, and they are what the
fractal is made of.

---

# Part III — the token description of the left end

Parts I and II described the tape as a sequence of blocks `0 4^j 2`.  The parse used there
only fits the tape at the *start of a rightward excursion*; the description below fits the
tape at a *recurring, canonical moment*, and it fits it exactly, every time.

## 12. The synchronisation moment and the token alphabet

Call a **left event** a moment at which the head stands on a cell strictly to the left of
every cell it has visited before.  Left events happen one per cell of leftward growth, and
they come in groups of three: at every third left event the machine is in state `B`, with
the head on the leftmost non-blank cell.  Call those the **`B`-events**; they are the
synchronisation moments used from here on.

At every `B`-event of the first `8 000 000` steps the non-blank part of the tape, read
from the head rightwards, is a concatenation of exactly two kinds of word:

```
U(a,b) = 0 4^a 2^b      (a ≥ 1, b ≥ 1)
V(c)   = 4 3 2^c        (c ≥ 1)
```

and the parse is unique.  Moreover, over those `2 470` `B`-events:

* the word always begins with `U(2,1)` or `U(2,2)`, and always ends with `U(a,1)`;
* no two `V` tokens are adjacent, and no word starts with `V`;
* every `V` is *preceded* by a `U(a,b)` with `a ∈ {1,2}` and `b` even, `b ≥ 2`, and is
  *followed* by `U(1,1)`;
* in every `U(a,b)` with `b ≥ 2` one has `a ∈ {1,2}` and `b` even; the exponents `a ≥ 3`
  only occur with `b = 1`, and the observed values are `a ∈ {1,2,4,10,28,82,244,730}`,
  i.e. `a = 2` or `a = 3^k + 1`;
* every `V(c)` has `c` odd.

These are *observations*, not theorems.  What makes the alphabet natural is the shape of
the machine's rightward moves — `A:0 → 1RB`, `B:2 → 3RA`, `B:4 → 0RB`.  A rightward
excursion started in state `A` on a `0` reads exactly `0 4^{a} 2`, rewrites it as
`1 0^{a} 3` and returns to state `A`; so it walks through all the tokens with `b = 1` and
is **turned around by the first token with `b ≥ 2`**.  Note also that it would *halt* if a
token `U(a,1)` were followed by a `V`, since it would then read a `4` in state `A`: the
constraint "a `V` is preceded by a `U(a,b)` with `b ≥ 2`" is exactly what forbids this.

## 13. The three phases

Written in the token alphabet, the first `B`-events are

```
 n     tape at the n-th B-event
 1     U2,1
 4     U2,2 u
 7     U2,2 V1 u
10     U2,1 U4,1 u^2
13     U2,2 u    U2,1 u^3
16     U2,2 V1 u U2,1 u^3
19     U2,1 U4,1 U1,4 u^4
22     U2,2 u    U2,8 u^4
25     U2,2 V1 u U2,8 u^4
28     U2,1 U4,1 U1,4 V5 u^5
31     U2,2 u    U2,8 V1 u^7
34     U2,2 V1 u U2,8 V1 u^7
37     U2,1 U4,1 u^2 U2,2 V1 u^10
…
```
(`u` abbreviates `U(1,1)`.)  The left end therefore cycles through three shapes

```
P1 :  U(2,1) U(4,1) · R
P2 :  U(2,2) u      · R
P3 :  U(2,2) V(1) u · R
```

and the three transitions `P1 → P2 → P3 → P1` are what has to be understood.

## 14. The three transitions are *local* rules with a carry

**`P2 → P3` is completely local** (proved, `rule_P2` in `RequestProject/LeftRules.lean`):
in exactly `31` steps the machine inserts the token `V(1)` and leaves everything else
alone.  Only the nine cells `p-3 … p+5` are read or written, so the rest of the tape is
arbitrary:

```
… 0 0 0 · 0 4 4 2 2 · 0 …   --31 steps-->   … 0 4 4 2 2 · 4 3 2 · 0 …
        ↑ head (state B)     ↑ head (state B)
```

**`P1 → P2` and `P3 → P1` move a "carry" of twos to the right.**  When the token after the
prefix is `U(1,2m)` they, too, are local (checked by direct simulation; not yet proved):

```
P1 :  0 0 0 · U(2,1) U(4,1) U(1,2m) 0   --(59+20m) steps-->  U(2,2) u    U(2,2m+4) 0
P3 :  0 0 0 · U(2,2) V(1) u U(1,2m) 0   --(71+20m) steps-->  U(2,1) U(4,1) U(1,2m+4) 0
```

(the trailing `0` is the first cell of the next token, and the rule requires `m ≥ 1`; for
*odd* `b` the head runs further to the right and the rule is different).  In general the
two rules are "deliver a carry of `4` twos to the first token with `b ≥ 2`", with the
following local behaviour of the tokens the carry passes through:

| token met by the carry `k` | becomes | carry passed on |
|---------------------------|---------|-----------------|
| `U(1,1)` (`= u`)          | `u`     | `k` |
| `U(1,b)`, `b ≥ 2`         | `U(1,b+k)` | absorbed (rule ends) |
| `U(2,1)`                  | `U(1,4)` | `k − 2` |
| `U(2,b)`, `b ≥ 4`         | `U(1,4) V(b−3)` | `k − 2` |
| `V(c)`, `c > k`           | `V(c−k)` | `k` |

and `P1` additionally raises the exponent `a` of the first token of `R` by one
(`u ↦ U(2,1)`, `U(1,b) ↦ U(2,b+…)`).  This is exactly the reason the machine is not a
"bouncer": the carry keeps escaping to the right, so the three phases never close into a
finite cycle.

## 15. The fractal: `U(a,1)` unfolds into an earlier tape

The exponents `a ∈ {4, 10, 28, 82, 244, 730}` — that is, `3^k + 1` — are where the
self-similarity lives.  When a carry reaches such a token it *unfolds* it into a piece of
tape that is a copy of an earlier configuration of the machine, e.g. (rules read off the
simulation, carry entering with `k = 4`):

```
U(4,1)  u        ↦  u   U(1,2)                     carry 6
U(10,1) u u      ↦  u u U(4,1)                     carry 10
U(28,1) u u u    ↦  u u U(4,1) U(1,4) V(5)         carry 18
```

and `U(4,1) U(1,4) V(5)` is precisely the prefix the tape had at the `28`-th `B`-event.
So a big `4`-run is a *compressed copy of the past*, and the space-time diagram is a
picture of these copies being unpacked at every scale.  This is the mechanism behind the
nested triangles of §4 and the fractal appearance of the diagram.

## 16. What a complete proof still needs

The above turns the problem into a question about a rewriting system on words over the
token alphabet: one has to exhibit a set `L` of token words, containing the tape at the
first `B`-event, such that

1. every word of `L` satisfies the adjacency constraints of §12 (this is what rules out
   the halting pattern `… 2 [B]4 …` at a `U`–`V` junction), and
2. `L` is closed under the three phase transitions of §14.

`L` cannot be all words satisfying the constraints of §12 — randomised testing finds words
of that shape from which the machine halts within a few hundred steps.  The extra
conditions needed are exactly the unfolding constraints of §15, i.e. a statement of the
form "a token `U(a,1)` with `a ≥ 3` is always followed by enough `u`s to absorb its
unfolding".  Making that precise, and checking closure, is the remaining gap.

## 17. Contents added in Part III

| file | contents |
|------|----------|
| `RequestProject/Local.lean`     | the window tape `Tape`, the list-level simulator `lstep`/`lrun`, its soundness, and the predicate `Win` for *local* macro rules together with `Win.of_lrun` (discharge a local rule by `decide`) and `Win.no_halt` |
| `RequestProject/Tokens.lean`    | the tokens `tokU a b = 0 4^a 2^b`, `tokV c = 4 3 2^c` and the word of a list of tokens |
| `RequestProject/LeftRules.lean` | `Win.embed`, `Win.trans` and the local rule `rule_P2` (`31` steps, arbitrary rest of tape, certified non-halting) |

The exploratory scripts for Part III are `sim/tok.py`, `sim/rules2.py`, `sim/closure.py`,
`sim/verify_local.py` and `sim/selfsim.py`; as before, nothing they print is
machine-checked.

---

# Part IV — the anatomy of one macro step, and the fractal identity

Part III described the tape at a `B`-event in the token alphabet and listed the three
phase transitions.  This part opens up *what the machine actually does* between two
`B`-events, and states the self-similarity precisely.

## 18. The five ingredients of a macro step

Between two consecutive `B`-events the head performs the following, in this order.

1. **A short fixed prologue at the left end**, depending only on which of the three phases
   `P1`, `P2`, `P3` the tape is in.
2. **A rightward sweep in state `A` over blocks `0 4^a 2`.**  Writing the tape from the
   head as a sequence of blocks, a rightward excursion started in state `A` on a `0`
   rewrites `0 4^a 2` as `1 0^a 3` in `a+2` steps and arrives at the next block, again in
   state `A` — this is `blockR` / `sweepR_blocks` of Part II.  It therefore runs through
   all the tokens with `b = 1` and is **turned around by the first token with `b ≥ 2`**.
3. **A turn-around inside the run of `2`s**: the marker `1 0 3` left behind by the sweep
   ping-pongs into the run two cells at a time (8 steps per two cells) until the run is
   exhausted, and comes back leaving `1`s, which the return sweep turns into `2`s.  The
   complete round trip is `cross_back` (`RequestProject/Cycle.lean`): a run of `2n+1`
   twos becomes a run of `2n+4` twos in exactly `10n+14` steps.  **This is where the four
   extra `2`s — the "carry" of §14 — are deposited.**
4. **A leftward return sweep in state `A`** over the blocks that were crossed in step 2:
   `1 0^a 3 → 2 0^a 4` for `a = 1` (`sweepL_103`), `1 0 0 3 → 2 2 0 4` for `a = 2`
   (`blockL_1003`) — but a block with `a ≥ 3` **reflects** the head instead of letting it
   pass (`turn_wall`).
5. If the head was reflected, steps 2–4 repeat from the reflection point; the reflection
   is what makes one macro step consist of *two* passes in the `P1` and `P3` phases (the
   reflecting block being the `U(4,1)` of the prefix), and it is also the mechanism by
   which a long `4`-run deeper in the tape is unpacked.

So one macro step advances every block of the bulk by two of the six phases of the cell
cycle `0 4 2 → 1 0 3 → 2 0 4 → 3 1 0 → 4 2 0 → 0 3 1 → 0 4 2`, and pushes four extra `2`s
into the first run of `2`s that is long enough to absorb them.

## 19. The carry table, probed in isolation

`sim/probe.py` sets up an artificial tape `0 0 0 · <prefix> <test tokens> u^N` with the
head in state `B` on the first cell, runs to the next `B`-event and prints the result.
With the `P3` prefix (so that an untouched carry of four `2`s arrives at the test tokens),
the outcome for a single test token is:

| token met by the carry | becomes | then |
|---|---|---|
| `U(1,1) = u`         | `u`                | carry passes on |
| `U(1,b)`, `b` even, next token not a `V` | `U(1,b+4)` | absorbed |
| `U(1,b)`, `b` odd ≥3 | unchanged          | carry passes on |
| `U(2,1)`             | `U(1,4)`           | a carry of `2` passes on |
| `U(2,b)`, `b ≥ 3`    | `U(1,4) V(b−3)`    | a carry of `2` passes on |
| `U(2,2)`             | — | the machine **halts** |
| `U(a,1)`, `a = 3j+1` | see §20           | carry passes on |
| `U(a,1)`, `a ≢ 1 (3)`, `a ≥ 3` | — | the prefix is destroyed, or the machine halts |
| `U(1,b) V(c)`, `b` even, `c` even | `U(1,b+4) V(c)` | absorbed |
| `U(1,b) V(c)`, `b` even, `c` odd ≥5 | `U(1,b+4) V(c−4)` | carry passes on |
| `U(1,b) V(1)`, `U(1,b) V(3)` | — | the machine **halts**, or the prefix is destroyed |

A carry of `k` that runs off the right end of the tape creates `k/2` new `u` tokens there.

The table makes precise which adjacency constraints of §12 are *needed*: the observed
tapes only ever present the machine with the safe rows.  In particular the refinement
found by counting over `8 000 000` steps — in a pair `U(a,b) V(c)` one always has
`a = 2 ⟹ c = 1` and `a = 1 ⟹ c ≥ 3` — is exactly what keeps the dangerous rows
(`U(2,2)`, `V(1)`, `V(3)`) out of reach of a carry.  Randomised tapes that satisfy only
the §12 constraints but violate this one do halt, usually within a few hundred steps.

## 20. The fractal identity

Let `W_0, W_1, W_2, …` be the token words at the successive `B`-events
(`W_0 = U(2,1)`, `W_1 = U(2,2) u`, `W_2 = U(2,2) V(1) u`, `W_3 = U(2,1) U(4,1) u^2`, …),
and let

```
core(W) = W with its first token and its trailing run of u removed.
```

**Identity.**  When a carry of four `2`s reaches a token `U(3j+1, 1)`, that token unfolds
into

```
u u        · core(W_j)      if W_j begins with U(2,1)      (phase P1)
u U(1,2)   · core(W_j)      if W_j begins with U(2,2)      (phases P2, P3)
```

and the carry passes on.  In other words **a `4`-run of length `3j+1` is a compressed copy
of the tape at the `j`-th `B`-event**, and the space-time diagram is the picture of these
copies being unpacked, at every scale at once.  (`sim/fractal.py` checks the identity for
`j = 0, …, 25`, i.e. for `4`-runs up to length `76`; as everywhere in this file, this is
simulation, not a machine-checked proof.  The two smallest instances, `j = 1` and `j = 3`,
*are* machine-checked, as `unfold_U4` and `unfold_U10` in `RequestProject/Carry.lean`.)

This explains at one stroke several of the observations of Part III:

* why the exponents `a ≥ 3` that occur are `4, 10, 28, 82, 244, 730, …` — those are the
  `3j+1` for which `U(3j+1,1)` is actually created, namely `a = 3^k + 1`;
* why `U(28,1)` unfolds into `u u U(4,1) U(1,4) V(5)` — because `W_9`, the tape at the
  `9`-th `B`-event, is `U(2,1) U(4,1) U(1,4) V(5) u^5`;
* why the machine is not a bouncer: the compressed copies are created faster than they are
  unpacked.

## 21. What is now machine-checked

| file | contents |
|------|----------|
| `RequestProject/Local.lean`     | the window tape, the list simulator `lstep`/`lrun`, the predicate `Win` for local macro rules, `Win.of_lrun` (discharge by `decide`) and `Win.no_halt` |
| `RequestProject/Tokens.lean`    | the tokens `tokU a b`, `tokV c` |
| `RequestProject/LeftRules.lean` | `Win.embed`, `Win.trans`, the bridges `Win.of_sweepR`/`Win.of_sweepL`, the rule `rule_P2`, and the ping-pong chain `pingpong_chain` |
| `RequestProject/Cycle.lean`     | `onesBack`, `cross_back` (the complete round trip through a run of `2n+1` twos, `10n+14` steps, any `n`), and the two left-end rules `rule_P1` (`79+20m` steps) and `rule_P3` (`91+20m` steps) |
| `RequestProject/Carry.lean`     | `rule_P3_gen`: the `P3` rule with an arbitrary run of `r` tokens `u` between the prefix and the absorbing token, in exactly `91 + 12r + 20m` steps; and `unfold_U4`, `unfold_U10`: the two smallest instances of the unfolding of §20, checked outright (`157` and `379` steps) |

Every one of these is a `Win` rule, so each also certifies that the head never leaves the
stated window — the rest of the tape is arbitrary and untouched — and that the machine
does not halt at any of the steps it covers.

## 22. What a complete proof still needs

The remaining gap is unchanged in kind but much better localised.  What is missing is a
rule for the carry meeting a token `U(a,1)` with `a ≥ 3` — i.e. a *parametric* version of
the reflection of step 5 of §18 — together with the induction that §20 suggests: the
unfolding of `U(3j+1,1)` reproduces the tape at the `j`-th `B`-event, so a proof by strong
induction on `j` has exactly the right shape.  The two things that must be carried through
the induction are

1. the adjacency constraints of §12 together with the refinement of §19 (these are what
   keep the halting rows of the carry table unreachable), and
2. the invariant that a token `U(3j+1,1)` is always followed by material that matches the
   tail of `W_j`.

## 23. Exploratory scripts added in Part IV

`sim/toklib.py` (token parsing, no side effects), `sim/be.py`, `sim/be2.py`, `sim/be3.py`
(the `B`-event sequence and the token-level transitions, with the reach of the head),
`sim/probe.py` (the carry table of §19), `sim/winchk.py`, `sim/wintrace.py`, `sim/pieces.py`
(checking candidate window rules and finding their phase decomposition) and
`sim/fractal.py` (the identity of §20).

---

# Part V — why the diagram is self-similar: a swept `4`-run is blank tape

Part IV stated the fractal identity — a token `U(3j+1,1)` unfolds into a copy of the tape
at the `j`-th `B`-event — as an empirical fact.  This part explains *why* it holds, which
turns it from a numerical coincidence into a structural statement, and reports the new
machine-checked rules that the explanation suggests.

## 24. The two "virtual blank tapes"

Two observations, both easy to state and both confirmed by simulation:

* **A `4`-run becomes a `0`-run.**  A rightward sweep in state `A` rewrites the token
  `U(a,1) = 0 4^a 2` as `1 0^a 3` (`blockR`, Part II).  So after the sweep the `4`-run
  *is* a finite piece of tape filled with `0`s — indistinguishable, for the machine, from
  the blank tape at the left end.
* **Every left-end rule needs only three blank cells.**  `rule_P2`, `rule_P1`, `rule_P3`,
  `rule_P1_gen`, `rule_P3_gen`, `rule_P3_U21` are all `Win` rules whose window begins with
  exactly `0 0 0`, and a `Win` rule certifies that the head never leaves its window.  So
  each of them applies verbatim wherever the tape happens to carry three `0`s followed by
  the pattern the rule asks for — in particular inside a `0`-run.

Put together: after the sweep the machine performs *its own* left-end macro steps inside
the former `4`-run, each consuming three cells of it.  A run of `3j+1` fours therefore
hosts exactly `j` macro steps of the machine's own computation before running out.  That
is the fractal identity.

This is visible directly in the simulation (`sim/self2.py`).  Running the machine on
`0 0 0 · U(2,2) V(1) u · U(22,1) · u^60` and recording every moment at which the head is
in state `B` at a new leftmost cell *inside the former `4`-run* gives

```
off=19   U2,1                     = W_0
off=16   U2,2 u                   = W_1
off=13   U2,2 V1 u                = W_2
off=10   U2,1 U4,1 u              = W_3
off=7    U2,2 u U2,1              = W_4
off=4    U2,2 V1 u U2,1           = W_5
off=1    U2,1 U4,1 U1,4           = W_6
```

(each followed by the padding of `u`s), i.e. the first seven tape words of the machine's
own run, at offsets `3` apart, and `22 = 3·7 + 1`.  The left context at each of these
moments is a run of `0`s, exactly as at a genuine `B`-event.

The right end has the same kind of "virtual blank": at the far right the machine keeps
creating fresh `u = U(1,1)` tokens, so an infinite run `u^ω` behaves like blank tape on
the right.  This is why the padding `u^60` in the probe reproduces the real machine's
behaviour, and why the sub-computation inside a `4`-run starts from the *blank* tape.

**Machine-checked** in `RequestProject/Fractal.lean`: `four_run_to_zero_run` (the sweep
turns `0 4^a 2` into `1 0^a 3`) and `Win.in_zero_run` (a rule whose window starts with
`0 0 0` applies `k` cells inside a run of `k+3` zeros), together with the three instances
`rule_P1_in_run`, `rule_P2_in_run`, `rule_P3_in_run`.

## 25. The carry table for a general carry

§19 tabulated what a carry of **four** `2`s does.  Tracking the orbit token by token gives
the rule for a carry of `k` `2`s.  Writing the tokens as cell counts
(`U(a,b)` occupies `1+a+b` cells, `V(c)` occupies `2+c`), the transducer *conserves cells*
and the carry is exactly the number of cells still to be delivered:

| token met by a carry of `k` | becomes | carry passed on |
|---|---|---|
| `U(1,1) = u` | `u` | `k` |
| `U(1,b)`, `b ≥ 2`, next token not a `V` | `U(1,b+k)` | absorbed |
| `U(1,b) V(c)`, `b ≥ 2`, `c > k` | `U(1,b+k) V(c−k)` | `k` |
| `U(2,1)` | `U(1,k)` | `2` |
| `U(2,b)`, `b ≥ 2`, next token not a `V` | `U(1,k) V(b−k+1)` | `k − 2` |
| `U(a,1)`, `a = 3j+1 ≥ 4` | the unfolding of §20 | grows |
| end of tape (blank) | `k/2` new `u` tokens | — |

In the phase `P1` the first token after the prefix additionally has its exponent `a` raised
by one.  Each row is consistent with the cell count: e.g. `U(2,1) → U(1,k)` grows the token
by `k − 2` cells, which is exactly the amount of carry it consumes.  (These rows are read
off the orbit and from `sim/probe.py`; three of them are now proved outright, see §26.)

## 26. New machine-checked rules

| theorem | file | statement |
|---|---|---|
| `rule_P1_gen` | `RequestProject/CarryP1.lean` | `0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(1,2m+2) 0  →  U(2,2) u · U(2,1) · u^r · U(1,2m+6) 0` in `91 + 12r + 20m` steps |
| `rule_P3_U21` | `RequestProject/CarryU21.lean` | `0 0 0 · U(2,2) V(1) u · u^r · U(2,1) · u^s · U(1,2m+2) 0  →  U(2,1) U(4,1) · u^r · U(1,4) · u^s · U(1,2m+4) 0` in `91 + 12r + 6s + 10m` steps |
| `three_phase_cycle` | `RequestProject/CarryU21.lean` | one full turn `P1 → P2 → P3 → P1`: `0^9 · U(2,1) U(4,1) u^(r+1) U(1,2m+2) 0  →  U(2,1) U(4,1) U(1,4) u^r U(1,2m+8) 0` in `233 + 18r + 30m` steps |
| `four_run_to_zero_run`, `Win.in_zero_run` | `RequestProject/Fractal.lean` | the two halves of §24 |

`rule_P1_gen` completes the pair of "carry crosses a run of `u`s" rules (`rule_P3_gen` was
the `P3` half).  `rule_P3_U21` is the next row of the carry table — `U(2,1) ↦ U(1,4)` with
two `2`s travelling on — with arbitrary runs of `u` on both sides, so it is the first
proved rule in which the carry is *not* absorbed by the token it meets.  `three_phase_cycle`
is the first composite of three consecutive macro steps; it is assembled purely by
composing window rules, which is evidence that the rule format scales.

Each of these is a `Win` rule, so each also certifies that the head never leaves the stated
window and that the machine does not halt during the steps it covers.

## 27. What a complete proof still needs

The picture of §24 localises the remaining gap sharply.  A complete proof would have to
provide, by strong induction on `j`:

1. a *parametric* macro-step theorem — "from a `B`-event with three `0`s on the left and a
   tape word `W` in a suitable class `L`, the machine reaches the next `B`-event three
   cells further left with tape word `F(W)`" — for a class `L` containing `W_0` and closed
   under `F`; and
2. the rows of the carry table that involve a token `U(3j+1,1)`, which by §24 *are* the
   statement that the first `j` macro steps happen inside the run.  This is where the
   induction feeds back into itself, and it is why the induction has to be on `j`.

The rules proved so far give `F` on all words in which the carry meets only tokens `u`,
`U(1,b)`, `U(2,1)` and the absorbing token, with arbitrary run lengths.  What is missing is
the rest of the table (`U(2,b)` with `b ≥ 2`, the pairs involving `V`) and the inductive
step for `U(3j+1,1)`.

## 28. Exploratory scripts added in Part V

`sim/self2.py` (the inner `B`-events of a `4`-run, §24), `sim/carrytab.py` (the input and
output of the carry transducer at every `B`-event transition, §25) and `sim/p1gen.py` (the
general shape of the `P1` rule).  As everywhere in this file, nothing these print is
machine-checked.

---

# Part VI — arbitrary block *shapes*, and a census of the macro steps that occur

Parts III–V proved macro rules in which the free parameters are the *lengths* of runs
(`u^r`, a run of `2`s of length `2m+2`, …).  This part removes that restriction in one
direction — the rule now holds for an arbitrary *sequence* of blocks, not just a run of
equal ones — and then measures, by simulation, exactly which macro rules the real orbit
needs, which turns "what is still missing" into a short finite list.

## 29. The two-pass anatomy, in the form that generalises

Between two `B`-events in the phases `P1` and `P3` the head makes exactly **two** passes
(this is visible in every proof so far: each of them crosses the run of `u`s four times).
Written at the level of cells rather than tokens, a pass is:

1. a rightward sweep in state `A` across blocks `0 4^k 2`, which rewrites each as
   `1 0^k 3` — this is `blockR`/`sweepR_blocks` and is already valid for *arbitrary*
   exponents;
2. a turn-around inside the first run of `2`s that it meets (`cross_back`), which is where
   two of the four `2`s of the carry are deposited;
3. a leftward return in state `A` across the blocks it just crossed, which rewrites
   `1 0 3` as `2 0 4` and `1 0 0 3` as `2 2 0 4` — but is *reflected* by a block
   `1 0^k 3` with `k ≥ 3` (`turn_wall`);
4. a reflection at the `4`-run of the prefix, after which the second pass runs, in state
   `B`, over the words `2 0 4` the return sweep left behind.

The second pass is stopped by the **first `2 2`** it meets, and after the first pass a
`2 2` sits exactly where a block with exponent `k = 2` used to be.  Hence:

> in a block sequence `U(k₁,1) ⋯ U(kₙ,1)` with all `kᵢ ∈ {1,2}`, the first block with
> `kᵢ = 2` absorbs the second half of the carry and becomes `U(1,4)`; every later block is
> touched once in each direction and is simply re-read, with the shifted token boundary, as
> `U(1,kᵢ)`.

That is exactly the content of the two new theorems.

## 30. The two new machine-checked rules

| theorem | file | statement |
|---|---|---|
| `rule_P3_flat` | `RequestProject/Flat.lean` | `0 0 0 · U(2,2) V(1) u · u^r · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2) 0  →  U(2,1) U(4,1) · u^r · U(1,4) · U(1,k₁) ⋯ U(1,kₙ) · U(1,2m+4) 0` in `91 + 12r + 10m + ∑ (4kᵢ + 2)` steps |
| `rule_P1_flat` | `RequestProject/FlatP1.lean` | `0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2) 0  →  U(2,2) u · U(2,1) · u^r · U(1,4) · U(1,k₁) ⋯ U(1,kₙ) · U(1,2m+4) 0` in `91 + 12r + 10m + ∑ (4kᵢ + 2)` steps |

for every `r`, `m`, `n` and every `k₁, …, kₙ ∈ {1,2}`.  Both are `Win` rules, so both also
certify that the head never leaves the displayed window and that the machine does not halt
during the steps they cover (`rule_P3_flat_no_halt`, `rule_P1_flat_no_halt`).  Taking all
`kᵢ = 1` recovers `rule_P3_U21`; these are the first rules of the development that hold for
an arbitrary *shape* of tape word rather than for an arbitrary run length.

The new ingredient they need is the leftward counterpart of `sweepR_blocks`:

* `sweepL_blocks_small` (`RequestProject/Flat.lean`): a concatenation of blocks
  `1 0^{k₁} 3 ⋯ 1 0^{kₙ} 3` with every `kᵢ ∈ {1,2}` is crossed right-to-left in state `A`
  in exactly `∑ 3kᵢ` steps, block `i` becoming `2^{kᵢ} 0 4`.  The hypothesis `kᵢ ≤ 2` is
  exactly what excludes the reflection of §29.4.

together with the two re-reading identities `shift_wordOut` and `shift_wordBack`, which say
that the words the passes leave behind are the same words read with the token boundary
moved — `[0,4] ++ wordBack ks = outW ks ++ [0,4]` is the reason a crossed block `U(k,1)`
comes out as `U(1,k)`.

## 31. A census of the macro steps that actually occur

`sim/shapes.py` classifies every `B`-event of the real orbit by the only data a macro rule
needs: the phase, the exponents of the blocks the rightward pass crosses (all of which have
`b = 1`), the first token with `b ≥ 2` (the one that absorbs the carry), and the kind of
token that follows it.  Over the first `1 000 000` steps (336 `B`-events) there are just **twenty-four** classes.
Writing `r` for the number of tokens the rightward pass crosses before reaching the
absorbing one (`r = 0` means the absorbing token comes immediately after the prefix), and
listing the crossed exponents other than `1`, the whole census is:

```
  37  P1  r=0                absorb U(1,even)  followed by U   <- rule_P1
  37  P1  r=0                absorb U(1,even)  followed by V
  36  P1  r>=1               absorb U(2,even)  followed by V
   2  P1  (carry runs off the right end of the tape)
  37  P3  r=0                absorb U(2,even)  followed by U
  37  P3  r=0                absorb U(2,even)  followed by V
  12  P3  r>=1 one exponent 2   absorb U(2,even)  followed by U
  12  P3  r>=1 one exponent 2   absorb U(2,even)  followed by V
   4  P3  r>=1 one exponent 2   absorb U(1,even)  followed by U   <- rule_P3_flat
   4  P3  r>=1 one exponent 2   absorb U(1,even)  followed by V
   3  P3  r>=1 exponents 2, 10                                    <- the fractal recursion
   3  P3  (carry runs off the right end of the tape)
 112  P2  (every one of them covered by rule_P2, which is unconditional)
```

Three things stand out.

* Every `P2` step is covered by `rule_P2`, which is a nine-cell window rule and therefore
  unconditional; so a third of all macro steps is already closed, whatever the tape.
* The exponents of the crossed blocks are always `1`, except for a single `2` — which is
  precisely what `rule_P3_flat` and `rule_P1_flat` now allow — and, three times in a
  million steps, a `10`, which is the fractal recursion of §20.  So the block sequence in
  front of the carry is *never* complicated; the generality that is actually needed there
  is exactly the generality the new rules provide.
* **The whole remaining gap, apart from the recursion, is the absorbing token and its
  neighbour**: an absorbing token `U(2,b)` instead of `U(1,b)`, and a `V` immediately after
  the absorbing token instead of a `U`.  Nothing else about the tape matters.

Counting up, the rules proved so far — `rule_P2` for all `112` steps of the phase `P2`,
`rule_P1` for the `37` steps of the first row, and `rule_P3_flat` for the `4` steps of the
row marked above — already account for `153` of the `336` macro steps of the first million
steps, i.e. for `46 %` of them.  The two rows of §32 would add the `37` steps with an
absorbing token `U(2,even)` followed by a `U` and the `37 + 4` steps with an absorbing
token `U(1,even)` followed by a `V`, i.e. about two thirds of all macro steps; the
remaining classes are their combination (an absorbing token `U(2,even)` followed by a `V`,
`85` steps), the fractal recursion (`3` steps) and the `5` steps in which the carry reaches
the right end of the tape.

## 32. The next two rows, stated precisely

Both rows have been located and checked by simulation (`sim/probe2.py`; **not**
machine-checked).  They are local rules of exactly the same kind as those already proved,
so they are the natural next targets.

**The absorbing token is `U(2,b)`** — the most frequent missing row.  For all
`r, m, s, m' ≥ 0`:

```
0 0 0 · U(2,2) V(1) u · u^r · U(2,2m+4) · u^s · U(1,2m'+2) 0
          --(133 + 12r + 20m + 6s + 10m') steps-->
      U(2,1) U(4,1) · u^r · U(1,4) V(2m+1) · u^s · U(1,2m'+4) 0
```

so the token `U(2,b)` splits into `U(1,4) V(b−3)` and a carry of two travels on.  (Checked
for all `r, m, s, m' ≤ 3`.)  Note that `U(2,2)` — the case `b = 2`, excluded here — makes
the machine halt; the orbit avoids it, which is the content of the adjacency refinement of
§19.

**A `V` follows the absorbing token.**  For all `r, m, c, s, m' ≥ 0`:

```
0 0 0 · U(2,2) V(1) u · u^(r+1) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2) 0
          --(195 + 12r + 20m + 20c + 12s + 20m') steps-->
      U(2,1) U(4,1) · u^(r+1) · U(1,2m+6) · V(2c+1) · u^s · U(1,2m'+6) 0
```

so *both* tokens `U(1,·)` gain four `2`s and the `V` gives up four: the carry is not
absorbed at the first run of `2`s but is handed across the `V`.  (Checked for all
`r, m, c, s, m' ≤ 2`.)  The short `V`s are the dangerous ones — `V(1)` and `V(3)` in this
position make the machine halt — which is again exactly the adjacency refinement of §19.

The pieces these two rules need beyond what is already proved are the turn-arounds in which
the marker left by the rightward sweep is `1 0 0 3` instead of `1 0 3` (an absorbing token
with `a = 2`), and in which the run of `2`s is terminated by a `4` instead of a `0` (a `V`
in the way).  Both are again finite local computations with one run-length parameter, of
the same shape as `cross_back`.

**The three new pieces of the first of the two rows are now proved**
(`RequestProject/TurnU2.lean`):

* `turn_U2`: `1 0 0 3 · 2^(2M+1) · 0  →  1 1 3 · 2^(2M+2) · 0` in exactly `10M+15` steps,
  the head entering on the first `2` of the run and leaving on the first `2` of the new
  one.  This is the turn-around at an absorbing token `U(2,b)`: the extra `0` in the marker
  stops the return sweep one cell early, so the head does *not* leave the region as it does
  in `cross_back` but turns around and re-enters the run — which is why such a token
  ends up as `U(1,4) V(b−3)` and passes a carry of two on, instead of swallowing the whole
  carry.
* `retU2`: the leftward return across what `turn_U2` leaves behind,
  `1 1 3 2 → 2 2 4 3` in `4` steps.
* `turn_U2_second`: the reflection of the second pass at the same token,
  `0 2 2 4 3 → 1 1 0 0 3` in `9` steps — the analogue of `u21_turn`.

Getting these required generalising the ping-pong chain and the return sweep so that the
cell to the left of the marker may carry any symbol (`pingpong_chain0`, `onesBack_gen`);
that cell is never read, so the generalisation is free.  What is still missing for the
complete row is only the bookkeeping that chains these pieces with the sweeps, in the style
of `rule_P3_flat`.

## 33. Exploratory scripts added in Part VI

`sim/flat.py` (the flat `P3` rule for every block sequence over `{1,2}`, the data behind
`rule_P3_flat`), `sim/shapes.py` (the census of §31), `sim/probe2.py` (the two rows of §32)
and `sim/winck2.py` (a small window-rule checker used to validate candidate pieces).  As
everywhere in this file, nothing these print is machine-checked.

# Part VII — the three remaining shapes of absorbing token, and where the census stands

Part VI ended with a census of the `336` macro steps of the first million steps and with
two rows stated precisely but not proved.  This part proves those two rows and two more,
and records what simulation says about the rows that are still open.

## 34. Four new machine-checked rules

| theorem | file | statement |
|---|---|---|
| `rule_P3_U2b` | `RequestProject/CarryU2b.lean` | `0 0 0 · U(2,2) V(1) u · u^r · U(2,2m+4) · u^s · U(1,2m'+2) 0  →  U(2,1) U(4,1) · u^r · U(1,4) V(2m+1) · u^s · U(1,2m'+4) 0` in `133 + 12r + 20m + 6s + 10m'` steps |
| `rule_P3_V` | `RequestProject/CarryV.lean` | `0 0 0 · U(2,2) V(1) · u^(r+2) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2) 0  →  U(2,1) U(4,1) · u^(r+1) · U(1,2m+6) · V(2c+1) · u^s · U(1,2m'+6) 0` in `195 + 12r + 20m + 20c + 12s + 20m'` steps |
| `rule_P1_V` | `RequestProject/CarryP1V.lean` | `0 0 0 · U(2,1) U(4,1) · U(1,2m+2) · V(2c+5) · u^s · U(1,2m'+2) 0  →  U(2,2) u · U(2,2m+6) · V(2c+1) · u^s · U(1,2m'+6) 0` in `171 + 20m + 20c + 12s + 20m'` steps |
| `rule_P3_U21_U2b` | `RequestProject/CarryU21b.lean` | `0 0 0 · U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) 0  →  U(2,1) U(4,1) · U(1,4) · u^r · U(1,2) V(2m+3) 0` in `107 + 6r + 10m` steps |

All four are `Win` rules: each also certifies that the head never leaves the displayed
window and that the machine does not halt during the steps it covers (`…_no_halt`).

Three mechanisms appear here for the first time.

* **An absorbing token `U(2,b)` splits.**  The rightward sweep across the block `0 4 4 2`
  of such a token leaves the marker `1 0 0 3`, one `0` more than the marker `1 0 3` that a
  token `U(1,b)` leaves.  The extra `0` stops the return sweep one cell early, so the head
  turns around inside the run of `2`s instead of leaving it (`turn_U2`).  The result is
  that the token becomes `U(1,4) V(b−3)` and only *two* of the four `2`s of the carry stay
  behind; the other two travel on.  This is `rule_P3_U2b`.
* **A `V` does not stop the carry.**  A run of `2`s terminated by a `4` does not reflect
  the head: the ping-pong marker `0 3` walks straight through the `4 3` that begins a
  token `V` (`vcross_step`) and continues through the `V`'s own run of `2`s.  Both passes
  therefore run all the way to the token *after* the `V`, so the `V` gives up four `2`s and
  both neighbouring `U` tokens gain four.  This is `rule_P3_V` and `rule_P1_V`.  Short `V`s
  are the dangerous ones: `V(1)` and `V(3)` in this position make the machine halt, which
  is why these two rules are stated for `V(2c+5)`.
* **Both complications at once, and then the rule is short.**  In `rule_P3_U21_U2b` one of
  the crossed tokens has exponent `a = 2`, so the *second* pass is turned around by it
  (`u21_turn`) before it can reach the absorbing token again.  The absorbing token is
  therefore visited only once, the carry never gets past it, and the window of the rule
  stops one cell after it: whatever stands further right is irrelevant and untouched.  This
  is the first rule of the development whose window is bounded on the right by the
  absorbing token itself.

`rule_P3_V` is the one of the four whose shape does **not** occur in the census: the real
orbit never reaches a `P3` configuration with all crossed exponents `1`, an absorbing
`U(1,even)` and a `V` after it.  It is proved because it isolates the `V`-crossing
mechanism in its simplest form; `rule_P1_V`, which the orbit does use `37` times, is the
same computation with the `P1` prefix and is what covers the census row.

## 35. Where the census stands

Of the `336` macro steps of the first million steps, the rules proved so far cover

| rule | census row | steps |
|---|---|---|
| `rule_P2` | every `P2` step | 112 |
| `rule_P1` | `P1`, `r=0`, absorb `U(1,even)`, followed by `U` | 37 |
| `rule_P1_V` | `P1`, `r=0`, absorb `U(1,even)`, followed by `V` | 37 |
| `rule_P3_U2b` | `P3`, `r=0`, absorb `U(2,even)`, followed by `U` | 37 |
| `rule_P3_U21_U2b` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `U` | 12 |
| `rule_P3_flat` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `U` | 4 |

i.e. `239` of `336`, about `71 %`.  What is left is `97` steps in six rows: `36` steps of
the `P1` row with `r ≥ 1`, `37` of the `P3` row with `r = 0` and a `V` after an absorbing
`U(2,even)`, `12 + 4` of the two rows with a crossed exponent `2` and a `V`, the `3` steps
of the fractal recursion and the `5` steps in which the carry reaches the right end.

## 36. The three open rows, as simulation gives them

None of what follows is machine-checked; each line has been checked by direct simulation
over the stated range of parameters, and each is a local window rule of exactly the kind
the development already proves.

**The `P1` row with `r ≥ 1`** (`36` steps; `sim/p1fr.py`).  In the real orbit the tape at
such a step always reads `U(2,1) U(4,1) · u u · U(2,2) V(1) · u · …`: the *prefix of a `P3`
configuration occurs inside the tape*, which is the fractal of §20 in miniature.  For all
`r, m ≥ 0`:

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · U(1,2m+2) 0
       --(237 + 12r + 40m) steps-->
   U(2,2) u · U(2,1) · u^(r+2) · U(2,2m+10) 0
```

and, when at least one `u` separates the inner `U(2,2) V(1) u` from the next token with
`b ≥ 2`, for all `r, m, s ≥ 0`:

```
0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · u^(s+1) · U(1,2m+2) 0
       --(261 + 12r + 24s + 40m) steps-->
   U(2,2) u · U(2,1) · u^(r+2) · U(2,1) · u^s · U(1,2m+10) 0
```

(checked for `r, s ≤ 2`, `m ≤ 2`).  The head makes **four** passes here rather than two,
which is why the step counts are so much larger than in every rule proved so far.

**The `P3` row with a `V` after an absorbing `U(2,even)`** (`37` steps; `sim/u2bv2.py`).
In the orbit the absorbing token of this row is always `U(2,8)`, and then for all
`t, m' ≥ 0`:

```
0 0 0 · U(2,2) V(1) u · U(2,8) V(1) · u^(t+2) · U(1,2m'+2) 0
       --(403 + 30t + 50m') steps-->
   U(2,1) U(4,1) · u u · U(2,2) V(1) · u^t · U(1,2m'+12) 0
```

(checked for `t, m' ≤ 3`).  Here the head makes **five** passes, and the exponent `8` is
not incidental: with an absorbing `U(2,2m+4)` and a following `V(1)` the behaviour depends
on `m` in a genuinely irregular way — for `m = 0` the machine halts, for `m = 1, 2, 3, 4`
the outcome has four different shapes.  This row is where the self-similarity of the
space-time diagram enters the local rules, and a proof of it will need the fractal
identity of §20 rather than a fixed number of macro pieces.

**The two rows with a crossed exponent `2` and a `V`** (`12 + 4` steps; `sim/u21bv.py`).
The `12`-step row is `rule_P3_U21_U2b` with a `V(1)` after the absorbing token, and then
the carry is *not* stopped there: for all `r, m, t, m' ≥ 0`,

```
0 0 0 · U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) V(1) · u^(t+1) · U(1,2m'+2) 0
       --(167 + 6r + 10m + 12t + 20m') steps-->
   U(2,1) U(4,1) · U(1,4) · u^(r+1) · U(2m+6,1) · u^t · U(1,2m'+6) 0
```

(checked for `r, m ≤ 3`, `t, m' ≤ 2`).  Note the output token `U(2m+6,1)`: a long run of
`4`s is created, which by §24 is a "virtual blank tape" — again the fractal.

## 37. Exploratory scripts added in Part VII

`sim/u2b.py` (the stage decomposition behind `rule_P3_U2b`), `sim/vrow.py` (behind
`rule_P3_V`), `sim/u2bv.py` (the probe showing that an isolated `U(2,b)` immediately
followed by a `V` halts), `sim/p1v.py` and `sim/p1v2.py` (the rule and the stage
decomposition behind `rule_P1_V`), `sim/u21b.py` (behind `rule_P3_U21_U2b`), and
`sim/p1fr.py`, `sim/u2bv2.py`, `sim/u21bv.py` for the three open rows of §36.  As
everywhere in this file, nothing these print is machine-checked.

# Part VIII — the two rows with a crossed exponent `2` and a `V`, proved

Part VII proved four rules and left three rows of the census open.  This part proves the
two of them in which one of the crossed tokens has exponent `a = 2` and a token `V`
follows the token that absorbs the carry.

## 38. Two new machine-checked rules

| theorem | file | statement |
|---|---|---|
| `rule_P3_U21_U2b_V` | `RequestProject/CarryU21bV.lean` | `0 0 0 · U(2,2) V(1) u · U(2,1) · u^r · U(2,2m+4) V(1) · u^(t+1) · U(1,2m'+2) 0  →  U(2,1) U(4,1) · U(1,4) · u^(r+1) · U(2m+6,1) · u^t · U(1,2m'+6) 0` in `167 + 6r + 10m + 12t + 20m'` steps |
| `rule_P3_U21_V` | `RequestProject/CarryU21V.lean` | `0 0 0 · U(2,2) V(1) · u^(r+1) · U(2,1) · u^s · U(1,2m+2) · V(2c+5) · u^w · U(1,2m'+2) 0  →  U(2,1) U(4,1) · u^r · U(1,4) · u^s · U(1,2m+4) · V(2c+3) · u^w · U(1,2m'+4) 0` in `137 + 12r + 6s + 10m + 10c + 6w + 10m'` steps |

Both are `Win` rules: each also certifies that the head never leaves the displayed window
and that the machine does not halt during the steps it covers (`…_no_halt`).

The first was stated in §36 and is proved here as a chain of twenty-six window rules; the
second is new.  Together they complete the family "one crossed exponent `2`, a `V` after
the absorbing token", and between them they show the two ways such a step can end.

* In `rule_P3_U21_U2b_V` the absorbing token is a `U(2,b)`, so the marker the first pass
  leaves at it is `1 0 0 3` and the second pass is turned around *inside* it; the carry is
  handed across the `V(1)`, and the absorbing token and the `V` merge into a single long
  run of `4`s, the token `U(2m+6,1)`.  By §24 such a run is a "virtual blank tape", so this
  is one of the places where the space-time diagram creates a fresh copy of itself.
* In `rule_P3_U21_V` the absorbing token is a `U(1,b)`.  The crossed `U(2,1)` swallows two
  of the four `2`s of the carry and becomes `U(1,4)` (`u21_turn`), so only a carry of *two*
  travels on; the `V` does not stop it (`vcross_step`), and it is shared out as `+2` for
  the absorbing token, `−2` for the `V` and `+2` for the token after it.  The second pass
  is turned around by the crossed `U(2,1)`, so everything to the right of that token is
  visited only twice.  The proof is a chain of twenty-three window rules, every piece of
  which the earlier files already provide.

The stage decomposition of each was found by simulation first (`sim/u21bv2.py`,
`sim/u21v2.py`, which check that the stated sequence of pieces reproduces the head
position and state at every stage boundary) and only then written in Lean.

## 39. Where the census stands

Of the `336` macro steps of the first million steps, the proved rules now cover

| rule | census row | steps |
|---|---|---|
| `rule_P2` | every `P2` step | 112 |
| `rule_P1` | `P1`, `r=0`, absorb `U(1,even)`, followed by `U` | 37 |
| `rule_P1_V` | `P1`, `r=0`, absorb `U(1,even)`, followed by `V` | 37 |
| `rule_P3_U2b` | `P3`, `r=0`, absorb `U(2,even)`, followed by `U` | 37 |
| `rule_P3_U21_U2b` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `U` | 12 |
| `rule_P3_U21_U2b_V` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `V` | 12 |
| `rule_P3_flat` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `U` | 4 |
| `rule_P3_U21_V` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `V` | 4 |

i.e. `255` of `336`, about `76 %`.  What is left is `81` steps in four rows:

* `36` steps of the `P1` row with `r ≥ 1` (§36, first row; four passes),
* `37` steps of the `P3` row with `r = 0`, an absorbing `U(2,even)` and a `V` after it
  (§36, second row; five passes, and the one row whose shape depends on the exponent of
  the absorbing token in a genuinely irregular way),
* the `3` steps of the fractal recursion, and
* the `5` steps in which the carry reaches the right end of the tape.

The first two are stated precisely in §36 and are checked there by simulation over the
range of parameters that occurs; they are local window rules of exactly the kind the
development already proves, so the remaining obstruction to a complete non-halting proof
is not the *local* behaviour but the induction of §24 and §20 — the statement that the
tape word at each synchronisation moment stays inside the class these rules describe, for
which the fractal identity (a run of `3j+1` fours is a compressed copy of the tape at the
`j`-th synchronisation moment) is the right induction hypothesis.

## 40. Exploratory scripts added in Part VIII

`sim/u21bv2.py` (the stage decomposition behind `rule_P3_U21_U2b_V`), `sim/u21v.py` (the
probe that locates `rule_P3_U21_V`) and `sim/u21v2.py` (its stage decomposition and a
check of the rule over all parameters `≤ 2`).  As everywhere in this file, nothing these
print is machine-checked; they are the scaffolding from which the Lean proofs were
written.

# Part IX — from the blank tape into the token world

Every rule of the development is a *window* rule about a tape that already carries a word
of the token alphabet.  `RequestProject/Start.lean` connects them to the machine itself.

## 41. The first `2016` steps, computed

`blank_prefix` states that the first `2016` steps of the blank-tape run are a window
computation on `96` blank cells: the head starts in state `A` on cell `71`, never leaves
the window, and after exactly `2016` steps is in state `B` on cell `21`, the window
carrying

```
0^18 · U(2,2) u U(2,8) u^3 U(1,2) u^13 · 0 0 0 0
```

This is discharged by the list-level simulator `lrun` of `Local.lean` and `decide`, so it
is a kernel computation rather than a hand proof — the same device that proves the small
fixed pieces, run for two thousand steps instead of ten.

The cut is at `2016` for a reason.  Of the twenty-four census classes of §31, one — the
five macro steps in which the carry runs off the right end of the tape — has no
parametric rule, and simulation locates all five of them before step `1741`.  They are
therefore *inside* the computed prefix, and that census row is closed: from step `2016`
on, every macro step of the orbit belongs to one of the recurring rows.

## 42. Four macro steps of the real orbit

`orbit_prefix` continues from there by *applying the proved rules to the machine's own
tape*:

| step | rule | parameters | duration |
|---|---|---|---|
| `2016 → 2047` | `rule_P2` | — | `31` |
| `2047 → 2238` | `rule_P3_U2b` | `r=0, m=2, s=3, m'=0` | `191` |
| `2238 → 2485` | `rule_P1_V` | `m=1, c=0, s=3, m'=1` | `247` |
| `2485 → 2516` | `rule_P2` | — | `31` |

so that `orbit_prefix` is a single window rule covering the first `2516` steps.  Two
corollaries are stated: `run_2516`, which gives the exact configuration at step `2516`
(state `B`, head at `-62`, tape `U(2,2) V(1) u U(2,8) V(1) u^3 U(1,8) u^13`), and
`not_halted_le_2516`.

The chain stops there only because the next macro step of the orbit is the `P3` row with
an absorbing `U(2,8)` followed by a `V` — one of the two rows of §39 that are still open.
This is the first place in the development where the proved rules are applied to the
machine's own orbit rather than to an arbitrary tape of the right shape, and it is the
shape a complete proof will take: a finite computed prefix, followed by an induction in
which every step is one of the census rows.

# Part X — the `P1` fractal row, proved

Part VIII left four rows of the census open, the first of them the `P1` row with `r ≥ 1`
stated in §36.  This part closes that row.

## 43. The two rules

| theorem | file | statement |
|---|---|---|
| `rule_P1_fractal` | `RequestProject/FracP1.lean` | `0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · U(1,2m+2) 0  →  U(2,2) u · U(2,1) · u^(r+2) · U(2,2m+10) 0` in `237 + 12r + 40m` steps |
| `rule_P1_fractal_gen` | `RequestProject/FracP1s.lean` | `0 0 0 · U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · u^(s+1) · U(1,2m+2) 0  →  U(2,2) u · U(2,1) · u^(r+2) · U(2,1) · u^s · U(1,2m+10) 0` in `261 + 12r + 24s + 40m` steps |

Both are `Win` rules: each also certifies that the head never leaves the displayed window
and that the machine does not halt during the steps it covers (`…_no_halt`).  Together
they are the two ways the row can occur — the token that absorbs the carry either comes
immediately after the inner `u`, or after a further run of `s+1` tokens `u`.

What distinguishes this row from every other rule of the development is that the head
makes **four** passes over the region rather than two.  The reason is the inner
`U(2,2) V(1) u`: that is exactly the prefix of a `P3` configuration, sitting *inside* the
tape rather than at its left end, and it turns the carry around twice.  This is the
fractal of §20 in miniature, and it is why the step counts are so much larger than
elsewhere.

The second rule is proved as a chain of thirty-five window rules, split into
`p1fs_pass12` (the first two passes, `109 + 3r + 12s + 20m` steps), `p1fs_pass34` (the
third and fourth, `130 + 6r + 12s + 20m`) and `p1fs_return` (the return to the left end,
`22 + 3r`).  The extra run of `u`s is crossed eight times — four times rightwards and four
times leftwards — which is exactly the `24s` in the step count; the return pass does not
see it at all, which is why its cost is the same `22 + 3r` as in the rule without the
extra run.

Two small re-cuts of the computation were needed to make every piece an existing lemma.
Where the head comes back leftwards out of the run of `2`s and has the extra run of `u`s
in front of it, the natural reading — "turn the corner, then sweep" — puts the blocks out
of phase with `sweepL_bulk`; cutting the other way round, "sweep the `s+1` blocks
`1 0 3` first, then turn the corner with `fp1_two`", uses the lemmas the project already
has.  The same re-cut applies at the second such place, before `fp1_backL`.

## 44. Which steps of the orbit these two rules cover

`sim/p1cover.py` classifies every `B`-event of the first million steps whose tape word
begins `U(2,1) U(4,1) · u^(r+1) · U(2,2) V(1) · u · …`.  There are `36` of them, and

* `24` have the shape of `rule_P1_fractal`, always with `r = 1`, `m = 8`;
* `8` have the shape of `rule_P1_fractal_gen`, always with `r = 1`, `s = 7`, `m = 0`;
* `4` have neither shape: in one (at step `1324`) the carry runs off the right end of the
  tape, and that step is inside the computed prefix of §41; in the other three the token
  after the run of `u`s is not an absorbing `U(1,even)` but the long `4`-run `U(82,1)`,
  i.e. the fractal recursion of §20.

## 45. Where the census stands

Of the `336` macro steps of the first million steps, the proved rules now cover

| rule | census row | steps |
|---|---|---|
| `rule_P2` | every `P2` step | 112 |
| `rule_P1` | `P1`, `r=0`, absorb `U(1,even)`, followed by `U` | 37 |
| `rule_P1_V` | `P1`, `r=0`, absorb `U(1,even)`, followed by `V` | 37 |
| `rule_P3_U2b` | `P3`, `r=0`, absorb `U(2,even)`, followed by `U` | 37 |
| `rule_P3_U21_U2b` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `U` | 12 |
| `rule_P3_U21_U2b_V` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `V` | 12 |
| `rule_P3_flat` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `U` | 4 |
| `rule_P3_U21_V` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `V` | 4 |
| `rule_P1_fractal` | `P1`, `r≥1`, inner `U(2,2) V(1) u`, absorbing token next | 24 |
| `rule_P1_fractal_gen` | `P1`, `r≥1`, inner `U(2,2) V(1) u`, a run of `u`s in between | 8 |

i.e. `287` of `336`, about `85 %`.  What is left is `49` steps:

* `37` of the `P3` row with `r = 0`, an absorbing `U(2,even)` and a `V` after it (§36,
  second row; five passes, and the one row whose shape depends on the exponent of the
  absorbing token in a genuinely irregular way),
* the `3 + 3` steps of the fractal recursion — the carry meeting a long `4`-run instead of
  an absorbing token — and
* the `5 + 1` steps in which the carry reaches the right end of the tape, all of them
  before step `1741` and hence inside the computed prefix of §41.

So, apart from one further local row, the remaining obstruction is the recursion itself:
the statement that a run of `3j+1` fours behaves like the tape at the `j`-th
synchronisation moment (§20, §24), for which the rules proved here supply the induction
step at the left end.

## 46. Exploratory scripts added in Part X

`sim/p1fs.py` (the stage decomposition behind `p1fs_pass12`, `p1fs_pass34` and
`p1fs_return`: it replays the stage list against the real machine for all `r, s, m ≤ 2`,
checking the state and head position at every stage boundary, the total step count and the
final word, and prints the window of each stage) and `sim/p1cover.py` (the census check of
§44).  As everywhere in this file, nothing these print is machine-checked; they are the
scaffolding from which the Lean proofs were written.

# Part XI — the `P3` row with an absorbing `U(2,8)` and a `V`, proved

`RequestProject/U2bV.lean`.  This is the second of the two rows that §36 left open, and
the last of the "ordinary" census rows: everything that remains after it is the fractal
recursion itself.

## 47. The rule

For all `t, m ≥ 0`,

```
0 0 0 · U(2,2) V(1) u · U(2,8) V(1) · u^(t+3) · U(1,2m+2) 0
       --(433 + 30t + 50m) steps-->
   U(2,1) U(4,1) · u u · U(2,2) V(1) · u^(t+1) · U(1,2m+12) 0
```

is `rule_P3_U2b_V`, with `rule_P3_U2b_V_no_halt` the corollary that the machine does not
halt anywhere inside those `433 + 30t + 50m` steps.  It is §36's second row written with
`t` shifted by one, so that at least three tokens `u` follow the `V(1)`; that is exactly
the range in which the decomposition below is uniform, and — see §48 — it is the range
that occurs in the orbit.

The head makes **five** passes over the region.  Unlike every earlier rule, the fixed part
of the configuration is too long to be a handful of named pieces, so the proof is
organised the other way round:

* **Six fixed stretches** (`u2bv_fix0` … `u2bv_fix5`, of `65, 7, 41, 11, 17, 57` steps).
  In each of them the head stays inside the first twenty-nine cells, where the tape does
  not depend on `t` or `m` at all.  Each is therefore a single kernel computation —
  `Win.of_lrun (by decide)` on a twenty-nine cell window — and no hand reasoning is
  involved.  Their input and output words are the seven rows

  ```
  0000442243204204422222222432 0     (the configuration the rule starts from)
  0131011010310310111111110103 0/2
  0131011010310310111111111310 2/4
  0131011131031031000000000031 4/0
  0131011131031031000000013103 0/2
  0131011131031031000013100310 2/4
  0442044442042042044224320420 4     (the configuration it ends in)
  ```

* **Five excursions** (`u2bv_exc1` … `u2bv_exc5`, of `6t+10m+35`, `+41`, `+47`, `+53`,
  `+59` steps) into the run of `u`s and the token beyond it.  Each of these is a chain of
  pieces the development already proves — `sweepR_042/204/420`, `cross_back`,
  `pingpong_chain0`, `rule_endgame`, `onesBack_gen`, `sweepL_bulk`, `carry_B2` — and each
  is stated on a window that begins one cell to the left of the run of `u`s, so it never
  mentions the fixed part at all.

Chaining the eleven pieces (with the fixed stretches embedded in the parametric tail and
the excursions embedded behind a twenty-seven cell left context) gives the rule.  The step
count `433 + 30t + 50m` is `198` fixed steps plus `30t + 50m + 235` of excursion.

## 48. Which steps of the orbit the rule covers

`sim/u2bvcover.py` classifies every `B`-event of the first million steps whose token word
begins `U(2,2) V(1) u · U(2,b) V(1) · …`.  There are `37` of them, matching the census of
§35, and:

* `24` are exactly `rule_P3_U2b_V`, and — remarkably — *all* of them have the same
  parameters, `t = 0` and `m = 3`: the row occurs in the orbit in one single shape;
* the other `13` are the ones in which the carry is not stopped by a token `U(1,even)` at
  all but meets a further `U(2,8) V(1)` beyond the run of `u`s, or runs off the right end
  of the tape.  These are the fractal recursion, not a new local row.

Because the parameters are always `t = 0, m = 3`, the rule applies directly to the real
orbit: `orbit_prefix_3099` in `RequestProject/Start.lean` continues the blank-tape
computation of §41–42 with exactly this instance, and `not_halted_le_3099` records that
the machine does not halt in its first `3099` steps.

## 49. Where the census stands

Of the `336` macro steps of the first million steps, the proved rules now cover

| rule | census row | steps |
|---|---|---|
| `rule_P2` | every `P2` step | 112 |
| `rule_P1` | `P1`, `r=0`, absorb `U(1,even)`, followed by `U` | 37 |
| `rule_P1_V` | `P1`, `r=0`, absorb `U(1,even)`, followed by `V` | 37 |
| `rule_P3_U2b` | `P3`, `r=0`, absorb `U(2,even)`, followed by `U` | 37 |
| `rule_P3_U21_U2b` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `U` | 12 |
| `rule_P3_U21_U2b_V` | `P3`, one crossed exponent `2`, absorb `U(2,even)`, followed by `V` | 12 |
| `rule_P3_flat` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `U` | 4 |
| `rule_P3_U21_V` | `P3`, one crossed exponent `2`, absorb `U(1,even)`, followed by `V` | 4 |
| `rule_P1_fractal` | `P1`, `r≥1`, inner `U(2,2) V(1) u`, absorbing token next | 24 |
| `rule_P1_fractal_gen` | `P1`, `r≥1`, inner `U(2,2) V(1) u`, a run of `u`s in between | 8 |
| `rule_P3_U2b_V` | `P3`, `r=0`, absorb `U(2,8)`, followed by `V` | 24 |

i.e. `311` of `336`, about `93 %`.  What is left is `25` steps, and **every one of them is
an instance of the fractal recursion or of the carry reaching the right end of the tape**:

* `13 + 3 + 3` steps in which the carry, instead of being absorbed by a token
  `U(1,even)`, meets a long `4`-run or a further `U(2,8) V(1)` — the statement that such a
  run behaves like the tape at an earlier synchronisation moment (§20, §24);
* `5 + 1` steps in which the carry reaches the right end of the tape, all of them before
  step `1741` and hence inside the computed prefix of §41.

So the local classification is now complete: no row of the census needs a new *finite*
window rule.  The single remaining obstruction is the recursion itself.

## 50. Exploratory scripts added in Part XI

`sim/u2bv5.py` (dumps the six fixed stretches of the row — the twenty-nine cell words
before and after each — from which the `Win.of_lrun` statements were written) and
`sim/u2bvcover.py` (the census check of §48).  They join `sim/u2bv3.py` and `sim/u2bv4.py`
(the stage decomposition itself, replayed against the real machine for `1 ≤ t ≤ 4`,
`0 ≤ m ≤ 4`).  As everywhere in this file, nothing these print is machine-checked; they
are the scaffolding from which the Lean proofs were written.

# Part XII — the remaining gap, made formal, and the last missing local row

Part XI closed the last "ordinary" row of the census, leaving two things: the fractal
recursion, and the one row in which the carry runs off the right end of the tape.  This
part deals with the second of them outright, and turns the first into a precisely stated
*combinatorial* condition — a statement about words, with no Turing machine left in it.

## 51. Non-halting reduced to a closed family of tape words

`RequestProject/Reduce.lean`.  Every left-end rule of the development has one and the same
shape,

```
Win St.B St.B 3 0 ([0,0,0] ++ W) W' k ,        |W'| = |W| + 3 ,
```

i.e. *the head starts in state `B` on the leftmost non-blank cell with three blank cells
to its left, and `k` steps later it is again in state `B`, three cells further left, on
what is now the leftmost non-blank cell, the tape word having become `W'`*.  The rules
conserve cells: the three extra cells of `W'` are exactly the three blank cells the rule
consumes on the left, so the **right edge of the word never moves**.

Two definitions make this into a reduction.

* `AtWord n a W` — after `n` steps from the blank tape the machine is in state `B` with
  its head on cell `a`, the tape carries `W` on the cells `a, …, a+|W|−1`, and every other
  cell is blank.  This is a *synchronisation moment* in the sense used throughout this
  file.
* `MacroClosed P` — every word `W` of the family `P` admits a macro rule of the above
  shape, in a positive number of steps, whose result `W'` is again in `P`.

`AtWord.macro` shows that a macro rule carries one synchronisation moment to the next, and
hence

> **`never_halts_of_closed`.**  If `MacroClosed P` and the machine ever reaches a
> synchronisation moment whose tape word lies in `P`, then it never halts.

The machine does reach one: `orbit_atWord` restates `orbit_prefix_3099` of §48 in that
form — after exactly `3099` steps the machine is in state `B` on cell `−65`, the tape
carries

```
orbitWord  =  U(2,1) U(4,1) u u U(2,2) V(1) u U(1,18) u^12
```

beginning at that cell, and every other cell is blank.  So `never_halts_of_closed_orbit`
says: **a family of tape words containing `orbitWord` and closed under one macro step
proves the machine never halts.**  Nothing about the machine is needed beyond that; the
family may be infinite, and its members may use different rules.  That is the precise
sense in which what is left is combinatorial.

`Win.macro_append` is the small adapter that turns a catalogue entry — stated for the
shortest window it needs — into a step of such a family by appending an arbitrary,
untouched right context; `macro_step_P2` is the `P2` rule in that form, as a worked
example.

## 52. The fractal mechanism for a whole family at once

§24 explained the self-similarity: a rightward sweep turns a token `U(a,1) = 0 4^a 2` into
`1 0^a 3`, so a `4`-run becomes a piece of *virtual blank tape*, and every left-end rule —
being a window rule whose window starts with `0 0 0` — applies verbatim inside it,
consuming three of its cells.  `Fractal.lean` proved the two halves of that statement and
three instances.

`MacroClosed.in_zero_run` now states it for a whole closed family and for every depth
simultaneously, by induction on `j`:

> if `MacroClosed P` and `P W`, then for every `j` there are `W' ∈ P` with
> `|W'| = |W| + 3j` and a step count `n` such that
> `Win St.B St.B (3j+3) 3 (0^(3j) · 0 0 0 · W) (0 0 0 · W') n`.

In words: **a run of `3j` extra blank cells hosts exactly `j` macro steps of the family's
own computation**, and the window conclusion certifies that the head never leaves the run
while it does so.  This is the inductive engine behind "a `4`-run of length `3j+1`
reproduces the machine's own first `j` tape words"; what it does *not* supply — and what a
complete proof still needs — is the boundary bookkeeping at the two ends of the run, i.e.
the statement that what the sub-computation finds to the right of the run is again a word
of the family.

## 53. The carry running off the blank right end, proved

`RequestProject/BlankRight.lean`.  This is the one row of the carry table of §25 that had
no parametric rule: the carry meets no absorbing token at all and runs into the blank
tape.  Probing it in isolation (`sim/blank.py`) gives two clean families, and both are now
proved:

| theorem | statement | steps |
|---|---|---|
| `rule_P3_blank` | `0 0 0 · U(2,2) V(1) · u^(N+1) · 0 0 0  →  U(2,1) U(4,1) · u^(N+2) · 0` | `59 + 12N` |
| `rule_P1_blank` | `0 0 0 · U(2,1) U(4,1) · u^N · 0 0 0  →  U(2,2) u · U(2,1) · u^(N+1) · 0` | `47 + 12N` |

Both are `Win` rules, so each also certifies that the head never leaves the displayed
window — in particular that it never reads more than **three** blank cells on the right —
and that the machine does not halt during the steps it covers.

The anatomy is the two-pass anatomy of §29 with the run of `2`s replaced by the blank.  In
nine stages: the opening; the rightward crossing of the run of `u`s; a three-step bounce
off the blank (`blank_turn`: `A` on the first blank cell writes `1`, steps right, comes
back and overwrites it with `2`, so two blank cells become the tail of a fresh token); the
leftward sweep back; a turn of the corner (for `P1`, the reflection `p1b_reflect` inside
the swept `4`-run of `U(4,1)`); the second rightward crossing; a second bounce; the second
leftward sweep; the closing.  Each bounce delivers one new token `u`, and each of the four
crossings of the run costs `3` steps per token, which is the `12N`.

This row matters twice over.  It is what the machine does at the very beginning, while the
tape is still short — the five macro steps of §31 that the computed prefix of §41 had to
absorb.  And, because a swept `4`-run is virtual blank tape (§24, §52), it is also what
the machine does *inside* every fractal copy of its own computation: a copy starts from
the blank tape, so its first macro steps are exactly these two rules.  Without them no
closed family in the sense of §51 can contain the words that occur inside a `4`-run.

## 54. Where the gap stands now

Every *local* row of the carry table is now proved for arbitrary parameters: the carry
crossing runs of `u`, being absorbed by `U(1,even)` or `U(2,even)` with or without a
following `V`, crossing `U(2,1)`, the `P1` row with an inner `U(2,2) V(1) u`, and — as of
§53 — running off the blank end.  What remains is not a missing rule but the recursion:

1. produce a family `P` of tape words containing `orbitWord` and closed under one macro
   step (§51).  By §52 the sub-computation inside a `4`-run is again a computation of the
   same kind, so `P` has to be *self-referential*: the exponent of a long `4`-run in a word
   of `P` records how many macro steps of `P`'s own computation are hidden inside it;
2. equivalently, carry out the strong induction on `j` of §27, whose step is exactly
   `MacroClosed.in_zero_run` plus the boundary bookkeeping at the two ends of the run.

That is the whole of the remaining obstruction, and it is now stated in the project in
Lean rather than only in prose.

## 55. Two more instances of the unfolding

`RequestProject/Unfold.lean`.  `unfold_U4` (`j = 1`) and `unfold_U10` (`j = 3`) of §26 are
joined by the next two instances that are still window rules, found with `sim/unfold.py`:

| theorem | `4`-run | inner macro steps | it unfolds into | steps |
|---|---|---|---|---|
| `unfold_U13` | `U(13,1)` | `4` | `u U(1,2) u` | `561` |
| `unfold_U16` | `U(16,1)` | `5` | `u U(1,2) V(1) u` | `595` |

In both, the window is `0 0 0 · U(2,2) V(1) u · U(a,1) · u u U(1,2) · 0`, the tail being
the shortest one that absorbs the carry the unfolding produces.  For `a = 13` the run of
`13 = 3·4 + 1` blank cells left by the sweep hosts four inner synchronisation moments,
whose tape words are `U(2,1)`, `U(2,2)`, `U(2,2) V(1)`, `U(2,1) U(4,1)` — the machine's own
first four tape words, as §24 predicts; for `a = 16` there are five, the extra one being
the `P2` step that inserts the `V(1)`.  Each theorem is a single kernel computation and,
being a `Win` rule, also certifies that the head stays inside the window and that the
machine does not halt during those steps.

`sim/unfold.py`, which searches for the tail that makes each instance a window rule, is
exploratory: nothing it prints is machine-checked.

## 56. The machine is one cell away from halting

`RequestProject/NarrowGap.lean`.  Every window rule of this development begins its window
with three blank cells, `0 0 0`.  That hypothesis is load-bearing:

> **`halt_of_narrow_gap`.**  If the tape reads `0 0 1 0 0` and the head is in state `B` on
> the last of those five cells, the machine halts `13` steps later.

The `1` is the cell a rightward sweep leaves at the left end of a swept `4`-run, and the
head sits on the leftmost cell of the tape word to its right — in the token alphabet
always a `0`.  So the configuration is precisely a left-end step attempted with **one**
spare blank cell instead of three, and it is fatal.

Two things follow.  No rule of the catalogue can be weakened to two blank cells on the
left.  And the non-halting of this machine is not a soft phenomenon: a proof has to control
the arithmetic of the run lengths — the `3j+1` of §20 — because a run of the wrong length
really does drive the head into the halting transition.  Simulation illustrates this:
probing an isolated `U(a,1)` after the `P3` prefix with a padding of `u`s (`sim/self2.py`),
the machine halts for `a = 6` and `a = 15`, whereas every length `3j+1` that actually
occurs in the orbit runs on.  The probe is exploratory; the theorem is machine-checked.
