# Analysis of the 2-state, 5-symbol Turing machine

```
1RB---3RA2LA2RB_2LB3LA4LB4RA0RA
```

| | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| **A** | `1RB` | `---` | `3RA` | `2LA` | `2RB` |
| **B** | `2LB` | `3LA` | `4LB` | `4RA` | `0RA` |

Started on the all-blank tape in state `A`.  The only undefined transition is
`A` reading `1`, so the machine halts exactly when it reads a `1` in state `A`.

**Status of the halting problem for this machine: still open.**  This document
records what the present investigation established.  Everything in
[`RequestProject/Machine.lean`](RequestProject/Machine.lean) is machine-checked;
everything in the "Empirical structure" sections below comes from an external
simulation and is *not* formally verified — it is offered as a description of
the mechanism and as a conjectural reduction of the halting problem to an
arithmetic statement.

---

## 1. What is proved in Lean

`RequestProject/Machine.lean` contains a complete formalisation (state set, tape
zipper, `step`, `run`, `Halts`) and the following theorems.

* `halts_iff_state_A_reads_one` — the machine halts iff at some time it is in
  state `A` scanning the symbol `1`.
* `no_halt_in_B` — no halt is possible in state `B`.
* `pre_halt_shape` — a complete case analysis of the step immediately preceding
  a halt: the head must *move onto* a cell that already contains `1`, and there
  are exactly five local pictures in which that can happen.
* `halt_trap` — **the trap.**  From any configuration of the shape
  ```
      … 1 [A:0] 2 …
  ```
  (head in state `A` on a `0`, a `1` to its left and a `2` to its right) the
  machine halts after exactly four further steps, whatever the rest of the tape
  is:  `A0 → 1RB`, `B2 → 4LB`, `B1 → 3LA`, and then `A` reads the `1`.
* `no_halt_escape` — **the escape.**  From
  ```
      … 1 [A:4] 2 …
  ```
  the machine does *not* halt: after exactly four steps the `1` has been
  overwritten by `3` and the head has moved past it to the left.
* Sweep rules, each proved by induction on the length of the block crossed:
  `A_over_twos` (`A` running right across `2`s rewrites them as `3`s),
  `B_over_twos` (`B` running left across `2`s rewrites them as `4`s),
  `A_over_two_fours` (two steps turn `4 4` into `2 0`), and
  `frontier_overflow` (`B` walking left across the block of saturated digits
  `0…0` rewrites them as `2`s, converts the leftmost `1` into a `3` and hands
  over to `A` one cell further left — this is exactly how the used part of the
  tape grows by one cell).
* `not_halted_before_hundred_million` — the machine does not halt during its
  first `10^8` steps (verified inside Lean by compiled evaluation of the
  formalised simulator).

The trap/escape pair is the heart of the matter: the whole fate of the machine
is decided by *which symbol sits between the `1` and the approaching head* at
the rare moments when the head approaches a `1` from the right in state `A`.

An unverified external C simulation was also run for `4·10^11` steps without
halting; that number is **not** backed by a Lean artifact and should be treated
as informal evidence only.

---

## 2. Empirical structure of the computation

All statements in this section were obtained by instrumented simulation.  They
are stated as observations/conjectures.

### 2.1 Gross behaviour

After `3·10^10` steps the used part of the tape is only about 105 cells wide
(roughly `-34 … 71`), and the machine has spent that time shuttling inside this
narrow window.  Time grows exponentially in the width, which is the signature of
a counter.

Useful vocabulary:

* State `B` **only ever moves left**, except for the two transitions
  `B3 → 4RA` and `B4 → 0RA` which immediately hand control back to `A`.
* A **left run** is a maximal stretch of `B`-moves: `B` walks left over `0`s
  (writing `2`) and `2`s (writing `4`), and stops at the first `3` (writing `4`)
  or `4` (writing `0`), turning right in state `A`.
* A **right run** is a stretch in state `A`: `A` walks right over `4`s
  (`A4 → 2RB`, `B4 → 0RA`, so a run of `4`s is rewritten `2 0 2 0 …` and the
  state alternates) and over `2`s (`A2 → 3RA`, the `2` becomes `3`), and it
  reverses at the first `2` that it meets in state `B`.

### 2.2 The leftmost `1` and the base-3 counter

Whenever `A` meets the blank at the left end it writes a `1` there (`A0 → 1RB`)
and moves right.  This `1` stays put for a very long time; call its position `m`
(the *frontier*).  The cells `m+1, m+2, m+3, …` then behave exactly like the
digits of a **base-3 counter**, with the digit encoding

| tape symbol | `3` | `4` | `0` | (`2`) |
|---|---|---|---|---|
| digit | 0 | 1 | 2 | unused / just reset |

The head repeatedly comes in from the right and increments the counter:

* `B3 → 4RA` : digit `0 → 1`, no carry, head turns right;
* `B4 → 0RA` : digit `1 → 2`, no carry, head turns right;
* `B0 → 2LB` : digit `2 → 0`, **carry**, the digit is left as a `2` and the head
  continues left to the next digit;
* after a carry chain the head turns right again and `A2 → 3RA` rewrites every
  reset `2` as a `3` (digit `0`) on the way out.

When the carry runs off the most significant end it reaches the `1` itself:
`B1 → 3LA` turns the `1` into a `3` and pushes the head one cell further left
onto a fresh blank, where a new `1` is written.  This is exactly how the tape
grows to the left, one cell per complete overflow of the counter.

A sample of the frontier during one epoch (the tape shown is `m … m+8`):

```
1 4 3 2 2 2 2 2 2      ← after the overflow, all lower digits reset
1 4 3 3 2 2 2 2 2
1 4 3 4 2 2 2 2 2
1 4 4 3 3 3 2 2 2      ← a carry has moved one digit to the left
…
1 0 0 0 0 0 0 2 2      ← all digits saturated: the next carry reaches the 1
```

Consequently the most significant digit `m+1` runs through the values
`3 → 4 → 0` and *never* equals `3` again except for the single step immediately
after the frontier moves (when the head is sitting on it in state `B`).  This is
why the trap pattern `1 [A:3]` is never reached directly.

### 2.3 Cascades: the dangerous events

`A` moves left only when it reads a `3` (`A3 → 2LA`) or when `B` reads a `1`
(`B1 → 3LA`).  These events are extremely rare (a few hundred in `2·10^9`
steps), and they occur in **cascades**: a self-sustaining leftward signal

```
 … 3 3 0 [A]        A eats the 3s (writing 2s), reaches a 0,
 … 3 3 1 …          writes 1 and steps right in B,
 … 3 3 1 4 …        B comes back, B1 turns the 1 into a 3,
 … 3 [A] 3 4 …      and A continues left over the next 3.
```

Each stage of a cascade moves 2–3 cells left in 6 steps.  A cascade is launched
at the right end of the tape (after a long rightward sweep has converted a run
of `4`s into the alternating pattern `2 0 2 0 …`), and it dies at the first cell
to its left containing a `2` or a `4`.  In the simulation this rule is exact:
for every long cascade recorded, its stopping position coincided with the
position of the rightmost `4` to the left of its starting point.

Two cascades occur per frontier epoch: a short one (length 4, at the right
frontier) and a long one.  Measured travel distances of the long cascades
against the tape width:

| step | travel | tape width |
|---|---|---|
| 466 | 15 | 22 |
| 1 104 | 14 | 27 |
| 3 060 | 26 | 32 |
| 8 696 | 18 | 37 |
| 29 438 | 35 | 43 |
| 110 574 | 22 | 53 |
| 428 142 | 37 | 58 |
| 1 423 770 | 26 | 64 |
| 5 379 974 | 48 | 69 |
| 18 358 922 | 30 | 74 |
| 70 171 356 | 51 | 79 |
| 243 668 882 | 34 | 85 |
| 937 249 592 | 75 | 90 |
| 5 581 010 832 | 38 | 100 |
| 24 154 375 906 | 70 | 106 |
| 92 718 056 154 | 42 | 111 |

The cascade of step 937 249 592 came within 14 cells of the frontier (and the
one of step 24 154 375 906 within 35).

### 2.4 Conjectural halting criterion

> **Superseded.**  The criterion stated in this subsection is *not* correct as
> written; see §4.2, where the exact criterion is derived and machine-checked
> in [`RequestProject/Counter.lean`](RequestProject/Counter.lean).  In
> particular the condition "leading digit `2`" is spurious (a cascade that
> reaches the frontier halts whatever the last digit is), and a second
> condition was missing (no *two consecutive* digits `2`).

Putting the pieces together:

> **Conjecture.**  The machine halts if and only if some cascade reaches the
> cell `m+1` immediately to the right of the frontier `1` while that cell
> contains a `0`.

Indeed, by the Lean lemmas `halt_trap` / `no_halt_escape`, when a cascade
arrives at `m+1` (which it does in state `A`, with a `2` in the cell it has just
vacated on its right):

* if `m+1` holds `4` (digit 1) the cascade dies harmlessly and the `1` is simply
  consumed;
* if `m+1` holds `0` (digit 2) the machine halts four steps later.

Since a cascade stops at the first `2` or `4` it meets, and the cells to the
right of the frontier are the base-3 digits described above, the halting
condition takes the following arithmetic shape.  Let `N` be the value of the
frontier counter (most significant digit at `m+1`) at the moment a cascade is
launched.  The cascade reaches the frontier iff

* no digit of `N` equals `1`, i.e. the base-3 expansion of `N` uses only the
  digits `0` and `2` (a "Cantor-set" value), and
* the leading digit of `N` equals `2`, i.e. `m+1` holds a `0`.

So the halting problem for this machine reduces (conjecturally) to:

> does the sequence of counter values sampled at cascade launches ever hit a
> number all of whose base-3 digits are `0` or `2`, with leading digit `2`?

This is the analogue, in base 3, of the "does a recursive sequence hit a number
of a special 2-adic form" phenomenon.  None of the measured cascades came close
to satisfying it (the deepest one left 14 cells to go), and the
sequence of cascade launch values looks pseudo-random, so the naive heuristic
does not settle the question in either direction: whether the expected number of
successes converges or diverges depends on the (not yet determined) law of the
sampled values.

---

## 3. What would be needed to close the problem

1. A proof that the frontier cells really implement the base-3 counter described
   in §2.2 for *all* times (this looks provable by induction, but the induction
   hypothesis has to control the entire right-hand region, which is where the
   difficulty lies).
2. An exact description of the sequence of counter values at which cascades are
   launched — this is the "recursive sequence" of the reduction.
3. Either a proof that this sequence avoids the base-3 digit-`{0,2}` numbers
   with leading digit `2` for ever (non-halting), or an explicit hit (halting).

Steps 2 and 3 are the open part.

---

## 4. The counter dynamics, made precise

This part supersedes §2.2–§2.4.  Everything called a *theorem* here is
machine-checked in [`RequestProject/Counter.lean`](RequestProject/Counter.lean);
everything called an *observation* comes from instrumented simulation and is
**not** formally verified.

### 4.1 The particle calculus

Reading the transition table as rules for a moving head gives four particles.

* **`A→`** (state `A` moving right) eats `2`s (writing `3`), and at a `4` it
  writes `2` and hands over to a right-moving `B`.
* **`B→`** reads a single cell: `3 ↦ 4` and `4 ↦ 0` continue right in `A`;
  `0 ↦ 2` and `2 ↦ 4` turn the head into a left-moving `B`; `1 ↦ 3` turns it
  into a left-moving `A`.
* **`←B`** eats `0`s (writing `2`) and `2`s (writing `4`); it stops at a `3`
  (writing `4`, turning right in `A`), at a `4` (writing `0`, turning right in
  `A`) and at a `1` (writing `3`, becoming `←A`).
* **`←A`** — the *cascade* — is the only dangerous particle, because `A` is the
  state that can read a `1`.  It has **two internal modes**, determined by the
  symbol immediately to its right:

  | mode | cell `3` | cell `0` | cell `2` | cell `4` | cell `1` |
  |---|---|---|---|---|---|
  | **P** (a `2` on its right) | continue in P (1 step) | continue in Q (3 steps) | stop | stop | **halt** |
  | **Q** (a `3` on its right) | continue in P (1 step) | stop | continue in P (3 steps) | stop | **halt** |

  All ten entries are proved (`cascade_P_three`, `cascade_P_zero`,
  `cascade_Q_three`, `cascade_Q_two`, `cascade_P_two_stops`,
  `cascade_P_four_stops`, `cascade_Q_zero_stops`, `cascade_Q_four_stops`,
  `cascade_halts_on_one`).  A cascade is born when `A` steps onto the blank at
  the right end of the used tape: `0 0 ↦ 3 2` and a mode-`Q` cascade leaves to
  the left (`cascade_birth`).

The old lemmas `halt_trap` and `no_halt_escape` are the two special cases
"mode P meets `0` next to the frontier" and "mode P meets `4`".

### 4.2 The exact halting criterion (the Cantor condition)

Because *both* modes halt on a `1`, the machine halts **iff a cascade ever
reaches the frontier**, with no extra condition on the last digit.  Which
blocks a cascade can cross is decided by the inductive relation `Cross` of
`Counter.lean`, whose crossable words form a regular language.  Encoding
counter cells as base-3 digits (`3 ↦ 0`, `4 ↦ 1`, `0 ↦ 2`):

> **Theorem (`cross_digits_iff`).**  A block of counter digits followed by the
> frontier `1` is crossed by a mode-`P` cascade **iff** no digit equals `1`
> and no two consecutive digits equal `2`.

So the halting condition really is a Cantor-type condition — the base-3
expansion of the counter segment must avoid the digit `1`, which is exactly
membership of the middle-thirds Cantor set (`cantor_value`) — *plus* a
no-two-consecutive-`2`s condition that the earlier write-up missed.  The
density of such blocks is therefore not `(2/3)^n` but `φ^n/3^n ≈ 0.54^n`
(Fibonacci-many admissible digit strings of length `n`).

Consequences proved in Lean:

* `cascade_halt_over_cantor_block`, `halts_of_reachable_cantor_block` — if such
  a configuration is ever reached, the machine halts;
* `no_halt_of_cascade_into_four` — the exact converse for the commonest
  blocker: while a cascade crosses a Cantor block and runs into a digit `1`
  (cell `4`), the machine provably does not halt;
* `cross_bg` — the alternating background `… 0 2 0 2 …` that fills most of the
  tape is *always* crossed (three steps per cell), which is why cascades travel
  so far; `halt_of_bg_then_cantor` combines the two;
* `halt_of_cantor_to_right_end` — the end-to-end statement, from the birth of a
  cascade at the right end of the tape to the halt at the frontier.

A cascade therefore dies exactly at the first cell that is a `4`, or at the
first `0` met in mode `Q`.  Checked against simulation: for **every** long
cascade in the first `3·10^7` steps, the mode-`P`/`Q` automaton predicts the
stopping cell exactly.

### 4.3 The base-3 counter, proved as a macroscopic rule

With the digit encoding above, the cells to the right of the frontier are a
base-3 counter whose **least significant digit is the right-hand end** of the
counter block; the head increments it whenever it arrives there in state `B`:

* **`counter_increment`** — from `⟨B⟩` on the least significant digit of a
  non-saturated word `d :: ds`, the machine takes exactly `incrCost (d :: ds)`
  steps (`1` for no carry, `2k+1` for a carry of length `k`) and leaves the
  counter holding `incr (d :: ds)`, with the head back out on the right in
  state `A`; `counterValue_incr` proves `value (incr w) = value w + 1`.
  (The carry leaves *pending* `2`s behind, which the outgoing `A2 → 3RA` sweep
  turns into digits `0`; both halves are part of the theorem.)
* **`counter_overflow`** — a saturated counter of `k+1` digits (value
  `3^(k+1) - 1`) sends the carry into the frontier: the frontier is consumed,
  a new frontier `1` appears one cell further left, the old frontier cell
  becomes the new most significant digit `1`, and all lower digits are reset,
  i.e. the value becomes exactly `3^(k+1)` (`counterValue_saturated`,
  `counterValue_after_overflow`).  This is how the used tape grows leftwards:
  one cell per power of three.

*Observation.*  In every epoch after the twelfth, the head touches the cell
next to the frontier exactly **twice**, both times in state `B`: once for the
increment `4 ↦ 0` of the most significant digit and once for the overflow
carry — precisely the two theorems above.  The verified increment cost is also
visible directly in the data: the time the head spends left of a fixed line
near the frontier takes the values `1, 3, 5, 7, 13, 15, 17, …`, i.e. `2k+1`.

### 4.4 What the rest of the tape is doing: two counters back to back

The visit profile of one epoch (number of head visits per cell, epoch 20,
`3·10^5` steps) is

```
cell (relative to the frontier):  0  1  2  3   4   5   6  …  21  …  50 52 54 56 58
visits:                           1  3  8 24  72 216 648  … 35496 …  10  8  8  8  1
```

* going **right from the frontier** the counts multiply by `3` — the signature
  of a ternary counter whose least significant digit sits near the peak (at
  cell 21 in this epoch);
* going **left from the right end** the counts halve every **two** cells — the
  signature of a binary counter with two cells per digit.

Both readings can be confirmed directly.  Decoding the right-hand region in
two-cell blocks with `2 4 ↦ 0`, `4 4 ↦ 1` (least significant block next to the
peak), the values read off at successive entries of the head into that region
are

```
17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, …
```

i.e. **the right-hand half of the tape is an exact binary counter in two-cell
blocks, incremented by exactly one on each visit**, its least significant digit
in the middle of the tape and its most significant digit at the right end.

On the other side, each visit of the head to the left region advances one
ternary digit: in the middle region the digits sit every third cell (separated
by the two background cells `0 2`), the least significant one cycles
`3 → 4 → 0` and then carries, and the carry flips the next digit — exactly the
`counter_increment` rule of §4.3, whose `2k+1` step cost is also directly
visible in the data.  Near the frontier the digits are packed one per cell
(hence the `×3` growth per cell there), further out one per three cells (`×3`
every three cells); the boundary between the two packings is the transition
zone that each cascade rewrites.

So the machine runs *two* counters back to back — a base-3 counter growing
leftwards from the middle and a base-2 counter growing rightwards from the
middle — and the head shuttles between their least significant ends, adding
one to each counter per round trip.  The cascades are launched at the far
right, when the binary counter runs into fresh tape, and travel left through
the alternating background until they meet a digit `1` of the ternary counter
or a mis-phased `0`.

### 4.5 Jumping between events

With this picture the natural acceleration is to stop simulating individual
steps and jump from event to event, an *event* being one round trip of the
head between the two least significant digits.  Each event costs
`2k+1` steps on the ternary side (`counter_increment`, proved) plus a similar
function of the carry length on the binary side, and both counters simply
advance by one.  Since the total carry length over a range of counter values
has a closed form (`N + N/3 + N/9 + …` for base 3, `N + N/2 + N/4 + …` for
base 2), the cost of *all* the events between two structural changes could be
summed in closed form, which would jump over `3^n`, resp. `2^b`, individual
events at once.

What is still missing before such jumps can be trusted is an exact rule for
the two remaining ingredients:

1. the **interface**: how the two counters hand over to each other, including
   the change of digit packing (one cell per digit near the frontier, three
   cells per digit in the middle) in the transition zone;
2. the **structural events**: the extension of the binary counter into fresh
   tape (which launches a cascade), the cascade itself (which rewrites the
   transition zone and, by §4.2, is the only thing that can ever halt the
   machine), and the overflow of the ternary counter into the frontier
   (`counter_overflow`, proved).

Until those are pinned down — by hand, or by a parametric rule-induction
engine that discovers them automatically — the jumps cannot be certified and a
step-by-step simulation remains the only sound method.  The pieces already
proved in `Counter.lean` are exactly the per-event rules such an accelerator
would have to assume.

### 4.6 Empirical status

A raw C simulation (`tools/sim.c`, *not* formally verified) was run for
`2·10^11` steps: no halt, tape width `113`.  Per epoch it records the closest
approach of a cascade to the frontier; the minimum over the whole run is `14`
cells, and the approach distance fluctuates without trend (recent values
`35`, `68`).  Inside Lean the verified bound is still `10^8` steps
(`not_halted_before_hundred_million`).

Heuristically, a cascade launched `n` cells from the frontier reaches it with
probability about `0.54^n` (§4.2), and `n` grows by one every few epochs while
one cascade is launched per epoch; the expected number of halting events is
therefore a convergent sum, dominated by its first terms — the machine is
almost certainly non-halting, but this is a heuristic, not a proof.

---

## 5. The missing rules of §4.5, and what they say about the invariant

This part answers the two questions left open in §4.5 and revises two claims of
§4.4.  Everything called a *theorem* is machine-checked in
[`RequestProject/Macro.lean`](RequestProject/Macro.lean) (which builds on
`Counter.lean`); everything called an *observation* comes from the instrumented
simulations in [`tools/`](tools) and is **not** formally verified.

### 5.1 Correction: there is no change of digit packing

§4.4 conjectured that the ternary counter is packed one digit per cell near the
frontier and one digit per three cells further out, and listed the resulting
"interface" as the first unknown.  That is **wrong**, and the unknown dissolves:

> *Observation.*  Decode the cells strictly between the frontier `1` and the
> head as base-3 digits (`3 ↦ 0`, `4 ↦ 1`, `0 ↦ 2`, most significant digit next
> to the frontier) at every moment at which the head arrives from the right in
> state `B`.  The decoded values are exactly `v, v+1, v+2, …` — one increment
> per arrival, with no gaps.  (`tools/counterview.py`; e.g. from `t = 26727` the
> readings are `729, 730, 731, …, 755` on a counter `7` cells wide.)

So the counter really is **one cell per digit along its whole length**, its most
significant digit next to the frontier, its least significant digit at its right
end.  What §4.4 mistook for a coarser packing is the *region to the right of the
counter*, which is not a ternary counter at all.  The ×3 factor per cell in the
visit profile is the counter; the ×2 factor per two cells further out belongs to
the other region.

Everything to the right of the counter is a block of cells holding only `2`s and
`4`s (immediately after a return sweep), or the output of the last outward pass
(`3`s, `2 0` pairs, and the occasional `4`).  The head shuttles through it and
comes back with the carry.

### 5.2 The complete local rule set

The head is always one of four particles: `A→`, `←B`, `←A` (the cascade) and the
one-cell-lookahead `B→` that only ever appears inside the `A→` rules.  The rules
below are exhaustive, and each is a theorem about an *arbitrary* configuration.

Right-moving `A→`, on a cell `x` with the cell to its left holding `p`:

| `x` | next cell | left cell `p` | effect | cost | Lean |
|---|---|---|---|---|---|
| `2` | — | — | `2 ↦ 3`, continue right | 1 | `A_on_two` |
| `4` | `3` | — | `4 3 ↦ 2 4`, continue right | 2 | `A_on_four_three` |
| `4` | `4` | — | `4 4 ↦ 2 0`, continue right | 2 | `A_over_two_fours` |
| `4` | `2` | any | bounce: `4 2 ↦ 4 4`, head arrives on `p` as `←B` | 3 | `A_bounce` |
| `4` | `2` | `3` | `3 4 2 ↦ 4 2 0`, continue right | 6 | `A_bounce_three` |
| `4` | `2` | `4` | `4 4 2 ↦ 0 2 0`, continue right | 6 | `A_bounce_four` |
| `4` | `2` | `0`/`2` | the pass **stops**: `←B` continues left | 4 | `A_turn` |
| `4` | `0` | any | the pass stops, `←B` continues left | 3 | `A_on_four_zero` |
| `3` | — | — | a **cascade** `←A` is born | 1 | `cascade_*` (§4.1) |
| `0` | — | — | fresh tape: see §5.5 | 3 | `right_end_extension` |
| `1` | — | — | **halt** | 1 | `cascade_halts_on_one` |

Left-moving `←B`: it rewrites `0 ↦ 2` and `2 ↦ 4` at one step per cell and stops
at the first cell holding something else (`B_sweep`); there it writes `3 ↦ 4`
or `4 ↦ 0` and turns into `A→`, or, at the frontier, `1 ↦ 3` and becomes a
cascade.

Left-moving `←A`: the two-mode `P`/`Q` automaton of §4.1, already proved.

### 5.3 The outward pass is a two-phase transducer

Reading the table, the outward journey of the head across a block of `2`s and
`4`s is a transducer whose state is the symbol `p` immediately to its left:
phase `3` (the head has just consumed a `2`), phase `4` (it has just crossed
`4 3`) and phase `0` (it has just crossed `4 4`, or just completed a bounce).
The pattern `4 2` is crossed in phases `3` and `4` but **stops the pass** in
phase `0`.

This is the inductive relation `Out p w q w' n` of `Macro.lean`: the head
crosses the block `w` in exactly `n` steps, leaves `w'` in its place and
rewrites the cell on its left from `p` to `q`.  `out_cross` proves that every
derivation is a genuine run of the machine.  The cost of a pass is therefore
`(#2-cells) + 2·(#44-pairs) + 2·(#43-pairs) + 6·(#bounces)`.

### 5.4 The interface rule (first unknown of §4.5)

`interface_return_increment` is the exact hand-over between the region and the
counter:

> the head coming back as `←B` across a block of cells holding `0`s and `2`s
> reaches the least significant counter digit and increments the counter — in
> exactly `(length of the block) + 1 + incrCost(counter word)` steps, leaving
> the crossed cells rewritten by `0 ↦ 2`, `2 ↦ 4` and the head on its way out
> again in state `A`.

Together with `counter_increment` and `counter_overflow` (§4.3) this closes the
left-hand side of the computation: one round trip of the head = one increment,
and `3^L` increments = one epoch, after which the frontier moves one cell left.

### 5.5 The structural events (second unknown of §4.5)

**Extension of the tape.**  `right_end_extension`: when the outward pass runs
off the used tape, three steps (`A0 → 1RB`, `B0 → 2LB`, `B1 → 3LA`) write `3 2`,
extend the used tape by two cells and emit a cascade `←A` in mode `Q`.

**The cascade re-crosses what the pass has just written.**  This is the point
that makes the halting question tractable in principle: the cascade born at the
right end travels back over the *output of the very pass that created it*.  The
pass writes a `3` for every `2` it consumes and a pair `2 0` for every pair
`4 4`; it writes a `4` only in the rules `4 3 ↦ 2 4` and `3 | 4 2 ↦ 4 | 2 0`.
A `4` kills the cascade (`cascade_P_four_stops`, `cascade_Q_four_stops`), while
a word made of `3`s and `2 0` pairs is crossed completely — that is
`cross_passRev`.  Composing the three events gives

* `pass_then_cascade_halts` — pass, extension, cascade, halt: an end-to-end
  halting rule;
* `halt_of_four_free_pass` — **the machine halts as soon as one outward pass
  reaches fresh tape leaving no `4` behind** (and the cells between the region
  and the frontier are crossable, which by `cross_digits_iff` means the counter
  digits avoid `1` and have no two consecutive `2`s);
* `halt_of_frontier_two_twos` — a worked instance, so the criterion is visibly
  not vacuous.

**The overflow of the counter** was already proved (`counter_overflow`).

So all three structural events are now exact rules, and the halting question has
become a question about the transducer of §5.3:

> **If an outward pass reaches fresh tape leaving a `4`-free trail behind it,
> the machine halts** (`halt_of_four_free_pass`, proved).

There is a second way for a cascade to be born, and it is in fact the commoner
one: the pass has no rule for a cell holding `3`, and there `A3 → 2LA` turns the
head around and starts a cascade in mode `P` (row `3` of the table in §5.2).
Since an extension leaves `3 2` behind, the *next* pass that gets that far meets
exactly that `3`.  The same composition works for this birth as well:

* `pass_then_mid_cascade_halts`, `halt_of_four_free_pass_mid` — pass, turn at a
  `3`, cascade, halt;
* `halt_of_frontier_two_twos_mid` — the corresponding worked instance.

*Observation.*  Both births happen at the right end of the used tape: an epoch in
which the head never reaches the last used cell contains no cascade at all
(epochs 29–33 of `tools/approach.c`: head reaching `76–84` cells right of the
frontier on a tape of width `93–97`, and no left-moving `A` step in the whole
epoch).  What is *not* proved is that no cascade is ever born deeper inside the
tape; that is the remaining gap in the converse direction.

### 5.6 Jumping from cascade to cascade: the `×4` law

The natural acceleration is not "one round trip at a time" but "one cascade at a
time", and the measurements say that this is a real possibility: **the events
are spaced by an exact multiplicative law in the counter value.**

Let `v` be the value of the ternary counter (§5.1) — a genuinely global clock,
since it goes up by exactly one per round trip of the head and survives the
epoch boundaries (`counter_overflow` takes `3^k − 1` to `3^k`).  Let `gap` be
the number of cells between the counter and the right end of the used tape.
`tools/cascade_counter.c` reads both off at every long cascade:

| `t` | `L` | `v` | `gap` | `v` ratio | `gap − 2·log₂v` |
|---|---|---|---|---|---|
| `5.4·10^6` | 9 | `10 191` | 60 | — | `33.370` |
| `1.8·10^7` | 10 | `40 879` | 64 | `4.0489` | `33.362` |
| `7.0·10^7` | 11 | `163 623` | 68 | `4.0113` | `33.360` |
| `2.4·10^8` | 13 | `654 605` | 72 | `4.0026` | `33.359` |
| `9.4·10^8` | 14 | `2 618 483` | 76 | `4.0001` | `33.359` |
| `5.6·10^9` | 18 | `283 089 298` | 82 | `108.11` | `25.847` |
| `2.4·10^10` | 20 | `1 414 276 258` | 86 | `4.9959` | `25.205` |
| `9.3·10^10` | 21 | `5 939 024 074` | 90 | `4.1993` | `25.065` |

Two laws are visible.

* **`gap` grows by exactly `4` cells at every cascade** (one exception, `+6`, at
  the regime change), and

* **`gap = 2·log₂ v + c`** with `c` constant to three decimal places inside a
  regime.  That is: *the region to the right of the ternary counter stores
  `log₂ v` binary digits at two cells per digit* — the two counters of §4.4 hold
  the same number `v`, on the left in base 3 at one cell per digit, on the right
  in base 2 at two cells per digit.  Consequently a cascade is launched every
  time the binary counter gains two digits, i.e.

  > **cascades happen at `v ≈ C·4^k`** — consecutive ratios `4.0489, 4.0113,
  > 4.0026, 4.0001` show `v_k/4^k` converging to a constant (`≈ 10228.46` on the
  > first regime).

So the jump the "event to event" idea asks for exists at the level of cascades:
between two cascades the counter is simply multiplied by four, and one could in
principle skip straight from one cascade to the next.  What makes this still a
conjecture rather than an accelerator is:

1. the binary semantics of the right-hand region is *not* proved — the local
   rules of §5.2 are, but the invariant "the region word is the base-2
   expansion of `v` in two-cell blocks" is exactly the sort of statement one
   would have to establish by induction over the return-sweep/outward-pass cycle;
2. the law has **regime changes**.  There are stretches of epochs in which the
   head never reaches the right end and no cascade happens at all (epochs 29–33:
   lengths `1.7·10^7, 5.2·10^7, 1.6·10^8, 4.7·10^8, 1.4·10^9`, each almost
   exactly three times its predecessor, and zero left-moving `A` steps in any of
   them).  Across such a stretch the binary side falls behind the ternary one:
   `c` drops from `33.36` to `25.07` in the table above.  Any accelerator has to
   know when the next regime change happens, and nothing in the present analysis
   predicts it.

Note also what the law does *not* buy: it jumps over the `3^L` increments of an
epoch only if the inner dynamics is summable, and it is not — see §5.6.1.

### 5.6.1 Why step-by-step acceleration is hopeless

Between two structural events the head performs one outward pass and one return
sweep per counter increment, and the pass output depends on the whole region
word.  The region word has no long runs: run-length encoding it gives blocks of
length 1–3 (`tools/shapes.py`), and a Marxen–Buntrock macro machine over blocks
of 2, 3, 4 or 6 cells with chain steps gains only a factor ≈ 3–5
(`tools/macro.py`: 20 000 macro steps ≈ 95 000 machine steps).  The `3^L`
increments of an epoch are `3^L` genuinely different local computations.  Any
real speed-up must therefore come from counter arithmetic (§5.6), not from
pattern matching on the tape.

### 5.7 What halting would mean arithmetically

Put §5.5 and §5.6 together.  A cascade is launched when `v ≈ C·4^k`; it travels
back over the word the outward pass has just written and dies at the first
surviving `4`; if it survives to the frontier the machine halts, and surviving
the counter block means (by `cross_digits_iff`) that the base-3 digits of `v`
contain no `1` and no two consecutive `2`s.  So the halting question has the
shape the "recursive sequence" guess predicted:

> does the base-3 expansion of `C·4^k` ever avoid the digit `1` (and, before
> that, does the pass leave no `4` in the `2·log₂ v` cells of the binary side)?

This is an Erdős-type question about powers of four in base three — the same
family as the conjecture that `2^n` always contains the digit `2` in base 3 for
`n > 8` — and the heuristic is strongly in favour of non-halting: the
probability that an `L`-digit base-3 string avoids `1` and has no two adjacent
`2`s is `≈ 0.54^L` with `L = log₃ v ≈ 1.26 k` growing linearly in the event
number `k`, so the expected number of halting events is a rapidly convergent
sum.  The caveat is the regime changes of §5.6: they make `C` drift, so the
sequence `C·4^k` is not literally a geometric sequence with a fixed constant.

### 5.8 The non-halting invariant: what it would have to be

The criterion of §5.5 says what an invariant has to guarantee (in addition to
excluding cascade births deep inside the tape): *every* outward pass that
reaches the right end must leave a `4` behind, i.e. must apply the rule
`4 3 ↦ 2 4` (not immediately cancelled by a following `4 | 4 2 ↦ 0 | 2 0`) or
the bounce `3 | 4 2 ↦ 4 | 2 0` somewhere between the frontier and the right end.
A non-halting proof is a set of region words containing the reachable ones,
closed under "return sweep, then outward pass", all of whose passes leave a `4`.

The natural candidate is the binary-counter invariant of §5.6 — "the region is
the base-2 expansion of `v` in two-cell blocks, plus a transition zone" — which
would make the position of the surviving `4` a function of `v` and reduce
everything to arithmetic.  Proving it is the concrete next target; the local
rules needed for the induction are all in `Macro.lean`.

What the measurements say about the margin, on the other hand, is discouraging:

> *Observation* (`tools/approach.c`, `tools/cascade_counter.c`, unverified,
> `3·10^11` steps, 37 epochs).  For the long cascades of epochs 19–37 the
> distance travelled was `22, 37, 26, 43, 30, 51, 34, 62, 38, 63, 42` cells and
> the cascade died `30, 20, 37, 20, 43, 27, 50, 14, 61, 35, 68` cells short of
> the frontier, while the tape width grew from `55` to `113`.  Neither the
> distance travelled nor the distance remaining shows a clear trend, and the
> smallest remaining distance, `14`, occurred late (epoch 28, `t ≈ 5.8·10^8`).

So the surviving `4` is not kept at a safe distance by any visible mechanism.
With one long cascade every one or two epochs and epoch lengths tripling, only
about a dozen cascades can ever be observed in a feasible simulation, so the
empirical sample cannot settle the question by itself.

**Status.**  The halting problem for this machine remains open.  What is now
available is a complete and machine-checked set of macroscopic rules
(`Macro.lean`), a proved sufficient condition for halting in terms of a single
transducer (§5.5), an exact empirical jump law between cascades (§5.6), the
arithmetic shape a halt would have to take (§5.7), and a precise statement of
what a non-halting invariant would have to prove (§5.8).

---

## 6. The region is a binary counter (this pass of the analysis)

Part 5 answered the two questions of §4.5 (the interface rule and the structural
events) and recorded the empirical `×4` law between cascades.  This part goes
one level deeper and *explains* that law: the region to the right of the ternary
counter is itself a counter, in base two, at two cells per digit, and its
increment rule is now a theorem.

### 6.1 The round trip

[`RequestProject/RoundTrip.lean`](RequestProject/RoundTrip.lean) composes the
rules of §5 into one macroscopic step, `round_trip`:

> the head leaves the counter, crosses the region block `w` (outward pass),
> turns around at the first `4 2` preceded by a `0` or a `2`, sweeps back over
> the cells it has just written and increments the ternary counter — in exactly
> `n + (4 + |t|) + incrCost(counter)` steps, where `n` is the cost of the pass
> and `w'.reverse = p :: t` is its output.

Two features of the coupling between the two halves of the tape are visible in
the statement.  The **phase in which the outward pass starts is the least
significant digit of the ternary counter** (`3 ↦` phase `3`, `4 ↦` phase `4`,
`0 ↦` phase `0`), and the pass can **change that digit** (the bounce rules
`four_two_of_three` and `four_two_of_four` turn it into the next digit up).  So
the interface of §4.5 is two-way, and both directions are now exact rules.

`round_trip` requires the pass output to be free of `3`s.  That is the *simple*
case, and it is not the general one: see §6.3.

### 6.2 The marker rule: the region counts in base two

Encode a pair of tape cells as a binary digit:

| cells | digit |
|---|---|
| `4 2` | `0` |
| `4 4` | `1` |

least significant digit first, i.e. nearest to the ternary counter
(`binWord`, `binValue` in
[`RequestProject/Binary.lean`](RequestProject/Binary.lean)).

The outward pass writes a `3` over every isolated `2` it consumes.  Call such a
cell a **marker**.  The commonest event of the whole computation is the
returning sweep meeting a marker (`B3 → 4RA`), and the effect of that event is
exactly a binary increment:

> **Theorem** (`marker_increment`).  If the cells to the right of a marker read
> `b₀`, then `k` digits `1`, then a digit `0`, then anything, the machine takes
> exactly `4k + 13` steps and comes back to the cell left of the marker in state
> `B`, having
> * turned the marker into a `2` (so the sweep now passes over it: the marker is
>   consumed),
> * left the lowest digit `b₀` untouched,
> * turned the `k` digits `1` into `0` and the digit `0` above them into `1`,
> * left everything further right untouched.
>
> In terms of the value of the region counter this adds exactly `2`
> (`binValue_marker_increment`): the digits above the lowest one go up by one.

The proof is the composition of the rules of §5: the bounce off the marker, the
outward pass over the carry chain (`4 4 ↦ 2 0` per digit), the turn at the first
digit `0`, and the return sweep (`2 0 ↦ 4 2` per digit, restoring the digits as
zeros).  The two cases `b₀ = 0` and `b₀ = 1` run differently — with `b₀ = 0` the
pass bumps the marker to a `0` on its way out, with `b₀ = 1` it does not, and the
sweep has to turn around once more on the marker (`B4 → 0RA`) — yet both take
`4k + 13` steps.

*Measurement* (`tools/markerstats.c`, unverified, `2·10^9` steps).  There are
`1.11·10^8` marker events; the hypothesis of `marker_increment` holds at
`5.05·10^7` of them (50.5 %), and those events account for **40.7 % of all
machine steps**.  The carry lengths are

| `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | ≥9 |
|---|---|---|---|---|---|---|---|---|---|---|
| count | 41 465 275 | 11 177 406 | 1 754 378 | 877 149 | 438 528 | 218 912 | 109 008 | 53 586 | 21 336 | 94 |

— from `k = 2` on each carry length is half as frequent as the one before, which
is exactly the carry distribution of a binary counter.  At the remaining marker
events the pattern is broken: in half of them the cell right of the marker holds
a `2` (a second marker is about to be created there), in the other half the
carry chain runs into the transition zone instead of into a digit `0`.

### 6.3 What this explains, and what is still missing

**It explains the `×4` law of §5.6.**  The region counter goes up by `2` per
marker event and there are boundedly many marker events per increment of the
ternary counter (≈ 25 in the measured range), so its value is proportional to
`v` and it needs `log₂ v` digits, i.e. `2·log₂ v` cells — which is precisely the
observed `gap = 2·log₂ v + c`.  A cascade is the event in which the binary
counter grows into fresh tape, and `gap` grows by `4` there, i.e. one cascade per
two new binary digits: cascades at `v ≈ C·4^k`.  The empirical law of §5.6 is
therefore a consequence of a proved local rule plus one unproved global fact
(that the region really is in binary-counter shape all the way out).

**What is missing** for an accelerated simulation, and for a non-halting
invariant, is exactly that global fact.  Concretely:

1. the global shape.  The two local rules `marker_increment` and `marker_shift`
   (the latter: a marker whose successor cell holds a `2` leaves a `4` behind,
   moves one cell right and resumes the pass) cover every marker event, but
   knowing which of the two applies requires knowing the shape of the region;
2. the invariant "between the ternary counter and the right end the tape is a
   transition zone of bounded width followed by a binary counter", closed under
   the events of §5 and §6.2;
3. the position of the surviving `4` in the pass output as a function of the
   binary counter — this is what a cascade runs into, and what the non-halting
   proof has to bound away from the frontier (§5.8).

Item 2 is now a much more concrete statement than it was in §5.8, because the
digits and their increment rule are pinned down; items 1 and 3 are the remaining
gaps.

*Measurement* (`tools/tripstats.c`, unverified, `2·10^9` steps).  The head's
excursions are short: between two visits to the counter it never travels more
than `77` cells to the right, and the longest excursion took `1830` steps; the
record reach grows by about `4` cells per multiplication of the step count by
`3.6`, and every record excursion is one that reaches the right end of the used
tape — i.e. a cascade.  So the machine is a local oscillator that touches the far
end of its tape only at the rare cascade events.

### 6.4 Comparison with the solved 2×5 machine "BMO3"

The reduction quoted for that machine is: `a₀ = 2`,
`aₙ = aₙ₋₁ + 2^(v₂(aₙ₋₁)+2) − 1`, and it halts iff some `aₙ` is a power of four.
The structure here is the same kind of object — a recursively defined integer
sequence together with an arithmetic condition — but the two ingredients differ:

* **the recursion.**  Here the natural sequence is the value `v` of the ternary
  counter at the successive cascades.  Measured (`tools/events.c`,
  `tools/cascade_counter.c`): the tape-extension events happen at
  `v = 23, 95, 127, 505, 359, 1559, 6351, 25539, 102247, 409137, 1636521, …` and
  the long cascades at `v = 10191, 40879, 163623, 654605, 2618483, …,
  283089298, 1414276258, 5939024074, 24037989554`.  Successive values satisfy
  `v_{k+1} = 4·v_k + δ_k` with `|δ_k| ≲ 150` (observed corrections `123, 115,
  135, 91, 149, −27`; `115, 107, 113, 63` for the cascades).  Pinning `δ_k` down
  as a function of the state — which §6.2 brings within reach, since the state
  is now two counters and a bounded transition zone — would give a BMO3-style
  exact recursion.
* **the halting condition.**  It is *not* literally "`v` is a power of four".
  By `cross_digits_iff` a cascade survives the ternary counter exactly when the
  base-3 digits of `v` avoid `1` and have no two consecutive `2`s (a Cantor-type
  condition), and it must in addition find no surviving `4` in the region.  Note
  that `4^k` in base 3 contains the digit `1` (`4 = 11₃`), so the two conditions
  are genuinely different; what the `×4` law gives is that the *candidates* are
  the values `v ≈ C·4^k`, not that halting means `v = 4^k`.

So the analogy is structural: both machines reduce to "does a recursively
defined sequence ever satisfy a digit condition?", and for this machine the
recursion is `v ↦ 4v + δ` and the condition is a Cantor condition in base 3.

---

## 7. The outward pass as a function, and what stops a cascade

Part 6 ended with three missing items (§6.3): the *coverage* of the local rules,
the global shape invariant, and the position of the surviving `4`.  This part
settles the first and the third, in
[`RequestProject/Pass.lean`](RequestProject/Pass.lean); the second is still
open.

### 7.1 Coverage: the pass is a total computable function

`passF p w` takes the **phase** `p` (the symbol in the cell immediately to the
left of the head, which is what decides the behaviour at the pattern `4 2`) and
the whole tape `w` to the right of the head, and returns the complete
description of the outward pass: its exact step count, the exact word it leaves
behind, and *how it ends*.  `passF_correct` proves that the machine does exactly
that, for every phase and every tape.

There are exactly four ways a pass can end (`PassEnd`):

| end | cause | what happens |
|---|---|---|
| `turn` | a `4 2` met in phase `0` or `2` | the head turns, comes back as a left-moving `B` |
| `turnZero` | a `4` at the right edge of the used tape | same, three steps |
| `mark` | the head runs onto a cell holding `3` | a mode-`P` cascade is born (`A3 → 2LA`) |
| `fresh` | the head runs off the right end | the tape grows by two cells, a mode-`Q` cascade is born |

together with the halting case (a `1`).  `passF_ne_other` proves that this list
is exhaustive on any region made of the symbols `2`, `3`, `4` entered with any
phase other than the frontier symbol `1`: the residual branches of the function
are unreachable.  This is exactly the coverage statement asked for in item 1 of
§6.3 — *which* rule applies is now a computable function of the region word.

Since a marker event is just `B3 → 4RA` followed by a pass in phase `4`,
`markerF = passF 4` (plus one step) classifies **every** marker event
(`markerF_correct`), with `marker_increment` and `marker_shift` of §6.2 as the
two cases that occur when the region is in binary-counter shape.

### 7.2 Where the surviving `4`s are (item 3)

Reading off the definition of `passF`, a cell holds a `4` after the pass in
exactly two situations:

* it held a `2`, the pass wrote a `3` over it, and the head **bounced** off that
  fresh marker at the following `4 2` (rule `four_two_of_three`, which turns it
  into a `4`);
* it held a `3` — an older marker — crossed as the second cell of a pattern
  `4 3`, without an immediate bounce afterwards.

Everything else the pass writes is a `3` (over a consumed `2`) or a pair `2 0`
(over a consumed `4 4`), and those are exactly the words a cascade crosses
(`PassFwd`, the tape-order form of `PassRev`).  The decision procedure
`noFourOut p w` implements this: it returns `some q` — `q` being the final
content of the phase cell — precisely when the pass writes no `4` in the region.
`noFourOut_sound` proves it sound, and `noFourOut_complete_upto_eight` checks by
evaluation that it is also necessary, for every region word of length at most
`8` and every phase.

The two consequences are the two halves of the halting question:

* `halt_of_noFour_fresh` — if the pass runs off the right end, leaves no `4`,
  and its last written cell is a marker, then the cascade born at the right end
  crosses the whole pass output; the machine then halts as soon as the cells
  beyond it are crossable (the Cantor condition of §4.2).
* `mark_cascade_dies` — conversely, if the word the pass leaves behind contains
  a `4`, the cascade crosses the cells to the right of it, runs into that `4`
  and is extinguished (`passRev_traverse`, `passRev_dies_at_four`), and the
  machine is alive at every step of the excursion.  `bounce_example` is a
  concrete instance.

So the fate of each cascade is decided by a single local feature of the pass
that produced it: whether that pass bounced off a marker.

### 7.3 Measurement: what actually stops the cascades

*(`tools/shield.c`, unverified, `2·10^10` steps.)*  Only two transitions of the
machine ever write a `4`: `B2 → 4LB`, the returning sweep crossing a `2`, and
`B3 → 4RA`, a marker event.  Recording the origin of the `4` at every cascade
death gives

| how the cascade died | count | of which ≥ 5 cells |
|---|---|---|
| ran into a `4` written by a marker event (`B3`) | 53 | 13 |
| ran into a `4` written by the sweep (`B2`) | 0 | 0 |
| stopped on a `0` in mode `Q` | 59 | 4 |
| stopped on a `2` in mode `P` | 0 | 0 |

— 112 cascades in `2·10^10` steps, and **every single `4` that ever stopped a
cascade was written by a marker event**, i.e. was a bounced marker, exactly the
mechanism isolated in §7.2.  The stopping cells of the long cascades sit at
distances `1, 5, 6, 12, 9, 18, 12, 30, 20, 37, 24, 43, 27, 50, 26, 13, 61` from
the frontier, in order of occurrence — the leading `1` is the initial transient
at step `99`, when the used tape was ten cells wide, and from then on the
closest approach is `5`.  The run reached `2·10^10` steps without halting.

### 7.4 A `4` between the frontier and a cascade is enough

The shield of §7.2 needed the cells between the cascade and the `4` to be the
output of a four-free pass.  That hypothesis can be dropped completely
([`RequestProject/Shield.lean`](RequestProject/Shield.lean)):

> **Theorem** (`cascade_dies_before_four`).  If a left-moving cascade has a cell
> holding `4` somewhere to its left and none of the cells in between is the
> frontier symbol `1`, then the cascade comes to an end in finitely many steps —
> in one of exactly four ways (`CascadeOver`: it meets the `4` in mode `P` or in
> mode `Q`, or it stops earlier on a `2` in mode `P` or on a `0` in mode `Q`) —
> and the machine does not halt at any step in between.

The proof is an induction on the cells between the head and the `4`: at each one
the cascade either crosses it (a `3` in either mode, a `0` in mode `P`, a `2` in
mode `Q`) or stops there, and the distance to the `4` decreases.

*Measurement* (`tools/fours.c`, unverified, `2·10^10` steps).  There were `299`
cascade births — a cascade birth being the first step at which the head arrives
moving left in state `A`, the head being strictly right of the frontier — and
**at every one of them at least one cell between the frontier and the head held
a `4`**; the distribution of that count is

| `4`s between frontier and head at birth | 1 | 2 | 3 | 4 | 5 | 6 | ≥7 |
|---|---|---|---|---|---|---|---|
| births | 30 | 16 | 17 | 55 | 107 | 18 | 56 |

with minimum `1`.  So `cascade_dies_before_four` accounts for every cascade the
machine has been observed to produce.  (The count does drop to `0` at other
moments — `2.9·10^6` of the `2·10^10` steps have the head in state `A`, at
distance at least two from the frontier, with no `4` in between — but never at a
cascade birth.)

This reduces the non-halting problem to a single clean statement:

> **Conjecture.**  At every cascade birth there is a cell holding `4` strictly
> between the frontier and the head.

By the theorem above, that conjecture implies that the machine never halts.

### 7.5 What is still missing

Item 2 of §6.3 — the global shape invariant — is untouched by this part, and it
is now the only thing standing between the proved local calculus and a
non-halting proof: it is what the conjecture of §7.4 would need.  What would be
needed is a set `S` of region words such that

1. `S` is closed under the events of §5–§7 (marker increment, marker shift,
   round trip, tape extension), and
2. every pass starting from a word of `S` that ends in `mark` or `fresh` leaves
   a `4` behind, at a position whose distance to the frontier stays positive.

Condition 2 is now a decidable property of the word (`noFourOut`), and
condition 1 is a statement about a map that is now a *function* (`passF`); what
is missing is the invariant itself, i.e. the proof that the region stays in
binary-counter shape with a bounded transition zone.

---

## 8. The second shield: the ternary counter at the cascade moments

### 8.1 A correction

An earlier pass of this analysis dismissed the ternary counter as a possible
cause of non-halting with the argument: *the counter is incremented once per
round trip, so it runs through all values, and in particular through
Cantor-compatible ones; therefore the Cantor criterion cannot be what blocks
every cascade.*  That argument is wrong, and the objection to it is exactly
right: the Cantor criterion is not tested at every value of the counter.  It is
tested **only at the rare moments a cascade is born** — by §5.6/§6.3 at counter
values `v ≈ C·4^k`, i.e. at a sparse, geometrically thin subsequence of the
values the counter takes.  Whether that subsequence ever lands in the Cantor set
is a genuine open question, and it is a perfectly possible mechanism for
non-halting.  §8 replaces the bad argument by what can actually be said.

### 8.2 What the criterion is

By `cross_digits_iff` (§4, `RequestProject/Counter.lean`) a cascade arriving at
the counter crosses it — and so reaches the frontier `1` and halts the machine —
**iff** the digit cells it meets contain

* no cell holding `4` (no base-3 digit `1`), and
* no two consecutive cells holding `0` (no two consecutive base-3 digits `2`).

The digits are met most significant first, and adjacency is symmetric, so this
is a condition on the base-3 expansion of the counter value `v`: it must be a
word over `{0,2}` with no factor `22`.  The set of reals whose base-3 expansion
avoids `1` is the Cantor set; hence "Cantor criterion".

### 8.3 Measurement at the cascade moments

*(`tools/cantor.c`, unverified, `2·10^10` steps.)*  A cascade is delimited here
by its three stopping patterns, so each cascade is counted once (the naive
"left-moving `A` step" flag counts a long cascade many times, because crossing a
digit `2` in mode `Q` performs the right-moving step `A2 → 3RA`).

| cascades | counter Cantor-compatible | blocked by a digit `1` | blocked by `22` only |
|---|---|---|---|
| 78 | **0** | 78 | 0 |

The distinct counter values at those 78 cascades, with their base-3 expansions:

| `v` | base 3 | digits `1` | factor `22`? |
|---|---|---|---|
| 1 | `1` | 1 | no |
| 3 | `10` | 1 | no |
| 5 | `12` | 1 | no |
| 9 | `100` | 1 | no |
| 23 | `212` | 1 | no |
| 29 | `1002` | 1 | no |
| 39 | `1110` | 3 | no |
| 59 | `2012` | 1 | no |
| 89 | `10022` | 1 | yes |
| 95 | `10112` | 3 | no |
| 119 | `11102` | 3 | no |
| 127 | `11201` | 3 | no |
| 151 | `12121` | 3 | no |
| 201 | `21110` | 3 | no |
| 359 | `111022` | 3 | yes |
| 505 | `200201` | 1 | no |
| 599 | `211012` | 3 | no |
| 809 | `1002222` | 1 | yes |
| 1559 | `2010202` | 1 | no |
| 2517 | `10110020` | 3 | no |
| 6351 | `22201020` | 1 | yes |
| 10191 | `111222110` | 5 | yes |
| 25539 | `1022000220` | 1 | yes |
| 40879 | `2002002001` | 1 | no |
| 102247 | `12012020221` | 3 | yes |
| 163623 | `22022110010` | 3 | yes |
| 409137 | `202210020020` | 1 | yes |
| 654605 | `1020020221122` | 3 | yes |
| 1636521 | `10002010212220` | 3 | yes |
| 2618483 | `11221000212212` | 5 | yes |
| 141693346 | `100212121202201201` | 6 | yes |
| 283089298 | `201201200102111211` | 8 | no |
| 848679538 | `2012010221101110111` | 10 | yes |

Every one of them has at least one digit `1`, so every cascade so far was
blocked by the counter as well as by the region.  Two things are worth noting.

* **The margin is thin.**  Ten of the 33 distinct values — `1, 3, 5, 9, 23, 29,
  59, 505, 1559, 40879` — have *exactly one* digit `1` and no factor `22`:
  changing a single digit would make them Cantor-compatible.  The number of digit `1`s does grow with `v`
  (distribution over the 78 cascades: `1`→43, `3`→24, `5`→4, `6`→3, `8`→1,
  `10`→3), but slowly.
* **`4^k` is not the point.**  Since `4 = 11₃`, the values `4^k` themselves are
  *not* Cantor-compatible, but the cascade values are `v ≈ C·4^k` with a
  correction, not `4^k`, so no such cheap argument is available.

### 8.4 Why one should expect this to continue (heuristic, not a proof)

Count the Cantor-compatible words: the number of words of length `n` over
`{0,2}` with no factor `22` is a Fibonacci number, `≈ c·φⁿ` with `φ = 1.618…`,
against `3ⁿ` words in total, so a "random" base-3 word of length `n` is
Cantor-compatible with probability `≈ c·(φ/3)ⁿ = c·0.539ⁿ`.  At the `k`-th
cascade the counter has `n ≈ k·log 4 / log 3 = 1.26·k` digits, whence

  `P(k-th cascade crosses the counter) ≈ 0.539^{1.26 k} ≈ 0.459^k`,

a geometric sequence.  Its sum over all `k` converges, and is dominated by the
first few terms — which have been checked explicitly, and all failed.  So the
heuristic expected number of counter-crossings over the whole infinite future is
finite and, after the first ~30 cascades, small.  This is a Borel–Cantelli-type
argument of the kind familiar from Collatz-like problems: it supports
non-halting and proves nothing, because the digits of `v` are not random.

### 8.5 Two independent shields

The machine is therefore protected twice over, and the two protections are
logically independent:

1. **the region shield** (§7.4): at every observed cascade birth there is a cell
   holding `4` strictly between the frontier and the head — a bounced marker —
   and `cascade_dies_before_four` turns that into a proof that the cascade dies;
2. **the counter shield** (§8.3): at every observed cascade birth the ternary
   counter is not Cantor-compatible, and `cascade_dies_of_not_cantor` (new in
   `RequestProject/Shield.lean`) turns *that* into a proof that the cascade
   dies.

The second one is the formal counterpart of the objection answered in §8.1.  Its
statement is:

> **Theorem** (`cascade_dies_of_not_cantor`).  If the cells ahead of a
> left-moving cascade split as `u ++ v` where no cell of `u` is the frontier
> symbol `1` and `v` begins either with a cell holding `4` or with two cells
> holding `0`, then the cascade comes to an end in finitely many steps, in one
> of the four ways of `CascadeOver`, and the machine does not halt in between
> (`no_halt_before_stopper`).

It is proved by the same induction as §7.4, now run against an abstract
*stopper* (`StopsCascade`): a block of cells that ends every cascade arriving on
it, whatever its mode and whatever the tape to its right.  `4` and `0 0` are
stoppers (`stopsCascade_four`, `stopsCascade_zero_zero`), and these two are
exactly the negation of the Cantor criterion of §8.2.

So a halt requires **both** shields to be down at the same cascade: the counter
must be Cantor-compatible *and* the whole stretch of region between the cascade
and the counter must be free of `4`s and of `0 0`.  Either invariant alone
suffices for non-halting; neither is proved.

### 8.6 Status

Halting remains open.  The proved part of the argument is now: *a complete local
calculus (§5–§7), the fact that the pass is a total computable function of the
tape (§7.1), and two shield theorems that convert either invariant into a
non-halting proof (§7.4, §8.5).*  The missing part is unchanged and is a single
global statement — the shape invariant of item 2 of §6.3 — in either of the two
forms the shields ask for.

### 8.7 Which numbers are actually tested

The Cantor condition of §8.2 is a condition on the value `v` of the base-3
counter, but the counter runs through *every* value (it is incremented once per
round trip), so the question "does the machine halt?" is the question

> does the condition hold for one of the **tested** values — the values `v` takes
> at the rare moments a cascade is born?

Those are the numbers that get checked.  Measured (`tools/cantor.c`, unverified,
`2·10^10` steps) the tested values, in order of first occurrence, are

`1, 3, 5, 9, 23, 29, 39, 59, 89, 95, 119, 127, 151, 201, 359, 505, 599, 809,
1559, 2517, 6351, 10191, 25539, 40879, 102247, 163623, 409137, 654605, 1636521,
2618483, 141693346, 283089298, 848679538, …`

and from `v = 2517` on they organise into **two interleaved chains, each
multiplying by 4**:

| chain | values | `v_{k+1} − 4·v_k` |
|---|---|---|
| A | 2517, 10191, 40879, 163623, 654605, 2618483, … | 123, 115, 107, 113, 63 |
| B | 6351, 25539, 102247, 409137, 1636521, … | 135, 91, 149, −27 |

with `v_B ≈ 2.5·v_A`, so that the observed ratios between consecutive tested
values settle at `1.6` and `2.5` (and `1.6 × 2.5 = 4`).  In closed form the
tested values look like `v ≈ 2557·4^k` and `v ≈ 6393·4^k`; the law is not exact
(the chain structure does break occasionally — after `2618483` the next value
seen is `141693346`, a jump of about `4^3.4`), which is why §6.3 item 2 has to be
proved rather than read off.

So the halting question, in the "does a recursive sequence hit a value of some
form?" shape asked for at the start, is:

> Let `v_k` be the value of the base-3 counter at the `k`-th cascade, a sequence
> satisfying `v_{k+2} = 4·v_k + δ_k` with small `δ_k`.  Does some `v_k` have a
> base-3 expansion that avoids the digit `1` and contains no two consecutive
> digits `2`?  (And, if so, does the region shield of §7.4 also fail there?)

`cross_digits_iff` and `cascade_dies_of_not_cantor` are the two directions of the
digit condition, both proved; the recursion `v_{k+2} = 4 v_k + δ_k` is measured,
not proved, and pinning down `δ_k` is exactly the global shape invariant that is
still missing.

### 8.8 Closing a gap in the standing assumption

Everything above rests on: *a halt can only be caused by something arriving at a
cell holding `1` from the right.*  `pre_halt_shape` (§3) does not give that — it
leaves five local situations, three of which have the head moving **right** onto
a `1`.  Those three are now excluded
([`RequestProject/Frontier.lean`](RequestProject/Frontier.lean)) by a one-line
invariant:

> **Theorem** (`noOneRight_run`).  At every reachable configuration, no cell
> strictly to the right of the head holds a `1`.

It holds initially and is preserved by every transition, because the only
transition that writes a `1` is `A0 → 1RB`, which moves right and so leaves the
`1` behind it, while the four left-moving transitions write `2`, `3`, `4`, `2`.
Hence

> **Theorem** (`halt_needs_left_arrival`).  If the machine halts, it passes
> through a reachable configuration with a `1` in the cell to the left of the
> head, in state `A` on a `3` or in state `B` on a `1` — i.e. the head moves
> *left* onto the `1`.  Equivalently (`not_halts_of_no_left_arrival`): if no
> reachable configuration is of that shape, the machine never halts.

This is what licenses the cascade analysis: a halt is a cascade event, and the
shields of §7.4 and §8.5 are about exactly that.
