# `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---`: bouncer + chaotic counter, and it halts

```
      0     1     2     3     4
A   1RB   4RA   1LA   4RB   2LA
B   2LB   3LA   1RB   2RA   ---
```

The only halting transition is **state `B` reading `4`**.

## Status

**The machine halts, and this is proved in Lean:** `BCM.halts : BCM.Halts`
(`RequestProject/Halt/Verified.lean`), where `Halts := ∃ n, run n init = none`.
`#print axioms BCM.halts` gives
`propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound`.
The last two come from one `native_decide` evaluation, so the Lean compiler is
part of the trusted base for this one theorem.  Every other theorem below uses
only `propext, Classical.choice, Quot.sound`.  There is no `sorry`, no added
`axiom` and no `implemented_by` in the project.

The halt happens in tape cell **238** of the right half-tape (the cell whose
input word begins `B A B A`; cell 237's input word begins `ABBAABB`).  From C
computations that are *not* part of the Lean proof: this happens at about
`N ≈ 9.6·10^26` arrivals of the bouncer at the counter, i.e. after roughly
**`5.6·10^53` machine steps** (estimate `≈ 0.6·N²`, from the bouncer timing
below).  The Lean statement asserts only that some finite run halts.

Building: `lake build` builds everything.  `RequestProject.Halt.Verified`
takes about 1.5 minutes (one core, a few GB of memory); every other module takes
seconds.

---

## 1. The bouncer (`RequestProject/Wall.lean`)  — Lean-proved

Split the tape at cell `0`.  The left half is a bouncer (the "wall") that grows
by one block `144` every five visits.  With the block `E = [4,4,1]` (nearest
cell first; the wall reads `…144144` from left to right), the left half-tape is
always one of

| phase | wall (nearest cell first) | excursion length | head returns in |
|-------|---------------------------|------------------|-----------------|
| 0     | `E^n`                     | `10n + 1`        | `B`             |
| 1     | `1 :: E^n`                | `1`              | `A`             |
| 2     | `4 :: E^n`                | `10n + 3`        | `B`             |
| 3     | `1 :: 1 :: E^n`           | `1`              | `A`             |
| 4     | `4 :: 1 :: E^n`           | `10n + 9`        | `B`             |

and phase 4 goes to phase 0 with `n+1` blocks.  `BCM.wall_excursion`: from each
of these, entered in state `A` from cell `0`, the machine runs exactly the
listed number of steps, never reads cell `0` or anything to its right, and puts
the head back on cell `0` in the listed state, with the wall in the next phase.
The excursion itself is a leftward sweep turning `144` into `212`
(`sweepL`, 5 steps per block), a turn at the blank end (`turn`), and a
rightward sweep turning `212` back into `144` (`sweepR`).

So the bouncer is eliminated: the right half-tape (cells `≥ 0`) receives the
arrival stream

```
A (B A B A B)^ω
```

(the initial `A` is the machine starting on cell `0` in state `A`).

## 2. The counter as a cascade of cell transducers — Lean-proved

`RequestProject/Cascade.lean`: every cell of the right half-tape is the same
finite transducer `cell1 c f x` (content `c`, flag `f` = "right neighbour is
non-blank", arriving state `x`) → new content, new flag, list of states sent to
the right neighbour:

| content | arrival `A`                          | arrival `B`                                  |
|---------|--------------------------------------|----------------------------------------------|
| `0`     | send `B`, → `3` (flag set)           | → `2` (head leaves in `B`)                   |
| `1`     | send `A`, → `2`                      | → `3`                                        |
| `2`     | → `1`                                | send `B`, → `3` (blank nbr) / send `BA`, → `2` |
| `3`     | **HALT** (blank nbr) / send `B`, → `2` | send `A`, → `1`                            |
| `4`     | → `2`                                | **HALT**                                     |

(Content `4` never occurs at rest.)  Theorems:

* `sound_lvl`: the machine really performs the depth-first processing `lvl`.
* **`halts_iff`**: `Halts ↔ ∃ N n, seqO (lvl n) (word N) [] = .halt` — the
  machine halts iff the cascade halts on a finite prefix of the arrival stream.

`RequestProject/Levels.lean`: the level (breadth-first, longitudinal) picture.
`lev [] (word N) p` is the input word of cell `p`; the word of cell `p+1` is
the output of cell `p`.

* `exists_haltsAt_of_halts`: a halt of the machine is a halt of one cell on
  its level word.
* **`cellDies_blank_iff`**: a blank cell halts on its input word iff the word
  begins with **`B A B A`**.
* **`not_halts_of_no_BABA`**: if no level word ever begins with `BABA`, the
  machine never halts.
* **`halts_of_BABA`**: if a level word begins with `BABA` and the cascade on
  that prefix dies out, the machine halts.

## 3. The chaotic counter (`RequestProject/Counter.lean`) — Lean-proved

After its first emission a cell holds `1`, `2` or `3` forever and can never
halt (`cellDies_emitted`).  In this regime it is **one digit of a binary
counter whose 1-digits carry a colour**:

| content | digit           |
|---------|-----------------|
| `2`     | `0`             |
| `1`     | `1`, colour a   |
| `3`     | `1`, colour b   |

`A` = increment, `B` = a second signal:

```
A at 0            -> 1 (colour a), sends nothing
A at 1 (colour a) -> 0,            carry A
A at 1 (colour b) -> 0,            carry B
B at 0            -> 0,            sends B A
B at 1 (colour a) -> 1 (colour b), sends nothing
B at 1 (colour b) -> 1 (colour a), sends A
```

* **`phase_law`**: the digit after reading `w` is the starting digit plus the
  number of `A`s in `w`, mod 2.  `B`s and colours never change the digit.
* **Token form** (`token_zero`, `token_one`): cut the input at its `A`s into
  tokens `B^r A`.  Tokens are read alternately by a `0`-digit and a `1`-digit
  (the `1`-digit always starts with colour a):
  * a `0`-digit turns `B^r A` into `(B A)^r`;
  * a `1`-digit turns `B^s A` into `A^⌊s/2⌋` followed by `A` (`s` even) or `B`
    (`s` odd).

  So each `B` read at `0` is copied with an increment attached, and the `B`s
  read at `1` pair up into increments; the parity of the `B`-run decides the
  type of the carry.  That parity is the only source of the chaos.
* There seems to be no additive invariant beyond the phase law: a short hand
  calculation (not formalized) shows that no assignment of integer values to
  `A`, `B`, the three digits and a digit weight makes all six rules additive,
  except mod 2.
* **`BABA_preimage`** (the dangerous prefixes): a blank cell emits a word
  beginning with `BABA` — the word on which the next cell halts — iff its own
  input begins with **`ABBAAA`, `ABBAABB`, `BBBBAAA` or `BBBBAABB`**.

## 4. Periods of the level words — numerical, not Lean-proved

Each level word is eventually periodic, `x·y^ω`.  Cut the period `y` (rotated
to end in `A`) into tokens `B^{r_t} A`; let `a = #A(y)`, `b = #B(y)`.

* **`a` odd:** the next period covers two copies of `y` (every token is read
  once by a `0`-digit and once by a `1`-digit), and
  `|y'| = 2b + a + Σ_t ⌊r_t/2⌋`.
* **`a` even:** the next period covers one copy; the tokens split into those
  read at `0` and those read at `1`, and
  `|y'| = Σ_{read at 0} 2r_t + Σ_{read at 1} (⌊r_t/2⌋ + 1)`.

Both formulas were checked against the exact words for cells 0–54 (Python,
`tools/`).  They follow from the token form above, but I did not prove the
period statement in Lean.

The difference from the other counter machine: the parity of `#A` of the period
is **not** preserved.  Over cells 0–170 it is odd 92 times and even 79 times,
so the period length does a multiplicative random walk: roughly ×1.55 on an odd
step and ×0.78 on an even step.  The drift is positive: `|y|` grows from 5 at
cell 0 to 3 831 101 441 at cell 170 (≈ ×1.128 per cell).  The letter density
settles near `#A/|y| ≈ 0.548`, and one letter of a cell produces about 0.78
letters of the next.

## 5. How the halt was found

* `tools/exact.c` computes the exact words `x·y^ω` of cells 0–170 (minimal
  period, rotated prefix; `tools/exact_cells_0_170.txt`).  None of these cells
  ever halts.
* `tools/stream.c` streams the exact word of a cell `c₀` through the cells
  above it.  Started from `c₀ = 160`, `165` and `170`, it finds the same halt
  every time: **cell 238 receives `BABA`**, after cell 237 received `ABBAABB`
  (`tools/stream165_halt.txt`).
* Near misses before the halt (cells whose word agrees with a dangerous prefix
  on its first 5 letters or more): cells 12, 212 and 235 (`ABBAABA…`, one letter
  away from `ABBAABB`), and cells 86 and 95 (`BBBBA B…`).  Cells 41, 76, 92,
  119 and 230 agree on 4 letters.
* Cross-checks: the step table of the Lean engine is checked against the Lean
  transducer `cell1` by `decide`; the Lean engine reproduces the period lengths
  of the C program (e.g. cells 10–130) and the halt; and the words of cells 0–4
  agree with crossing sequences of the real machine over 3·10⁵ steps
  (`tools/crossings.py`).

## 6. The Lean proof of halting (`HaltEngine.lean`, `RequestProject/Halt/`)

This is the verified engine from your project on
`1RB3RB3LA4LA2RB_2LB3RA---1RA1LA`, adapted to this machine.  What changed: the
cell step table, the blank initial half-tape, the arrival stream `A (BABAB)^ω`
and its bookkeeping (`lev [] (word (1 + 5·(a + b·k))) q = x ++ y^k`).  The
soundness proofs carried over with small edits.

* `HaltEngine.check 170 1 80 524288` computes the periodic level words up to
  cell 170 (period 3 831 101 441 letters, eight letters per byte), streams the
  prefix and one period through cells 170–249, and reports a *quiet* halt: a
  cell halts before emitting anything, so the next level word is empty and the
  cascade has died out.
* `BCM.Eng.halts_of_check` (soundness, standard axioms only): if the check
  returns `true`, the machine halts.
* `BCM.check_ok` (`native_decide`, about 80 s) and **`BCM.halts`**.

## Files

| file | content |
|------|---------|
| `RequestProject/TM.lean` | machine, configurations, `step`, `run`, `Halts` |
| `RequestProject/Wall.lean` | bouncer elimination (`wall_excursion`) |
| `RequestProject/Cascade.lean` | cell transducer, `sound_lvl`, `halts_iff` |
| `RequestProject/Levels.lean` | level words, `BABA` criterion, `not_halts_of_no_BABA`, `halts_of_BABA` |
| `RequestProject/Counter.lean` | digit encoding, `phase_law`, `token_zero`, `token_one`, `BABA_preimage` |
| `HaltEngine.lean` | executable bit-packed engine (compiled) |
| `RequestProject/Halt/*.lean` | engine soundness, `check_ok`, `halts` |
| `tools/` | C/Python exploration (not verified): exact words, streaming, bookkeeping |
