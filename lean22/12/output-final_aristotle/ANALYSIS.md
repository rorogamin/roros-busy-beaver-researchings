# The Turing machine `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` halts

Two states `A, B`, five symbols `0..4`, blank `0`.

| state | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| **A** | `1RB` | `3RB` | `3LA` | `4LA` | `2RB` |
| **B** | `2LB` | `3RA` | **halt** | `1RA` | `1LA` |

The only halting transition is **state `B` reading symbol `2`**.

## Status

**The machine halts, and this is proved in Lean**: `TM5.halts : TM5.Halts`
(`RequestProject/Halt/Verified.lean`), where `TM5.Halts := ∃ n, run n init = none`
(`RequestProject/TM.lean`). `#print axioms TM5.halts` gives
`propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound`.

The proof has two parts:

* a soundness theorem `TM5.Eng.halts_of_check` (no `sorry`, standard axioms
  only) for a fast, bit-packed executable check `HaltEngine.check` of the level
  cascade;
* one compiled evaluation, `HaltEngine.check 44 12 260 524288 = true`, done by
  `native_decide`. The Lean compiler and `Lean.ofReduceBool` are therefore part
  of the trusted base. Building `RequestProject.Halt.Verified` takes a bit over
  an hour on one core and about 25 GB of memory; every other module builds in
  a few minutes.

The halt occurs in cell 200 of the level cascade, whose input word begins
`BAAA`; cell 199's input word begins with `ABBBB`. By earlier C computations
(not part of the Lean proof) this is at wall-stream position `N ≈ 3.42·10¹⁴`,
i.e. after roughly **7.3·10²⁸ machine steps**. The step count is only an
estimate; the Lean statement asserts only that some finite run halts.

The project has been trimmed to the halting core: every Lean declaration left
is used by the proof of `TM5.halts` (apart from a few `rfl` simp lemmas).
The whole development uses only Lean core (no Mathlib imports). Exploratory
material (simulators, the non-halting reduction, counting results, simulation
bounds, C cross-checks) was removed and remains available in the git history
(commit `163dddc`).

## 1. The wall (bouncer elimination) — `RequestProject/Wall.lean`

Configurations are zippers `⟨state, left, cur, right⟩` (both lists
nearest-cell-first, unlisted cells blank). With

```
E  = [1,3,2,3,3]      (the block by which the wall grows)
Tw = [3,2,3,3]        Cw = [4,3,4,4,1]      Dw = [3,1,3,2,3]
```

every entry of the head into the wall (from cell 1, in state `A`) has the form
`wcfg r n R = ⟨A, wpre r ++ E^n, curOf r, R⟩`, `r = 0,…,7`:

| phase `r` | `wpre r` | `curOf r` | steps of the excursion | exit state |
|---|---|---|---|---|
| 0 | `[3,2,3,3]` | 3 | `16n+17` | `B` |
| 1 | `[]`        | 3 | `16n+5`  | `A` |
| 2 | `[3]`       | 3 | `16n+7`  | `B` |
| 3 | `[3,3]`     | 2 | `16n+9`  | `A` |
| 4 | `[2,3,3]`   | 1 | `1`      | `B` |
| 5 | `[2,3,3]`   | 3 | `16n+11` | `B` |
| 6 | `[1,2,3,3]` | 2 | `3`      | `A` |
| 7 | `[3,2,3,3]` | 1 | `1`      | `B` |

The excursion leaves the right context untouched, ends with the head on the
first right cell in the exit state, and moves the wall to phase `r+1 mod 8`
(one more `E`-block after phase 0). So the out-states form the periodic word
`B A B A B B A B`. Proofs: `sweepR`, `turn`, `sweepL_E`, `sweepL_iter`,
`sweepR_iter`, `phase0 … phase7`, `wall_excursion`, and `init_reaches_wall`
(310 steps from the blank tape to phase 0 with right context
`R0 = [4,4,4,4,4,1,4,4,3]`).

## 2. The cascade — `RequestProject/Cascade.lean`, `Levels.lean`

What remains is the half-tape `R` (cells ≥ 1). Each cell acts as a
finite-state transducer on the sequence of states in which the head arrives
from its left neighbour. `TM5.cell1 c f x` (content `c`, flag `f` = "right
neighbour non-blank", arrival state `x`) gives the new content, new flag and the
list of states sent to the right neighbour, or `none` for a halt:

| state | input `A` | input `B` |
|---|---|---|
| `(0,0)` | emit `BA`, → `(4,1)` | → `(2,0)` |
| `(2,·)` | → `(3,f)` | **HALT** |
| `(3,0)` | → `(4,0)` | emit `AB`, → `(4,1)` |
| `(3,1)` | → `(4,1)` | emit `AB`, → `(4,1)` |
| `(4,0)` | **HALT** | → `(1,0)` |
| `(4,1)` | emit `B`, → `(3,1)` | → `(1,1)` |
| `(1,0)` | emit `BAB`, → `(4,1)` | emit `A`, → `(4,1)` |
| `(1,1)` | emit `B`,  → `(4,1)` | emit `A`, → `(4,1)` |

* `TM5.lvl n x R` processes one arrival in the machine's own depth-first order
  (depth bound `n`); `TM5.sound_lvl` proves the machine really does this.
* `TM5.word N` = first `N` letters of the wall stream `B A B A B B A B …`.
* **`TM5.halts_iff`**: `Halts ↔ ∃ N n, seqO (lvl n) (word N) R0 = .halt`.
* `TM5.lev R0 (word N) p` (in `Levels.lean`): the input word of cell `p` in the
  level (breadth-first) picture; cells `p ≥ 9` start blank (`R0_drop_ge9`).

## 3. The halting criterion — `RequestProject/HaltCriterion.lean`

**`TM5.halts_of_haltsAt`**: if cell `p` halts on its level word
`lev R0 (word N) p` and the level word of some cell `q` is empty, then the
machine halts. (Via the commutation lemma `lvl_lev` between depth-first
processing and level words, and `seqO_ne_oof`: when the level words die out
at level `q`, depth `q` suffices.)

## 4. The executable engine — `HaltEngine.lean`

Plain Lean-core code, compiled to native code (`precompileModules = true`).
Letters are bits (`false` = `A`, `true` = `B`) packed eight to a byte; a cell
state is the byte `2·c + f`. Byte tables give, for (state, input byte), the new
state (or "halts inside this byte"), the number of emitted letters (≤ 24) and
the emitted letters, collected in a 64-bit accumulator.

1. *Periodic phase* (`pwUpTo q`). Starting from `x₀ = ∅`, `y₀ = BABABBAB`,
   for each level `p < q` it computes `x_{p+1}, y_{p+1}` and bookkeeping
   `a, b` such that the level word of cell `p+1` for the wall prefix of length
   `8·(a + b·k)` is `x_{p+1} y_{p+1}^k`, for every `k`.
2. *Streaming phase* (`streamPW`). Streams `x_q y_q^k` in chunks of `c` bytes
   through cells `q, …, q+M-1` and stops at the first halt, reporting it as
   *quiet* if that cell had emitted nothing yet.

`check 44 12 260 524288`: the level-44 word has prefix 744 002 430 letters and
period 47 618 515 171 letters (`a = 68 719 476 800`, `b = 4 398 046 511 104`);
the halt comes during the 10th period, in cell 200, quietly.

## 5. Soundness of the engine — `RequestProject/Halt/*.lean`

| file | content |
|---|---|
| `Halt/Basic.lean` | `cstep`/`crun` agree with `cell1`/`cellEnd`/`cellOut` (`stepOK`, `crun_spec`) |
| `Halt/Acc.lean` | bit streams `rd`, correctness of the output accumulator (`add_spec`) |
| `Halt/Feed.lean` | table lookups; `feed_spec`: feeding `rd inp i n` does what `cellEnd`/`cellOut` prescribe, and a quiet halt emits nothing |
| `Halt/Periodic.lean` | `pwUpTo_spec`: `lev R0 (word (8·(a + b·k))) q = X ++ Y^k` |
| `Halt/Stream.lean` | `pushChunk_spec`, `streamArr_spec`: pipeline states agree with the level words; a quiet halt at level `l` leaves level `l+1` empty |
| `Halt/Sound.lean` | **`halts_of_check`**: `0 < c → check q k M c = true → Halts`, via `halts_of_haltsAt` |
| `Halt/Verified.lean` | `check_ok` (by `native_decide`) and **`TM5.halts`** |

## 6. Files and dependency order

```
TM.lean → Wall.lean → Cascade.lean → Levels.lean → HaltCriterion.lean
HaltEngine.lean ─┐
                 └→ Halt/Basic → Acc → Feed → Periodic → Stream → Sound → Verified
```

Notes for a port to another proof assistant (e.g. Rocq): everything except
`Halt/Verified.lean` is ordinary definitions and proofs over `Nat`, `List`,
`Bool`, `UInt8`, `ByteArray`/`Array`; the only computational step is the single
closed evaluation `check 44 12 260 524288 = true`, which needs a fast native
evaluator (in Rocq, `native_compute`/`vm_compute` with machine integers and
arrays) and about 25 GB of memory with the byte-per-8-letters representation
used here.
