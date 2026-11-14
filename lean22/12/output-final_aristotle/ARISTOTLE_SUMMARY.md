# Summary of changes for run 3a2b6e7f-0904-40cc-87ee-7626c968cce3
**Result: the machine `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` halts, and this is proved in Lean.** The theorem is `TM5.halts : TM5.Halts` in `RequestProject/Halt/Verified.lean`, where `Halts := ∃ n, run n init = none`. The module built successfully. `#print axioms TM5.halts` lists `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool` and `Lean.trustCompiler`. The project contains no `sorry`, `axiom` or `implemented_by`.

**How the proof works**
- `TM5.Eng.halts_of_check` is a soundness theorem for the fast, bit-packed check in `HaltEngine.lean`. It is fully proved with standard axioms only.
- That check is evaluated once: `HaltEngine.check 44 12 260 524288 = true`, by `native_decide`. The check computes the exact eventually periodic level word of cell 44 and streams it through cells 44–303. It finds a halt in cell 200, whose input begins `BAAA`, before that cell has emitted anything.
- Because of `native_decide`, the Lean compiler is part of the trusted base. Building that one module takes about 66 minutes on one core and about 25 GB of memory; all other modules build in minutes.
- The step count of about 7.3·10²⁸ is only an estimate from earlier C runs. The Lean statement says only that some finite run halts.

**Trimming for a Rocq port**
- **Removed modules:** `Simulation.lean`, `Bound.lean`, `Counting.lean` and `Main.lean`. The one definition from `Counting.lean` that the proof needs, `cellEnd`, moved to `Levels.lean`.
- **Removed declarations:** everything the proof of `TM5.halts` doesn't use, found by walking its dependencies. This takes out the non-halting reduction (`not_halts_of_no_ABBBB`, `exists_level_halt`), `halts_of_BAAA`, the counting identities, `sweepL` and `no_halt_in_wall`. A few `rfl` lemmas that simplification needs were kept.
- **Removed files:** the benchmark (`Bench.lean`, the `bench` executable) and all the exploration and C material in `sim/`, `accel/` and `counter/`. All of it is still in the git history (commit `163dddc`).
- **Remaining core** (about 2 300 lines, no Mathlib imports, only Lean core):
  - `TM.lean → Wall.lean → Cascade.lean → Levels.lean → HaltCriterion.lean`
  - `HaltEngine.lean`
  - `Halt/{Basic, Acc, Feed, Periodic, Stream, Sound, Verified}.lean`
- `lakefile.toml` still lists Mathlib as a dependency, but no file imports it.

`ANALYSIS.md` has been rewritten as a short guide to this core. It covers the wall analysis, the cell transducer, the halting criterion `halts_of_haltsAt`, the engine and a file-by-file soundness table, plus notes for porting. For Rocq, the one computational step needs a fast native evaluator with machine integers and arrays. I also updated the Properties table to match: rows for removed results were dropped, and the halting row is marked proved.

# Summary of changes for run d8335d2f-c781-4417-adb3-7c1f8f407d2c
**The machine appears to halt, after about 7.3·10²⁸ steps.** This comes from computation, not a Lean proof. Two separately written programs find the same halt: cell 199 (Lean numbering) receives the fatal prefix `ABBBB`, and cell 200 then halts on `BAAA`. So Conjecture C is false. The halt is at wall-stream position N ≈ 3.42·10¹⁴. I kept every run under ~15 minutes.

**Counting behaviour (done first, as you asked)**

Proved in Lean, in `RequestProject/Counting.lean` (no `sorry`, standard axioms):
- **Settled cells:** a settled cell (content 4, non-blank neighbour) is exactly the pair substitution σ: `AA→B, AB→BAB, BA→B, BB→A`, and it never halts.
- **Digit encoding:** a cell's content only records whether it has received an even or odd number of letters, plus the pending letter: 4 = even, 3 = odd ending in A, 1 = odd ending in B. So the counter state is just this list of digits, one per level.
- **Blank cells:** a blank cell is one of four fixed preludes (`A→BA`, `BAB→AB`, `BAABA→BAB`, `BAABB→A`) followed by a settled cell.
- **Period counting:** for a period `w` of odd length, the next period is σ applied to `ww`. It has `#A = #B(w)` (so A_{p+1} = B_p), `#B = #A(w) + D`, where `D` is the number of mixed pairs, and length `|w| + D`, which is again odd.

Numerical facts, not proved (`ANALYSIS.md` §6):
- These identities hold exactly for the real level periods at levels 3–27.
- In the periodic regime the counter works like a binary counter: one period of level p comes from 8·2^{p−2} wall states.
- Letter frequencies oscillate with damping towards f_B ≈ 0.631; each level is about λ ≈ 0.857 times as long as the one below.
- Levels are born in bursts of 2–7.
- No fixed digit weights make the counter additive, so it is not a positional number system.

**Acceleration (§7)**

Cost of reaching level L:

| method | cost |
|---|---|
| direct simulation | ~1.36^L |
| longitudinal streaming | ~1.167^L |
| exact periodic words up to about 0.22·L, then streaming | ~1.128^L |

The third method is the best I found; on 8 cores it reaches level 200 in about 10 minutes. I found nothing faster:
- the level words have positive entropy (exponential factor growth; `xz` gets about 0.67 bits per letter), which rules out a numeration-style digit encoding or compression of the level words;
- the front of level L depends on the whole prefix below it.

This was still enough to reach the halt.

**The halt (§8)**

- `accel/fast3.c`, started from the step-129 snapshot, halts at its level 201 (Lean cell 200).
- `counter/verify.c` is a from-scratch rewrite. It starts from the Lean-verified data `R0` and `word`, and its level words match Lean's `lev` on small prefixes. Its two runs give the same cell and the same position (`counter/verify43.out`, `counter/verify43_first.out`).
- The last level words, which you can check by hand: `BAB|BA BA BA…` → `ABBBB…` → `BAAA`.
- The real orbit behaves like a random one. In a random-input model the halting rate is about 0.6% per level. Near misses occur on about 5% of levels in both. The first 11 were saved, and the 12th was fatal.

**New Lean result**

`RequestProject/HaltCriterion.lean` proves the converse of the earlier non-halting reduction, which the last run had left unformalized. `TM5.halts_of_BAAA` says: if a blank cell's level word for `word N` begins with `BAAA` (or `BB`), and the cascade on `word N` dies out, then `TM5.Halts`. It rests on a level-commutation lemma `lvl_lev`.

The only missing piece is the finite fact "`BAAA` is a prefix of `lev R0 (word N) 200` and `lev R0 (word N) 201 = []`". It involves words of about 10¹¹–10¹² letters, far too large to check inside Lean, so it rests on the two computations.

`ANALYSIS.md` is updated with the new status, §4a (random model), §6 (counting), §7 (acceleration), §8 (the halt) and the file list, and the Properties table is updated to match. The whole project builds with no `sorry`.

# Summary of changes for run 3ec82de1-0938-48d1-97a0-7d1239f7fedb
The machine `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` is still unresolved. What changed this session: the longitudinal reduction was previously only derived and checked numerically. It is now proved in Lean (no `sorry`, only the standard axioms), so the halting question is formally reduced to one combinatorial statement about the counter.

**New in `RequestProject/Cascade.lean`**
- `cell1` is the single-cell transducer. Input: the cell's content, a flag saying whether its right neighbour is non-blank, and the state the head arrives in. Output: the new content, the new flag, and the states sent into the right neighbour, or a halt.
- `lvl` processes one arriving state on the right half-tape in the machine's own depth-first order. `sound_lvl` proves the machine actually does what `lvl` predicts.
- Combining this with the existing wall (bouncer) lemmas gives:
  - **`halts_iff`**: `Halts ↔ ∃ N n, seqO (lvl n) (word N) R0 = .halt`. Here `word N` is the first `N` states of the wall stream `BABABBAB…`, and `R0 = [4,4,4,4,4,1,4,4,3]` is the half-tape when the head first enters the wall (after 310 steps).
  - **`not_halts_of_cascade_ok`**: if every prefix of the wall stream is processed without halting, the machine never halts.

**New in `RequestProject/Levels.lean` (the level-word view)**
- `lev R0 (word N) p` is the input word of cell `p` (tape cell `p+1`), computed level by level.
- A commutation lemma turns a halt in the depth-first processing into a halt of some cell on its level word (**`exists_level_halt`**).
- Which cells can halt:
  - cells 0–7 never halt;
  - cell 8 halts only on an input starting with `AA`, which never happens (shown by a finite computation plus the fact that level words only grow by extension as `N` increases);
  - a blank cell (`p ≥ 9`) halts exactly on inputs starting with `BB` or `BAAA`;
  - a blank cell's output starts with `BAAA` only if its input starts with `ABBBB`.
- Result: **`not_halts_of_no_ABBBB`**: if no level word of a blank cell ever starts with `ABBBB`, the machine never halts. This is Conjecture C from `ANALYSIS.md`, which is now formally sufficient for non-halting.

**What remains open**
- Conjecture C itself.
- The converse (an `ABBBB` prefix forces a halt) is not formalized. It would also need every single arriving state to be processed in finitely many steps. That is not needed for a non-halting proof.
- Exploratory note, not verified: for that finiteness it would suffice that repeatedly applying the blank-cell transducer to any finite word eventually gives the empty word. An exhaustive check of all words up to length 16 found this true, but no simple length-based measure proves it.

**Other changes**
- `TM.lean` and `Wall.lean` were converted to Lean modules; their content is unchanged.
- `ANALYSIS.md` has a new §3a describing the formal reduction, plus the note above.
- Before proving anything, I checked the new definitions against direct simulation of the machine for 600 wall excursions; they agreed.

# Summary of changes for run 63febab0-67ce-4d3d-ab4d-295929f1665c
I studied `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` with longitudinal analysis. The machine is **not** resolved — it is a bouncer driving a chaotic counter — but the bouncer half is now completely eliminated with machine-checked proofs, and the remaining problem is reduced to one explicit combinatorial statement.

**Proved in Lean (builds, no `sorry`, no extra axioms).**
- `RequestProject/TM.lean`: the machine, zipper configurations, `step`, `run`, `init`, `Halts`, and run-composition lemmas.
- `RequestProject/Wall.lean`: the full bouncer ("wall") analysis. Two context-independent sweep lemmas (`sweepL`: 7 steps consume one wall block `[3,2,3,3,1]` and write `[4,3,4,4,1]`; `sweepR`: 9 steps write `[3,1,3,2,3]` and cross `[4,3,4,4,x]` for an arbitrary, unread `x`), their iterated versions by induction, and the eight phase excursions `phase0 … phase7`, packaged as `wall_excursion`: from each of the eight wall entry configurations `wcfg r n R` the machine runs exactly `wsteps r n` steps (`16n+17, 16n+5, 16n+7, 16n+9, 1, 16n+11, 3, 1`), never reads the right-hand context, and returns the head to the first context cell with the wall advanced one phase; eight excursions grow the wall by exactly one block `[1,3,2,3,3]`, with exit states following `B A B A B B A B`. Also `no_halt_in_wall` (no halt can occur at any time inside an excursion) and `init_reaches_wall` (the blank tape reaches the phase-0 wall configuration in exactly 310 steps).
- `RequestProject/Simulation.lean`: `no_halt_before_200M` — no halt within the first 2·10⁸ steps (via compiled evaluation, so the compiler is in the trusted base).

**Reduction and evidence (derived and checked numerically, not formally proved).** `ANALYSIS.md` documents the whole analysis: the wall table above; the crossing-sequence (longitudinal) view in which every tape cell acts as one fixed finite transducer, so the sequences of rightward arrival states form a cascade `u₁ → u₂ → …` starting from `u₁ = B(ABABBABB)^ω`; the resulting exact halting criterion — the machine halts **iff some level word of the cascade begins with `ABBBB`** — and the pair-substitution form `AA→B, AB→BAB, BA→B, BB→A` with the four prelude classes. Streaming the cascade for 10¹⁰ wall cycles (≈10²¹ machine steps, 143 levels) produced no halt. I also recorded the per-class danger conditions and the "near misses": class-`BAB` levels whose pair word starts with two letters of `{a,c}` (levels 25, 53, 71, 96 in the range examined) are each exactly one letter away from a halt and are saved every time by the same continuation `db`; that suggests the sharper statement (C′) in the document as a plausible route. The document also explains, with the failed experiments kept in `sim/`, why prefix/factor-language invariants cannot close here: the prefix dynamics needs geometrically growing lookahead, so it is not finite-state.

Supporting scripts are in `sim/` (simulators, reduced machine and its step-for-step comparison against the real machine, the phase decomposition used to build the Lean proofs, the transducer derivation and check, the exact eventually-periodic level words, the deep cascade run and the near-miss statistics).