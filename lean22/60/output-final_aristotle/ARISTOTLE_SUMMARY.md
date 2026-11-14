# Summary of changes for run ca4b5ec6-8315-4058-a61a-3896d92e3cfb
The machine `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` does not halt. `BB25.never_halts : ∀ n : Nat, ¬ Halted (run n)` builds with no `sorry`. `#print axioms` now lists only `propext` and `Quot.sound`; the old version also used `Classical.choice`. I rebuilt the original proof chain before changing anything, then trimmed the project down to that proof.

**What was removed**
- Every Lean file not needed by `never_halts`: 39 of 45 files, including the old macro-rule and token files, `Main.lean` and `Reduce.lean`.
- The `sim/` folder of Python scripts, `ANALYSIS.md` and `VERIFICATION.md`.
- The Mathlib dependency, taken out of `lakefile.toml` and `lake-manifest.json`. The project now depends on nothing but core Lean, and a clean `lake build` takes a few seconds.

**What is left**: six files in `RequestProject/`, about 1,200 lines.
- `Machine.lean` is the specification you have to trust: the transition table, `init`, `run` and `Halted`.
- `Rect.lean` defines the rectangles (`Visit`, `Cell`, `Rect`) and how they combine.
- `Fractal.lean` holds the induction over all ranks (`all_ranks`).
- `Oracle.lean` proves that every rectangle is actually executed by the machine (`rect_sound`).
- `Driver.lean` handles the right-hand part of the tape (`rule1`–`rule3`).
- `NonHalting.lean` puts it together and states `never_halts`.

**Changes made so the proof builds without Mathlib**
- `run` is now plain recursion (`run (n+1) = step (run n)`) instead of `step^[n] init`; the two are equivalent.
- A small `iter` function replaces Mathlib's iteration.
- `ring` became `omega`, `fin_cases` became case analysis on the symbol, and `set` became `obtain`.
- A few `simp` calls were replaced by direct lemma applications; this is what removed `Classical.choice`.
- Two unused lemmas were deleted.
- Every file uses `module`.

The mathematical argument is unchanged.

**For the Rocq port**
- The proof uses only core tactics: `omega` (which corresponds to `lia`), `simp` (mostly for regrouping lists), `rw`, `induction`/`cases` and `rfl`.
- `Visit`, `Cell` and `Rect` translate directly into Rocq `Inductive` definitions.
- One thing needs a decision: tapes are functions `Int → Sym`, and equalities between tapes are proved with function extensionality (in `wr_same`, `wr_wr`, `wr_comm`, `wl_wl` and one case of `step_left`). In Rocq you can either assume `FunctionalExtensionality` or compare tapes cell by cell instead.

`README.md` has the file map, a short informal proof and these notes. The Properties table now lists only the main theorem, the machine and run definitions, `Rect`, `all_ranks` and `rect_sound`. I left `ARISTOTLE_SUMMARY.md` untouched.

# Summary of changes for run b38c0222-67e6-45be-a4a3-dc861d3c3a07
The third session's proof is correct: I formalised it in Lean and `never_halts` is now proved. `BB25.never_halts : ∀ n, ¬ Halted (run n)` in `RequestProject/NonHalting.lean` builds with no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). It uses the original `Machine.lean` definitions, which I did not change. The full `lake build` succeeds.

I downloaded all three archives from the folder and checked each one. Details are in `VERIFICATION.md`.

**Session 3 (`bb25_nonhalting_project`, `PROOF.md`) — the claimed proof: confirmed.** I found no mathematical error: the word identities, exponent bookkeeping and parameter side conditions all check out as stated. The formalisation follows `PROOF.md` section by section:
- `LRect.lean`: the single-cell histories and rectangles, how they compose side by side and one after another, how they are cut, and the 7-row single-cell table.
- `LFractal.lean`: the "all-ones" lemmas (B), (C) and the odd wall (U), the base rank, the echo and the cut `P' = H b P`. It also has the combined induction on the reset and triangle rectangles, ending in `all_ranks`.
- `LDriver.lean`: the three right-hand driver rules, proved for every `m`.
- `LOracle.lean`: the informal "stack of suspended visits" safety argument, made rigorous. I compare the real machine with one that reads its return state from a list whenever the head steps just left of the window. `rect_sound` shows every rectangle is actually executed by that machine.
- `LNonHalting.lean`: the assembly. Before the head can reach cell `−w`, the two machines coincide, and the triangle rectangle for a large enough rank rules out a halt.

**Session 1 (`bb25_fractal_followup`).** Its Lean files had never been compiled. `GrowingReduce.lean` compiled as delivered. `ClosureObstruction.lean` needed two small fixes: a docstring was misplaced, and the finite run needed `decide +kernel`. With those, `macroClosed_orbit_impossible` is proved. This confirms that the earlier sufficient condition in `Reduce.lean` (a `MacroClosed` family containing `orbitWord`) can never be satisfied. It does not conflict with `never_halts`, which is proved by a different route.

**Session 2 (`bb25_longitudinal_certificate`).** The SHA-256 checksums match and `check_certificate.py` passes. As the session itself says, this is finite Python evidence, not a proof. The final proof doesn't depend on it.

New files: `RequestProject/LRect.lean`, `LFractal.lean`, `LOracle.lean`, `LDriver.lean`, `LNonHalting.lean`, and the two session-1 files. I also changed `RequestProject/NonHalting.lean`: `never_halts` is now proved and its docstrings are updated. `ARISTOTLE_SUMMARY.md` is unchanged.

# Summary of changes for run 6e7d2c28-8290-4319-9f0a-2dca3b6b727b
I first restored and verified the state of the earlier work on `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`: nothing was lost — the whole development builds cleanly, uses only the standard axioms, and the only `sorry` in the project is still the open target `never_halts` in `RequestProject/NonHalting.lean` (this machine is unsolved). The written record in `ANALYSIS.md` was already current through Part XI, so I continued from there and added four new pieces, all machine-checked and all documented in a new Part XII (§51–§56).

**Non-halting reduced to a statement about words** (`RequestProject/Reduce.lean`). Every left-end macro rule of the project has the same shape — in state `B` on the leftmost non-blank cell with three blank cells to its left, the machine returns to state `B` three cells further left, the tape word `W` having become a word `W'` of length `|W|+3` — so the right edge of the word never moves. I formalised a synchronisation moment (`AtWord`), the property of a family of tape words being closed under one such step (`MacroClosed`), and proved `never_halts_of_closed`: **if any family of tape words is closed under one macro step and contains a word the machine actually reaches, the machine never halts.** It does reach one: `orbit_atWord` shows that after exactly `3099` steps the tape carries `U(2,1) U(4,1) u u U(2,2) V(1) u U(1,18) u^12` with blanks elsewhere, so `never_halts_of_closed_orbit` turns the remaining gap into a purely combinatorial condition on words.

**The fractal mechanism, for a whole family and every depth at once.** `MacroClosed.in_zero_run` proves, by induction, that a run of `3j` extra blank cells hosts exactly `j` macro steps of the family's own computation, with the head provably never leaving the run. Since a rightward sweep turns `U(a,1) = 0 4^a 2` into `1 0^a 3`, this is the inductive engine behind the self-similarity of the space-time diagram.

**The last missing local rule** (`RequestProject/BlankRight.lean`). The one row of the carry table with no parametric rule was the carry running off the blank right end. Both cases are now proved for every length `N` of the intervening run of tokens `u`: `rule_P3_blank` (`0 0 0 · U(2,2) V(1) · u^(N+1) · 0 0 0 → U(2,1) U(4,1) · u^(N+2) · 0` in exactly `59 + 12N` steps) and `rule_P1_blank` (`47 + 12N` steps). Each bounce off the blank converts two blank cells into a fresh token `u`. These rules matter not only at the start of the computation but inside every fractal copy, where a swept `4`-run plays the role of blank tape.

**Two further instances of the unfolding, and a halting configuration.** `unfold_U13` and `unfold_U16` (`RequestProject/Unfold.lean`) extend the two smallest instances of the fractal identity: a `4`-run of length `13 = 3·4+1` hosts four macro steps of the machine's own computation and comes out as `u U(1,2) u` after `561` steps; length `16` hosts five and comes out as `u U(1,2) V(1) u` after `595`. Finally `halt_of_narrow_gap` (`RequestProject/NarrowGap.lean`) shows that from `0 0 1 0 0` with the head in state `B` on the last cell the machine **halts** in `13` steps — that is a left-end step attempted with one spare blank cell instead of three, so the `0 0 0` in every window rule is load-bearing and any proof must control the arithmetic of the run lengths.

New exploratory scripts (`sim/blank.py`, `sim/unfold.py`) are described in `sim/README.md` and, as throughout, are explicitly marked as not machine-checked. `ARISTOTLE_SUMMARY.md` was left untouched; all work is committed.

# Summary of changes for run 8a5e1e55-9067-417d-97a0-3c1a38f98bab
I continued the longitudinal/fractal analysis of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`. The target `never_halts` is still open — it remains the only `sorry` in the project, since this machine is unsolved — but this session added three machine-checked results of a new kind and, I think just as usefully, measured exactly what is still missing.

**Arbitrary tape *shapes*, not just arbitrary run lengths.** Every macro rule in the project so far was parametric in the *lengths* of runs (`u^r`, a run of `2`s of length `2m+2`). The two new rules are parametric in the *shape* of the tape word:
- `rule_P3_flat` (`RequestProject/Flat.lean`): `0 0 0 · U(2,2) V(1) u · u^r · U(2,1) · U(k₁,1) ⋯ U(kₙ,1) · U(1,2m+2) 0 → U(2,1) U(4,1) · u^r · U(1,4) · U(1,k₁) ⋯ U(1,kₙ) · U(1,2m+4) 0` in exactly `91 + 12r + 10m + ∑(4kᵢ+2)` steps, for every `r`, `m`, `n` and every `k₁,…,kₙ ∈ {1,2}` in any order.
- `rule_P1_flat` (`RequestProject/FlatP1.lean`): the `P1` counterpart, with the same step count.

Taking all `kᵢ = 1` recovers last session's `rule_P3_U21`. The new ingredient is `sweepL_blocks_small`, the leftward counterpart of `sweepR_blocks` (a sequence of blocks `1 0^{kᵢ} 3` with `kᵢ ≤ 2` is crossed right-to-left in one pass in `∑ 3kᵢ` steps — the bound `kᵢ ≤ 2` is exactly the condition that the head is not reflected), plus two re-reading identities which explain why a crossed block `U(k,1)` comes back out as `U(1,k)`. Both rules are `Win` rules, so each also certifies that the head never leaves the stated window and that the machine does not halt over the steps it covers.

**A census of the macro steps that actually occur.** Classifying every `B`-event of the real orbit by the only data a macro rule needs (phase; exponents of the blocks the rightward pass crosses; the token that absorbs the carry; the token after it) gives just twenty-four classes over the first million steps. The crossed exponents are always `1`, except for a single `2` — precisely the generality the new rules provide — and, three times in a million steps, a `10`, which is the fractal recursion. So the whole remaining gap, apart from that recursion, is the *absorbing token and its neighbour*: a token `U(2,b)` instead of `U(1,b)`, and a `V` instead of a `U` right after it. Counting up, the proved rules now account for 46 % of all macro steps; the two rows I state precisely would take that to about two thirds.

**The first of those two rows, started.** Its three new pieces are proved in `RequestProject/TurnU2.lean`: `turn_U2` (`1 0 0 3 · 2^(2M+1) · 0 → 1 1 3 · 2^(2M+2) · 0` in exactly `10M+15` steps, for every `M`) — the turn-around when the marker the sweep leaves is `1 0 0 3`, whose extra `0` stops the return sweep one cell early so the head turns around *inside* the region instead of leaving it, which is why such a token passes a carry on instead of swallowing it — together with `retU2` and `turn_U2_second`. Getting these needed generalisations of the ping-pong chain and the return sweep to an arbitrary symbol left of the marker (`pingpong_chain0`, `onesBack_gen`); what is left for the complete row is only the bookkeeping that chains them with the sweeps.

Everything is sorry-free and uses only the standard axioms; `lake build` is clean. The analysis is written up in `ANALYSIS.md`, Part VI (the two-pass anatomy in the form that generalises, the new rules, the census, and the two next rows with their step counts — the latter checked by simulation and explicitly marked as not machine-checked). The new exploratory scripts `sim/flat.py`, `sim/shapes.py`, `sim/probe2.py` and `sim/winck2.py` are described in `sim/README.md`. `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 1fcbc2e5-5ca8-4554-9404-1f7375200860
I continued the longitudinal/fractal analysis of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`. The target theorem `never_halts` is still open — it remains the only `sorry` in the project, as this machine is unsolved — but this session both *explained* last session's fractal identity and added four new machine-checked parametric theorems.

**The main finding: why the diagram is self-similar.** Last session the fractal identity ("a run of `3j+1` fours unfolds into a copy of the tape at the `j`-th synchronisation event") was an empirical observation. It now has a mechanism, which is simply the conjunction of two facts: (i) a rightward sweep rewrites the token `U(a,1) = 0 4^a 2` as `1 0^a 3`, so a `4`-run becomes a run of `a` **zeros** — a finite piece of tape the machine cannot distinguish from the blank tape at its left end; and (ii) every left-end macro rule in the development is a window rule whose window begins with exactly three cells `0 0 0` and whose head provably never leaves the window, so each rule applies verbatim inside such a run of zeros, consuming three of its cells. Hence a run of `3j+1` fours hosts exactly `j` macro steps of the machine's own computation. Simulation confirms this directly: probing an isolated `U(22,1)` and recording the head's leftmost visits inside the former `4`-run reproduces, in order, the first seven tape words of the machine's own run. The same holds on the right, where an infinite run of `U(1,1)` tokens plays the role of blank tape. Both halves of the mechanism are proved in `RequestProject/Fractal.lean` (`four_run_to_zero_run`, `Win.in_zero_run`, and three instances for the phase rules).

**New machine-checked theorems** (all sorry-free, standard axioms only, each also certifying that the head stays in its window and that the machine does not halt over the steps it covers):
- `RequestProject/CarryP1.lean` — `rule_P1_gen`: the `P1` left-end rule with an arbitrary run of `r+1` tokens `u = U(1,1)` before the absorbing token, in exactly `91 + 12r + 20m` steps. This is the missing counterpart of last session's `rule_P3_gen`.
- `RequestProject/CarryU21.lean` — `rule_P3_U21`: the next row of the carry table, the carry crossing a token `U(2,1)` (which becomes `U(1,4)`, with two of the four `2`s travelling on), with arbitrary runs of `u` on *both* sides, in exactly `91 + 12r + 6s + 10m` steps. This is the first proved rule in which the carry is not absorbed by the token it meets.
- `RequestProject/CarryU21.lean` — `three_phase_cycle`: one full turn `P1 → P2 → P3 → P1`, obtained purely by composing the three window rules, in exactly `233 + 18r + 30m` steps.

**Analysis** is written up in `ANALYSIS.md`, Part V: the two "virtual blank tapes", the carry table refined to an *arbitrary* carry `k` (in which the transducer conserves cells and the carry is the number of cells still to be delivered), a table of the new rules, and a sharpened statement of the remaining gap — the rest of the carry table plus the strong induction on `j` that §24 now shows is the right shape. The new exploratory scripts (`sim/self2.py`, `sim/carrytab.py`, `sim/p1gen.py`) are described in `sim/README.md` and, as before, are explicitly marked as not machine-checked. `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 6e5b79bc-37ec-471e-a4fd-e1a29ef46d7b
I picked up the longitudinal/fractal analysis of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB` where the previous session stopped. The target theorem `never_halts` is still open (it remains the only `sorry` in the project — this machine is unsolved), but the session produced both a substantial new batch of machine-checked macro rules and, I think more importantly, a precise statement of the self-similarity that drives the space-time diagram.

**The main finding: the fractal identity.** Let `W_0, W_1, W_2, …` be the tape words, in the token alphabet `U(a,b) = 0 4^a 2^b`, `V(c) = 4 3 2^c`, at the successive synchronisation moments (the head reaching a new leftmost cell in state `B`), and write `core(W)` for `W` with its first token and its trailing run of `u = U(1,1)` removed. Then a token `U(3j+1, 1)`, when the "carry" of four `2`s reaches it, unfolds into `u u · core(W_j)` or `u U(1,2) · core(W_j)` according to which of the three phases `W_j` is in. In other words **a run of `3j+1` fours is a compressed copy of the tape at the `j`-th synchronisation moment**. This explains at one stroke why the observed `4`-run lengths are exactly `3^k + 1`, why `U(28,1)` unfolds into `u u U(4,1) U(1,4) V(5)`, and why the machine is not a bouncer. It is checked by simulation for `j = 0, …, 25` (runs up to length 76), and its two smallest instances are proved outright in Lean.

**New Lean content (all proved, no `sorry`, standard axioms only).**
- `RequestProject/LeftRules.lean` gains `pingpong_chain`: the marker `1 0 3` crosses `2n` cells of a run of `2`s in exactly `8n` steps, for every `n`.
- `RequestProject/Cycle.lean` (new): `onesBack`; `cross_back` — the complete round trip of the head through a run of `2n+1` twos, which comes back leaving `2n+4` twos in exactly `10n+14` steps, for every `n`; and the two remaining left-end macro rules, `rule_P1` (`79+20m` steps) and `rule_P3` (`91+20m` steps), each assembled from five pieces.
- `RequestProject/Carry.lean` (new): `rule_P3_gen`, the `P3` rule with an **arbitrary** run of `r` intervening `u` tokens, in exactly `91 + 12r + 20m` steps — proved by exhibiting the computation as nine macro steps in which the head crosses the run of `u`s four times and the run of `2`s twice; and `unfold_U4`, `unfold_U10`, the two smallest instances of the fractal unfolding.

Every one of these is stated in the `Win` window-rule format, so each also certifies that the head never leaves the stated window (the rest of the tape is arbitrary and untouched) and that the machine does not halt at any of the steps it covers.

**Analysis written up** in `ANALYSIS.md`, Part IV: the five ingredients of one macro step (rightward block sweep, turn-around inside the run of `2`s, leftward return, reflection at a `4`-run of length ≥ 3, repeat); the complete carry table, probed in isolation, including exactly which token contexts would make the machine halt; the fractal identity; and a sharpened statement of what a complete proof still needs — a parametric version of the reflection rule plus the induction on `j` that the identity suggests. The exploratory scripts behind all of this are in `sim/` (`probe.py`, `fractal.py`, `winchk.py`, `be*.py`, …) and are described in `sim/README.md`; as before they are explicitly marked as not machine-checked. I also fixed the broken file that the previous session left mid-edit, and cleaned up the linter warnings it had accumulated.

# Summary of changes for run 00790a88-b7b8-495b-a43a-d1317198351d
I continued the work on `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`. The target theorem `never_halts` is still open (it remains the only `sorry` in the project), but the formal development is now substantially stronger and the analysis has a much cleaner shape.

**A better coordinate system.** Looking at which transitions move the head right, a rightward excursion in state `A` can only read words of the form `0 4^{j₁} 2 · 0 4^{j₂} 2 · …`, and simulation confirms that at the start of every long rightward excursion the tape really is such a word. In this description the two kinds of "repeated region" found earlier are one family: the bulk is the blocks with `j = 1`, the walls are the blocks with `j ≥ 2`, and the fractal is the evolution of the exponent sequence.

**New Lean files (all proved, no `sorry`).**
- `RequestProject/Words.lean`: tape words (`Seg`) and three composable macro-rule predicates — `SweepR`, `SweepL` and `Bounce` (a reflection: the head enters a region at its right end moving left and comes back out on the right) — with their composition lemmas.
- `RequestProject/Chains.lean`: a one-cell rule for each transition, iteration of rules, the run ("chain") rules for a run of `4`s, `1`s and `3`s of arbitrary length, the block rule `0 4^j 2 → 1 0^j 3` for arbitrary `j`, and `sweepR_blocks`: a concatenation of blocks with *arbitrary, unrelated* exponents is crossed rightwards in one pass of exactly `∑ (jᵢ + 2)` steps. This strictly generalises the previous fixed-size bulk sweeps.
- `RequestProject/Bounces.lean`: the six bulk sweeps re-derived in the new framework, the complete case analysis of a leftward pass over a block (`j = 0, 1, 2` are crossed; `j ≥ 3` reflects), the wall turn-around `turn_wall`, and `bounce_wall_bulk` — one complete triangle of the space-time diagram, for every number `k` of bulk blocks, in exactly `6k + 9` steps.
- `RequestProject/Excursion.lean`: every macro rule certifies non-halting over its whole duration (the halting state is absorbing), and `left_end_sweep`: from the configuration the machine is in each time the head reaches a new leftmost cell, it writes `1 3` at the left end and crosses an arbitrary block sequence in `5 + ∑ (jᵢ + 2)` steps without halting.
- `RequestProject/NonHalting.lean` also gains `never_halts_of_unbounded`, which reduces the goal to exhibiting arbitrarily late non-halted configurations.

**Analysis (documented in `ANALYSIS.md`, Part II; exploratory scripts in `sim/`, explicitly marked as not machine-checked).** A coverage experiment shows the proved macro rules cover 98.3 % of the first 3 000 000 steps, and the set of local situations where no rule applies stays constant at 75 from 50 000 steps on — evidence that the rule catalogue is complete. A saturation search shows that no invariant built from purely local constraints (allowed tape words of length `w` up to 6, plus allowed head windows) can work, so the argument must use the sequence of regions. Finally, the crossing sequences — the longitudinal picture proper — are remarkably clean: every column `i ≥ 1` has crossing sequence exactly `B (AAABBB)^ω`, and every column `i ≤ 0` has a *finite* transient followed by the same periodic tail (the measured transient lengths are unchanged from 500 000 to 8 000 000 steps). The periodic tail is the period-6 cell cycle in which a `4` is always read in state `B`, which is why it cannot halt; the remaining gap is exactly the behaviour of the finite transients, i.e. a closed description of which block sequences occur.

# Summary of changes for run be1ba7d6-afc0-4df4-a548-b311c165e9d0
I did not manage to prove non-halting of `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`; that statement remains open in the project. What I did produce is a Lean formalisation of the machine together with a substantial, fully machine-checked part of the longitudinal analysis you suggested, plus a written record of the structure I found.

**Formalisation** (`RequestProject/Machine.lean`): the machine as a step function on configurations (state, head position in `ℤ`, tape `ℤ → Fin 5`), with the halting transition (`A` reading `4`) modelled by an absorbing state, the blank-tape run `run n`, and the predicate `Halted`. A kernel-checked 500-step evaluation confirms the transcription agrees with a reference simulation (state `B`, head at `-6` after 500 steps), which also gives `not_halted_le_500`.

**Longitudinal structure found.** Reading the space-time diagram column by column, every tape cell settles into the same period-6 visit pattern `A:0→1, A:1→2, B:2→3, A:3→4, B:4→0, B:0→0`, i.e. the value cycle `0→1→2→3→4→0→0`. Comparing neighbouring columns, the tape splits into two kinds of repeated region: a *bulk*, where the phase drops by 2 per cell so the contents are 3-periodic in space, and *walls*, where the phase is constant (long runs of `2`).

**Proved, for arbitrary region sizes** (no `sorry`, only the standard axioms):
- The six bulk sweep rules `042→103→204→310→420→031→042` (`sweep_042`, …, `sweep_031`): a bulk of `k` blocks is crossed in exactly `3k` steps without changing state, and nothing outside the region is touched.
- The three right-end turn-arounds and the resulting bounce theorems (`bounce_042`, `bounce_204`, `bounce_420`), which together show that one full 6-sweep cycle extends the bulk by exactly one fresh 3-cell block `042` on the right.
- The wall rules: the period-8 ping-pong by which a marker `0 3` travels two cells at a time through a run of `2`s (`wall_step`, `wall_chain`), and the complete odd-length case `wall_odd`: a wall of `2n+1` cells grows to `2n+4` cells in exactly `10n+14` steps while the head turns around — this is the mechanism by which a wall eats the bulk and produces the nested triangles in the diagram.
- The blank left-end growth rule `left_blank_extend` (5 steps, writes `1 3` and shifts right).

**What remains.** The irregular left end, where new walls are created, is not yet closed. `ANALYSIS.md` documents the empirical findings there (three-phase prefix shapes recurring with period 3 in the left-extension events, a 3-adic/odometer-like hierarchy in the gap sequence with stretches of length 27 recurring verbatim, and the way earlier tape words reappear as factors of later ones); these observations come from simulation and are explicitly marked as not verified. The target theorem `never_halts : ∀ n, ¬ Halted (run n)` is stated honestly in `RequestProject/NonHalting.lean` with its proof left as `sorry` — that is the only `sorry` in the project.