# Summary of changes for run 5cb82a4b-1cb6-4e8b-bcfc-35514ceba96a
**The GPT non-halting proof is correct.** Lean now checks the theorem `TM25.machine_never_halts : ¬ Halts` for `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`, i.e. the machine never halts from the blank tape. It builds with no `sorry`, no `native_decide`, no added axioms and no Mathlib. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

**Checking the proof.** I downloaded the package from the Drive link (`NONHALTING_PROOF.md` plus the Python/C checks) and formalized its whole argument:
- **Mixed-left lemma:** the capacity `K` of a left word, including buried `D` blocks, drops by exactly one per left excursion, and the saturation image is preserved. When `K` reaches 0 the next excursion reaches the left end and writes out that image.
- **Wide cascade:** the capacity updates `2E+1` / `2E−1` / `⌊(E−6)/2⌋` for `V` / `1` / `0`.
- **Right counter:** written as a single integer `M`, one right excursion is `M ↦ M+1`.
- **Exact reset-to-reset map:** `reset_return` proves the map as a theorem about the block system.
- **Debt arithmetic:** the safe-cascade lemma, the image bound, and the cost bound `≤ 8d+2`.
- **Invariant:** `inv_step` shows the reset invariant is closed.
- **Bootstrap:** 504 block steps reach reset 8, four exact returns reach the 50-letter seed at reset 12, and the seed satisfies the invariant.

Formalizing it turned up a few simplifications, none of them errors:
- The count clause `#V − #0 − #1 = 2` of the invariant is not needed; the debt bound alone forces a large enough height.
- The 3/8 contraction is more than needed; the proof only uses that the `1/256` debt bound is preserved.
- The finite Python/C checks are not needed beyond the bootstrap.

**Slimmed down for the Rocq translation.** The project now contains only what the proof uses: 7 files, about 1,400 lines, and a clean build takes a few seconds.
- **Removed:** all earlier exploratory Lean files (partial safety theorems, counter dynamics, the 10⁸-step `native_decide` check), the `sim/` scripts and the old `ANALYSIS.md`. They are still in the git history.
- **No Mathlib:** it has been dropped from `lakefile.toml` and the manifest, so the proof uses only core `Nat`, `Int`, `List` and `Option`.
- **No rationals:** every normalized-debt comparison `x/2^a ≤ x'/2^b` is stated with the denominators cleared, as `x·2^b ≤ x'·2^a`.
- **Tactics:** `omega`, `simp`, `decide`/`rfl`, plus `grind` for a few nonlinear `Nat` identities. These should map to `lia`, `nia`, `vm_compute` and `ring` in Rocq.

The files, in dependency order:
- `TM.lean`: the machine.
- `Blocks.lean`: the block system, each rule checked against the machine, and the reduction to "never reaches `D lB`".
- `MixedLeft.lean`: the mixed-left lemma and the cascade.
- `MixedReset.lean`: the right counter and the exact reset return.
- `MixedArith.lean`: the debt arithmetic.
- `MixedInv.lean`: the invariant and its preservation.
- `NonHalting.lean`: the bootstrap and the final theorem.

`PROOF.md` explains the proof, gives a file map, notes for the Rocq translation and the findings above. The Properties table has been updated to match.

# Summary of changes for run 5cb6b9c9-06c2-480a-b3fb-b8c40ffc1f51
I continued the study of `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---` and added a new, machine-checked layer to the existing development: `RequestProject/Protect.lean` (builds, no `sorry`, standard axioms only), written up as §20 of `ANALYSIS.md`.

**The idea.** The machine halts only when the left-going state-`B` head meets a parked digit `0 4`, and that head is born *only* when the wide head reaches the right end of the tape. So while any block is still sitting in the right word below the head, no halt is possible — and the two rules that read a `2 2` block (`> V → U >`, `w> V → U w>`) both plant a `U` immediately to the left of the head. A `2 2` block is therefore a **shield**.

**What is now proved.**
- `ahalts_release`: if the right word has `V rest` as a suffix (and the head is not the left-going `B` head), the machine cannot halt before reaching a configuration whose right word is exactly `rest` and whose left word begins with a `U`.
- `ahalts_guard`: the general form — a halting run must bring the head back to the top block of *every* suffix of the right word.
- `halts_imp_V_release`, `halts_imp_halt_config_V_free`: every `2 2` must be cleared before the machine can halt (at the halting configuration the right word is a block of `3 3`s), so a halting run has to park a fresh `0 4` on top of the `U` left by the last one.
- `deep_ones_any_left`, `wgt_nozero_safe`, `reset_nozero_safe`: a cascade whose remaining right word is made of `2 2`s and `1`-digits above the bottom junk is safe **with no hypothesis on the left word** — the earlier safety results needed a `U` next to the head.
- `deepest_one_safe`: the sharpest form — if the block directly above the bottom junk is a `1` digit, the machine cannot halt before returning to the cascade family, whatever the left word is and whatever sits above that digit. With the previously proved "a cascade arriving at the bottom on a `0` digit halts", the `1`-safe / `0`-dangerous dichotomy at the bottom of the tape is now a theorem on both sides.

**Why the strengthening matters in practice.** A new check (`sim/entercheck.py`) shows that at the moment each cascade enters the deep run of `1`s at the bottom (block steps 545, 1634, 15439, 137765) the left word begins with a parked digit `0 4`, not with a `U` — so the older safety theorem did not apply at those events, while the new ones do. I also added `sim/resetfull.py`, which dumps the full configuration at each reset.

**What remains open** is unchanged and is the arithmetic race of §§18–19: showing that the cascade always *does* find a `1` at the bottom, i.e. that the right counter is close enough to saturation whenever a cascade reaches the bottom of the tape. I did not resolve halting/non-halting; the previously recorded evidence (no halt within the first 10⁸ steps of the machine, and 2·10⁶ block steps cross-checked against the raw machine) stands. The whole project builds cleanly with no `sorry` and no added axioms, and the Properties table lists the new results.

# Summary of changes for run 9ca2881a-faf3-4416-9799-953449208920
Short answer: **yes — it is a condition on the counter values, but on the *leading* bits of the right counter, not on `R mod k`.** Everything below is now proved in `RequestProject/CounterValues.lean` (builds, no `sorry`) and written up as §19 of `ANALYSIS.md`.

**Which digit is the dangerous one.** The right counter is stored least-significant-digit next to the head, so a cascade walks from the *lowest* digit towards the *highest*; the digit it meets at the bottom of the tape is the most significant one. So, for a right counter of length `N = n+1` holding `R`: the deepest digit is a `1` exactly when `2^n ≤ R`, i.e. when the counter is in the **upper half** of its range (`rbits_getLast_C1_iff`), and a `0` exactly when `R < 2^n` (`rbits_getLast_C_of_lt`).

**Why not a congruence.** A condition `R mod k` would flip every `k` cycles, since a cycle is `R ↦ R+1`. The leading-bit condition is instead monotone over a whole stretch of cycles (`rbits_getLast_stable`): once the counter is in its upper half it stays there until it overflows, and only an overflow — which restores it at `0` — makes it dangerous again, for another `2^n` cycles. So the alternation has the period of the entire counter epoch `2^N`, invisible to any fixed modulus.

**The sharp form: distance to saturation, which is the conserved quantity.** The empirically observed safe bottom `2 3 … 2 3  2 1 $` with `j` deep ones is exactly the bound `δ = 2^N - 1 - R < 2^(N-j)` on the right counter's distance to saturation (`rbits_top_ones`). And `δ` is not a new quantity: a stretch of cycles lowers the two distances to saturation `2^λ-1-L` and `2^N-1-R` in lockstep, so at the reset that launches the next cascade the right counter's distance to saturation is precisely the **conserved difference** of the two (`slack_at_saturation`). Hence `bottom_ones_of_slack`: if that conserved difference is `< 2^(N-j)`, the cascade finds at least `j` ones at the bottom and (by the earlier deep-ones safety theorem) survives. In one line: the `0`/`1` alternative at the bottom is decided by the difference of the two counters, measured against the length of the right one.

**The data matches exactly** (new script `sim/slack.py`). Reading the right word's digits at each reset as a number: reset 8 `(N,R,δ) = (4,13,2)`, 9 `(6,61,2)`, 10 `(10,933,90)`, 11 `(15,31915,852)`, 12 `(24,16755023,22192)`, and the predicted run length `j = N - bitlength(δ)` gives `2, 4, 3, 5, 9` — exactly the exponents of the bottom shapes recorded earlier. At the early resets 1, 4, 5, 6 the deepest digit really is a `0` (the dangerous case); the machine survives them only because the cascade is cut short by the next reset before reaching the bottom.

This turns the remaining non-halting question into a concrete arithmetic target: show that from some point on the conserved slack difference at every reset stays below `2^(N-1)` — i.e. the right counter is always at least half full when a cascade starts (empirically it is within about `2^-9` of full by reset 12, and improving).

# Summary of changes for run 25785804-8faa-4249-9b45-8caf10d3fec8
Yes — that is exactly the right idea, and I have now done it. The whole project builds with no `sorry` and no added axioms.

**The counter dynamics, proved (`RequestProject/Counters.lean`).** Writing `lbits L λ` for the left word of length `λ` holding the number `L` (`0 1` = 0, `1 1` = 1, least significant digit next to the head) and `rbits R N` for the analogous right word (`1 3` = 0, `2 3` = 1):
- `arun_counter_cycle`: one sweep cycle is exactly `(L, R) ↦ (L+1, R+1)`, valid whenever `L+1 < 2^λ` and `R+1 < 2^N`, and — the important point — with an **arbitrary** left tail below the left counter and an **arbitrary** right tail below the right counter, so it applies in the presence of any leftover junk.
- `arun_counter_jump`: therefore `m` cycles are crossed by **one** application of one theorem, for every `m` with `L+m < 2^λ` and `R+m < 2^N`. Since `m` can be as large as `2^min(λ,N)`, this is the exponential jump you were pointing at.
- `counter_difference_invariant`: during such a stretch the two counters advance in lockstep, so `L − R` is conserved; `arun_counter_saturate`: taking `m` maximal crosses `min(2^λ−1−L, 2^N−1−R)` cycles and lands exactly on the first saturation — of the left counter (a reset) or of the right counter (an overflow). That is the race between the two counters in explicit arithmetic form.

**The accelerated simulator.** `sim/accel.py` and `sim/accel.c` implement precisely that jump on top of the exact block system, advancing `m = min(2^λ−1−L, 2^N−1−R)` cycles at once and charging the closed-form cost `2(F(L+m)−F(L)) + 2(F(R+m)−F(R)) + 2m` with `F(n) = n − popcount(n)`. `sim/accelcheck.py` re-runs each skipped stretch one block step at a time: the first 20 000 jumps agree with the exact simulation on both the configuration and the step count, and the accelerated run reproduces every reset and bottom-event step number of the plain simulator.

**Measured effect — and an interesting finding.** The realised speed-up is about **one order of magnitude**, not exponential: reaching reset 13 (block step 213 622 490 272) takes ≈75 s accelerated versus ≈12 min unaccelerated. There is one jump per ≈530 block steps, i.e. each jump only crosses ≈80 cycles, so the binding clean counter prefix is only about seven blocks long. The reason is exactly the leftover junk: the `2 2` blocks left in the right word and the `0 4` blocks left in the left word by the previous reset cascade sit a few blocks from the head and cut every counter prefix short. I also checked directly whether the configuration ever becomes a pure two-counter state between resets — it does for resets 2, 5, 7, but never after resets 8–12, so the junk is genuinely not cleaned up before the next reset. So the same leftover junk limits both the acceleration and the non-halting argument; a truly exponential accelerator would have to accelerate the crossing of those obstacles, which needs the same counter arithmetic the proof needs.

All of this is written up in §17 of `ANALYSIS.md` (with §16 covering the assessment of the proposed non-halting route, and §§12–15 the bottom-of-tape theory from the previous turn).


# Summary of changes for run 2b6e7b67-8233-41ab-b1f0-e2107fe3f8fa
I verified your analysis of `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---` formally in Lean, completed the rule set to a closed system, and reduced (non-)halting to one sharp remaining property — but I was not able to prove non-halting outright. Everything below is machine-checked, `sorry`-free, and uses only the standard axioms (plus the compiler-trust axioms for the one `native_decide` result). `ANALYSIS.md` is the written write-up; `sim/` holds the Python scripts used for exploration and for step-by-step cross-checking against the raw machine.

**1. Your analysis is correct.** All three heads and all fourteen blocks are as you describe, the machine does reach `L W < C R` after 21 steps (`TM25.start_21`), and all 25 rules hold, each for an *arbitrary* tape context (`RequestProject/Rules.lean`), with step counts recorded (e.g. `L < → L w>` 5, `w> C1 → < P V` 8, `w> V R2 → < C G G R` 16). Note `R1 = Q R` and `R2 = P Q R` as tape words, so three of the rules are instances of others; and in 2·10^6 block steps four rules (`> R1`, `w> G`, `w> P`, and, after once, `w> S`) never fire.

**2. The rule set is not closed, and I closed it.** The wide head has no rule against `R` or `R2`; both produce a *fourth* head, a left-going head in state `B` (`lB`): `w> R → lB G` (4 steps), `w> R2 → lB G G` (12). Adding `lB` with `U lB → < C`, `W lB → lB G`, plus `D lB` = halt and `L lB` = a provably infinite left-end loop, closes the system; `R1`, `R2` then become superfluous. Your rule `w> V R2 → < C G G R` is exactly a composite that passes through `lB`, and is safe there only because the wide head has just left a `U` behind it. The closed system (`TM25.astep`) is proved to simulate the machine faithfully (`TM25.astep_next`, `astep_halt`, `astep_loop`).

**3. Exact halting criterion.** `TM25.halts_iff_ahalt`: the machine halts **iff** the block system started at `L W < C R` ever reaches a configuration with head `lB` whose nearest left block is `D = 0 4`. And `TM25.no_halt_of_good`: the machine never halts provided every reachable configuration in which `w>` stands at the right end has a "good" left word (its first non-`W` block is a `U`, or there is none). That hypothesis is the entire remaining content of the problem, and I could not discharge it. The danger is genuine and local, not an artifact: from `> C1 P` the machine halts in 8 steps, from `w> S P` in 7 (`TM25.halt_trap_*`); the open question is only whether such configurations are reachable.

**4. Why the cleanup question is the crux.** The left word is a binary counter (`U`=0, `W`=1) and the right word a second one (`C`=0, `C1`=1) with the `D`s being digits temporarily parked on the left; `#{C,C1 in right} + #{D in left}` is preserved by everything except `w> C1 → < P V` (a reset) and is increased by the right-end rules. Empirically it stays ≥ 1 after the first 191 block steps, which is exactly what stops the wide head from running off the right end — making that inductive needs the relative growth rates of the two counters. `ANALYSIS.md` documents a near miss at block steps 151–181 where a leftover `Q` survives 30 block steps and is cleaned up by a reset just one carry before a halting pattern would have formed, which is precisely the race you anticipated.

**5. Finite evidence.** `TM25.not_halts_within`: the machine does not halt within its first 10^8 steps (the Lean model executed inside Lean); the closed block system was also run 2·10^6 block steps, every single step cross-checked against the raw machine, without reaching `D lB`.