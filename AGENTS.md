Freebuff compacts context automatically, and also remember this:
when making a fgh level machine, it must halt in the specified ordinal under the function f\_ordinal(n) steps, correctly verified in rocq with the rules.

## BB(3,3) holdout #758 (`1RB2LC1RC_2LC---2RB_2LA0LB0RA`) — binding rules (2026-11-16)

1. Any claimed proof of halting or non-halting must be paired with **both** a Lean file and a Rocq file, both compiled and run.
2. Do not do a little work and then answer "I can't prove it". The problem is not to be declared impossible; keep working across turns.
3. If the machine halts, it is the BB(3,3) champion.
4. On a completed proof that it halts, say exactly: **IT HALTED!!!!!!!!!!!!**
5. On a completed proof that it does not halt, say exactly: **welp, there goes the last champion candidate. BB(3,3) is likely equal to the current champion from 2007 or whatyever.**
6. These rules govern all work on this machine in this repository.

## Status 2026-11-16 (third session)

* (R) `|L(3m+r)-L(m)| <= 183 ln m` survived random 10,000-bit tests, scaling of the known worst values, and a 1024-bit hill climb.  Max observed ratio is 6.39; no violation.
* The shadowing proof target is **false**: `m = 3,814,756,888` has `L(m) = 26` and `L(3m+1) = 167` (defect 141), so the defect can equal an entire chain length.  (R) is a global chain-length bound in disguise, not a local perturbation statement.
* The conditional quadratic bound is formalized and compiled in `cryptids_a6/BusyBeaver/BB33/M_758_Quadratic.lean` (Lean, no `sorryAx`) and `rocq/BB33_758_Quadratic.v` (Rocq, closed under the global context).  Its hypothesis (R) is not proved.
* No halting or non-halting proof exists yet.  Do not use either required phrase.

## Status 2026-11-16 (fourth session)

* New exact invariant: `Q(a,c)=a/2+c` increases by a fixed positive weight on every rule, and `D(c)=F(c)-c = 3/2 + (sum of rule weights)`.  `D` is a weighted rule count, not an ordinary chain length.
* New target: a **constant** base-2 increment defect `|D(2m+r)-D(m)| <= K`.  Exhaustive scans give max about 444 at `10^9` (base 2) and 412 at `10^9` (base 3), far below `K=80,000`.
* Base-2 pair identity: `A(1,2m+1) -> A(5,2m+1)` and `A(1,2m) -> A(11,2m+1)`.  Fixed perturbation 6 at the same `c`; endpoint difference stays about 200 even when chain lengths differ wildly.
* Conditional reduction compiled: `cryptids_a6/BusyBeaver/BB33/M_758_Increment.lean` and `rocq/BB33_758_Increment.v`.  If the constant base-2 defect is at most `K`, then `D(c) <= D(1)+K*t` for all `c < 2^t`; at `K=80,000`, `t=463`, this is `< 37,040,008`, inside the wall window.  Hypothesis (S2) is not proved.
* Still no halting/non-halting proof.  Do not use either required phrase.

## Status 2026-11-16 (fifth session)

* Formalized the exact `Q(a,c)=a+2c` invariant in `cryptids_a6/BusyBeaver/BB33/M_758_QInvariant.lean` and `rocq/BB33_758_QInvariant.v`: rule weights `j:4 i:8 a:3 b:5 c:9 e:8 h:5`, plus `Q_apply`, `Q_cross`, `Q_run_cross`, and the base-2 start identities.
* Proved the **same-word** fixed-perturbation endpoint lemma: if the chains from `(5,c)` and `(11,c)` use the same rule word, then `F(11,c)=F(5,c)+3`.  Both files compile; Lean has no `sorryAx`, Rocq is closed under the global context.
* Formalized the pair-plus-scale reduction: pair defect `Kp` plus scale defect `Ks` gives the constant-defect bound `Kp+Ks`.
* The unconditional pair bound for differing words is still open.  Measured max `|F(11,c)-F(5,c)|` is 227 at `2e5`, 377 at `1e8`, 391 at `1e9`, 421 at `1e10`; it grows slowly (log-like).  The `Q` bound is `3+(9/2)*window`; the missing lemma is a bound on the divergence window (empirically about 4.4 bits).
* No halting/non-halting proof.  Do not use either required phrase.

## Status 2026-11-16 (fifth session, continued)

* Added the **length-based** endpoint bound to both formal files: `Q_run_le`/`Q_run_ge` give `Q p <= Q(run w p) <= Q p + 9*length w`, hence for even endpoints `2*F(5,c) <= 2*F(11,c)+9*L5` and `2*F(11,c) <= 2*F(5,c)+6+9*L11`.  This covers **all** word pairs, including non-synchronizing ones.
* Consequence: a universal chain-length bound `L(c) <= 17,777` at 463 bits would give the pair defect `K=80,000`; a cruder `L(c) <= 86,000` would already give `D(c) <= 774,001.5`, inside the 38.6M wall directly.  Empirical 463-bit chain lengths are about 300 (max 356 in `chain_scale.py`).
* The constant-defect pair half is therefore reduced to a chain-length bound, not a constant endpoint-difference bound.  The remaining open lemma is a universal `L(c)` bound for the 10-rule map (route 1: base-3 digit consumption, O((log c)^2)); the scale half `D(2m+1)` vs `D(m)` is still needed for the `K=80,000` form.
* No halting/non-halting proof.  Do not use either required phrase.

## Status 2026-11-16 (sixth session)

* Aligned `Valid` in `M_758_QInvariant.lean` with `BB33_758_QInvariant.v`: the `a`, `b`, `c` branches now carry exactly the same `mod 4` and `mod 2` components in both files, so the paired theorems have identical hypotheses.  Both files recompile (`LEAN_Q=0`, `ROCQ_Q=0`; Lean no `sorryAx`, Rocq all `Closed under the global context`).
* Chain-length attack: the dominant prefix is a pure `j` run.  From `A(1,c)`, after `k` valid `j` steps, `a_k = 2*3^k - 1` and `c_k = c - 3^k + 1 + 2*k`; the run stops at the first such `k`; the previous step gives `3^k < c+2k`, so at 463 bits `k <= 292`.
* Empirically every 463-bit segment is this one `j` run plus a short tail: 200 samples had lengths 291-320; 100,000-bit samples had length `0.6309*bits + 13..29`.  The remaining target is a uniform tail bound, not a second long run.
* Weakened sufficient target: `L(c) <= 50*log_3 c` (about 14,600 at 463 bits), which the length-based endpoint theorem turns into `K <= 65,700 < 80,000`.  This is not yet proved; no halting or non-halting claim.

## Status 2026-11-17 (seventh session)

* Formalized the pure `j`-run prefix in **both** files: `jIter`, `JValid`, `jIter_formula` (`jIter k (1,c) = (2*3^k-1, c-(3^k-1-2*k))`), `JValid_prefix`, `JValid_last`, and `j_run_length_le_292`.
* Formalized the precise remaining tail statement `TailBounded B` in both files, plus `length_le_17000_of_tail` and the concrete corollary `length_le_17000_of_tail_16708` (`TailBounded 16708 -> k + length w <= 17000`).
* Lean `M_758_QInvariant.lean` compiles; Rocq `BB33_758_QInvariant.v` compiles with all `Print Assumptions` reporting `Closed under the global context`.  The tail bound `TailBounded 16708` itself is **not proved**; it remains the open chain-length lemma.  No halting or non-halting claim.

## Status 2026-11-17 (post-`j` halving-time budget session)

* Both paired modules now carry the **same phase constant 791** for the first `L` phase: `cryptids_a6/BusyBeaver/BB33/M_758_TBudget.lean` and `rocq/BB33_758_TBudget.v`. Lean: exit 0, axioms only `propext`/`Quot.sound`. Rocq: exit 0 in 9 s, all 27 `Print Assumptions` report "Closed under the global context".
* The Rocq sharp constant needed a new route. The 1255-bit base comparison `2^792*(3^292+1) < 3^792` is discharged by `vm_compute` in `Z`, and the induction `2^n*(3^292+1) < 3^n` for `n >= 792` is carried out at the **`Z`** level (`three_pow_gt_Z`), because the same induction in `nat` overflows the checker. The bridge back to `nat` applies one `Nat2Z.inj_*` rewrite per occurrence: a single `rewrite Nat2Z.inj_pow` fires on only one instantiation, and `rewrite !` loops, so the repetitions are written out one per line.
* `Budget B` is **equivalent** to a length bound: every surviving step raises `Q = a + 2c` by at least 3, so `Budget B` <=> every post-`j` run has `T <= B/3`, and `Budget 30000` <=> `T <= 10000`. Hence no potential function can prove `Budget` (its increment is strictly positive) and the budget is exactly the alternation bound.
* Measurements (`t758_dyn.py`, `t758_mag.py`, `t758_s.py`, `t758_s2.py`): the extremal run `(k=289, c=2047)` has `T = 844`, 26 phases, rule counts `b:443 c:380 j:20 h:1`, `sum dQ = 5715`, while `Q(0) ~ 1.5e138`; `Q` is effectively conserved. With `Q` fixed, `s = 2c/Q` obeys `s -> 1.5*s` in the L region and `s -> 3*s - 2` in the J region: a two-branch expanding (cookie-cutter) map on `(0,1)`, so no linear or monotone potential exists (checked by solving for the coefficients).
* Termination rule: every `a`/`b`/`c` L-step flips the parity of `a`; the `i`/`j` J-steps preserve `a` odd; `h` fires at the first J-region entry with `a` even. Survival therefore requires every L-phase length to be even, i.e. the phase count is a geometric waiting time.
* Still open: an unconditional universal `T <= 10000`. `postJ_survives_le_10000` in both modules is conditional on `Budget 30000`, which is measured true with about 5x slack (`sum dQ = 5715`) but has no proof. The counting heuristic `0.585*n_L + 1.585*n_J <~ 1.585*k` gives `T <~ 2.71*k <= 791`; the measured max over `k <= 292` is about 844, so the target has slack but needs a pointwise argument over ~26 phases rather than a counting one.
* No halting/non-halting proof.  Do not use either required phrase.

## Status 2026-11-17 (second) — `Budget B` is false; the stopping rule was wrong

* **The residual of `M_758_TBudget` is refutable, not open.** `Budget B` quantifies over `run n (2*3^k - 1, c) = some (a', c')`, where `run` stops **only** on `Out.halt`. The accelerated map does **not** halt from the post-`j` states: from `(2*3^289 - 1, 2047)` there is no halt in 200000 steps (the orbit keeps returning to `a = 1` and halving `c` again). So `Survives n` holds for every `n` while `Q = a + 2c` grows by at least 3 per step, and no `Budget B` can hold.
* New paired modules `cryptids_a6/BusyBeaver/BB33/M_758_BudgetRefuted.lean` and `rocq/BB33_758_BudgetRefuted.v` prove it. Lean: exit 0, all six results depend only on `propext` / `Quot.sound`. Rocq: exit 0, all six `Print Assumptions` are "Closed under the global context".
  * `run_10001 : run 10001 (5, 1) = some (485, 25453)` — the *smallest* post-`j` state `(2*3^1 - 1, 1)`; `vm_compute` / `decide` verify all 10001 steps.
  * `Q_run_10001 : Q 485 25453 = Q 5 1 + 51384`, so `Q` grows by 51384 > 30000.
  * `not_survives_le_10000`, `not_budget_30000`, `not_budget_of_lt (B < 30003)`.
  Consequently `M_758_TBudget.postJ_survives_le_10000` is **vacuous** — its hypothesis is empty.
* Two independent simulators (`t758_dyn.py`, `t758_big.py`) agree on every rule for all `a, c <= 200`; `t758_sweep.c` / `t758_sweep_h.c` are the exhaustive sweeps.
* **The correct stopping rule** is `ht` of `M_758_Halving844`: stop on `Out.halt`, on `a' = 1`, or on `2*c' <= c0`. Only under that rule is the halving-time question well posed; `Budget` must be restated over it before the alternation bound has content.
* Exhaustive halving time over the **whole** family `1 <= c < 2*3^k` (correct rule, `t758_sweep_h.exe`), max `T` for `k = 1..18`:
  `2, 6, 16, 23, 19, 22, 41, 36, 46, 54, 55, 70, 64, 68, 92, 86, 102, 109`;
  max phase count `2, 3, 10, 11, 10, 8, 16, 14, 22, 18, 20, 26, 24, 30, 32, 30, 34, 38`.
  The growth is slow (about `6k`), so `T <= 10000` for `k <= 292` has a large margin (extrapolating ≲ 1800), unlike the halt-only reading which is unbounded.
* Still open: a proof of the halving-time alternation bound. No halting/non-halting proof. Do not use either required phrase.

## Status 2026-11-17 (third) — budget restated over the halving rule

`M_758_TBudget` / `BB33_758_TBudget` now carry the **correctly posed** residual, in a new section 6b in both files:

* `hrun c0 n a c` — `run` with the stopping rule of the certified 844 trace: stop on `Out.halt`/`Halt`, on `a' = 1`, or on `2*c' <= c0`. `hrun c0 n a c = none` exactly when the halving time is at most `n`.
* `HSurvives c0 n a c := exists a' c', hrun c0 n a c = some (a', c')` — **inhabited and co-inhabited**, unlike the halt-only `Survives`:
  `hsurvives_5_1 : HSurvives 1 1 5 1`, `hrun_stops_5_1 : hrun 1 2 5 1 = none`, `not_hsurvives_5_1 : ~ HSurvives 1 2 5 1`. `(5,1)` is the smallest post-`j` state; its halving time is exactly 2 (stops at `(1,9)`).
* `hrun_Q` — every step of a surviving halving run is a real `Out.next`/`Next` step, so `Q a c + 3*n <= Q a' c'`.
* `hrun_add` — **phase decomposition**: `hrun c0 m a c = some (a1,c1) -> hrun c0 (m+n) a c = hrun c0 n a1 c1`. This is the law a pointwise phase argument needs to chain per-phase bounds.
* `HBudget B` — `Budget` restated over `hrun`: on the halving run `Q` never rises more than `B` above its start.
* `hsurvives_le_of_budget : HBudget B -> 3*n <= B`, and
  **`postJ_halving_le_10000 : HBudget 30000 -> n <= 10000`**, correctly posed.
* The old `Budget` / `postJ_survives_le_10000` are retained only for the cross-reference to `M_758_BudgetRefuted`; they are vacuous.

Verification: Lean exit 0, all new results depend only on `propext` / `Quot.sound` (the `5_1` witnesses on `propext` or nothing); Rocq exit 0 with 35 `Print Assumptions`, all `Closed under the global context`. No `sorry`, `Admitted`, `Parameter`, `Axiom`, `native_decide`.

### Sweep data (halving rule, exact, `t758_hsweep.exe`)

Exhaustive over the whole family `1 <= c < 2*3^k`:

```
k     1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18
T    2   6  16  23  19  22  41  36  46  54  55  70  64  68  92  86 102 109
fase 2   3  10  11  10   8  16  14  22  18  20  26  24  30  32  30  34  38
dQ  10  28  90 140 106 134 246 222 286 328 346 464 410 432 526 540 636 660
```

Large `k` (Python, big ints): `k=289,c=2047: T=844, dQ=5720` (the known extremal);
`k=292,c=2047: T=775, dQ=5298`; `k=292,c=1: T=786, dQ=5450`; `k=289,c=1: T=778, dQ=5394`.
So `dQ/T` settles near 6.8-6.9, `max dQ` is 660 at `k=18`, and `HBudget 30000`
holds with roughly a 5x margin at `k = 292` — the restated target is TRUE in
range and, for the first time, has content.

### Open

`HBudget 30000` (equivalently the halving-time alternation bound) is still unproved.
`T <= 10000` is unproved. No halting/non-halting proof; do not use either required phrase.

## Status 2026-11-17 (fourth) — HBudget verified wide; it provably needs T <= 3333

### Verification of `HBudget 30000`

`dQ` below is `Q_end - Q_0` for the halving run; `HBudget 30000` is exactly `dQ <= 30000`.

Exhaustive over the whole family `1 <= c < 2*3^k` (`t758_hsweep.exe`, exact, no cap hit, no `c` over cap):

```
k         18     19     20     21     22
maxT     109    108    117    127    125
maxPhases 38     38     40     46     44
max dQ   660    686    746    798    782
```

`c` ran over the whole range `1 <= c < 2*3^k` in every case; `overcap = 0`
everywhere, so no visit was ever truncated and no bound is partial.

Wide structured sample at `k = 292` (`t758_k292_sample.py`, `t758_k292_wide.py`):

* `t758_k292_sample.py`: 84 664 values (exhaustive `c <= 60000`, `2047 +- 6000`, `round(A/m)` for `m <= 4000`,
  the `2^-i 3^-j` grid, 20 000 uniform draws) — `maxT = 823` at `c = 11899`, `max dQ = 5844`.
* `t758_k292_wide.py`: **1 419 999** values (exhaustive `c <= 1 200 000`, `round(A/m)` for `m <= 20 000`,
  200 000 uniform draws) — `maxT = 829` at `c = 670447`, `max dQ = 5844` at `c = 11899`.
  So **`HBudget 30000` HOLDS with a 5.13x margin** on a 1.4M-point window at k = 292, and on every
  family member with `k <= 21` exhaustively.

Trend of `max dQ` is about `+50` per unit of `k` (660, 686, 746, 798, ...), i.e. `max dQ(k) ~ 6.8*T_max(k) ~ 41*k`,
so at `k = 292` the extrapolated maximum is ~12 000 — still a 2.5x margin. `HBudget 30000` looks TRUE.

### The budget is provably NOT easier than a length bound

New in section 6c of both files:

* `Q_step_le` — every non-halting step raises `Q` by at most `9` (rules: a:3 b:5 c:9 e:8 h:5 i:8 j:4).
* `hrun_Q_le` — `hrun c0 n a c = some (a',c') -> Q a' c' <= Q a c + 9*n`.
* `HBudget_mono` — `B <= B' -> HBudget B -> HBudget B'`.
* `hbudget_of_length` — `(forall k c n, ... -> HSurvives c n (2*3^k-1) c -> n <= B) -> HBudget (9*B)`.
* `hbudget_30000_of_le_3333` — `(forall k c n, ... -> HSurvives ... -> n <= 3333) -> HBudget 30000`.

Since `3*T <= dQ <= 9*T`, the budget sits strictly between two length bounds:

```
T <= 3333   ==>  HBudget 30000   ==>  T <= 10000
```

So chaining per-phase bounds cannot close the budget without a length bound of
**3333** — three times stronger than the theorem's own target. Per-phase maxima
(`791` per L-phase, `293` per J-phase, ~26 phases observed) sum to far more than
3333, so `hrun_add` chaining of per-phase upper bounds is provably insufficient;
the alternation sum needs the cancellation structure, not the phase maxima.

### Open

`HBudget 30000` and `T <= 10000` both remain unproved. No halting/non-halting proof; do not use either required phrase.

## Status 2026-11-17 (fifth) — target restated over the halving time; budget demoted

`HBudget` is no longer the goal. Section 6 is retitled *"The budget route (superseded, kept for provenance)"*: by `hbudget_of_length` / `hbudget_30000_of_le_3333`, `HBudget 30000` requires `T <= 3333`, which is strictly stronger than the actual target, so the budget was a detour.

New **section 7** in both files (`M_758_TBudget.lean` 927-975, `BB33_758_TBudget.v` 1112-1159):

* `HalvingTimeLe B` — every post-`j` chain has halving time at most `B`.
  `HalvingTimeBound := HalvingTimeLe 10000` — **the target, stated directly over the halving time**.
* `ResidualHalving` — **the single named sub-goal**: for each family member there is a crossing
  `m <= 791` into the `J` region (`a1 <= c1`) with `hrun c m (2*3^k-1) c = Some (a1,c1)`, and every
  residual halving run of length `t` from `(a1,c1)` satisfies `m + t <= 10000`.
* `halving_le_of_split` — **the split**, unconditional and proved: if the run survives `m` steps to
  `(a1,c1)` and `m + t <= B` for every residual length `t`, then every run from `(a,c)` has length
  `<= B`. `hrun_add` supplies the step that turns the `m + d` prefix into a run from `(a1,c1)`
  (`n = m + (n-m)`, then `hrun c0 (m + d) a c = hrun c0 d a1 c1`).
* `halvingTimeBound_of_residual` — **`T <= 10000` from the residual alone**:
  `ResidualHalving -> HalvingTimeBound`. Nothing else is assumed.

So the whole halving time is `first L phase (<= 791) + residual`, and the residual is the only
mathematical obligation left. The `m <= 791` half is what `L_phase_le_791` supplies once the orbit
is linked to the phase sequence; that link is not formalised, and `ResidualHalving` is a
reformulation, not yet proved strictly weaker than `HalvingTimeBound`.

Verification: Lean exit 0, `halving_le_of_split` and `halvingTimeBound_of_residual` depend only on
`propext` / `Quot.sound`. Rocq exit 0 with **42** `Print Assumptions`, all `Closed under the global
context`. Section 7 is declaration-for-declaration identical in the two files.

### Open

`ResidualHalving` (hence `T <= 10000`) is unproved. The budget statements remain as superseded
provenance. No halting/non-halting proof; do not use either required phrase.

## Status 2026-11-17 (sixth) — the crossing assumption removed; it was FALSE

**The previous `ResidualHalving` was false, so `halvingTimeBound_of_residual` was vacuous.** Counterexample: `k = 1`, `c = 3` starts at `(5,3)`, one rule-`e` step gives `(17,1)`, and the halving rule fires on `2*c' = 2 <= c0 = 3`, so `T = 1` and the run ends with `a = 17 > c = 1`. No `m` has the endpoint in the `J` region. The mechanism: rule `e` resets `c` to `1`, after which `2*c' <= c0` can fire *inside* `L`. Coverage of "stops inside `L`": 1/4, 2/16, 6/52, 17/160, 29/484 of the family at `k = 1..5`.

`ResidualHalving` now contains **only the residual halving time** — no crossing, no existence claim:
```
forall k c m a1 c1 t, k <= 292 -> 1 <= c -> c < 2*3^k ->
  hrun c m (2*3^k-1) c = Some (a1,c1) -> m <= 791 ->
  HSurvives c t a1 c1 -> m + t <= 10000
```
`m` may be *any* split point within `791` steps. `halvingTimeBound_of_residual` picks `m = 791`, which `hrun_add` + the new `hsurvives_mono` (prefix monotonicity) justifies, and the `n < 791` case closes immediately. Both are proved and non-vacuous.

### Orbit-to-phase link

Lean section 8 (`M_758_TBudget.lean`, appended at end of file, inside the namespace):
* `st` — the `i`-th state of the halving run, saturating on stop;
* `st_succ_next` — one unfolding through a non-stopping `Next`;
* `st_hrun` — **while the run survives, `st` *is* the state `hrun` reaches**;
* `st_next` — **the `i`-th orbit step is genuinely `step`, state `i` to state `i+1`**;
* `phase_le_791` — **if the orbit survives `n` steps, stays in `L` (`c < a`) and avoids rule `e`, then `n <= 791`**, via `L_step` per step, `L_phase_budget` telescoped, `L_phase_le_791` at `k <= 292`, `1 <= c`. This is the phase-sequence link: the abstraction `A`/`C` is now proved to be the run, not an assumption.

Axioms: `st_hrun`/`st_next` `[propext]`; `phase_le_791` `[propext, Classical.choice, Quot.sound]` (`Classical.choice` from `omega`); everything else unchanged. Lean exit 0.

### Rocq

`hsurvives_mono`, the corrected `ResidualHalving`, `halvingTimeBound_of_residual`, `halving_le_of_split` (restored after an accidental splice deletion), `st`, `st_succ_next`, `st_hrun` all proved. Rocq exit 0, **44** `Print Assumptions`, all `Closed under the global context`.

**Documented gap (Rocq only):** `st_next` and `phase_le_791` are *not* ported. Marked in-file with a `**GAP (Rocq only)**` comment at the end of section 8. Nothing depends on them — `ResidualHalving` and `halvingTimeBound_of_residual` are complete without them. The Lean and Rocq files are therefore **not** yet declaration-for-declaration identical in section 8.

### Open

The residual bound in `ResidualHalving` is unproved, so `T <= 10000` (`HalvingTimeBound`) remains open. Closing it needs the `J`-phase law on the *orbit* (`J_phase_le_293` applied via `st`, the same way `phase_le_791` uses `L_phase_le_791`), plus the per-cycle bookkeeping of `phases <= 243`. No halting/non-halting proof; do not use either required phrase.

## Seventh status (2026-11-17): section 8 is now identical in Lean and Rocq; `halving_le_of_split` cut

**Rocq section 8 completed.** `st_next` and `phase_le_791` are now proved in `rocq/BB33_758_TBudget.v`; the `**GAP (Rocq only)**` note is gone. Declaration parity with Lean section 8: `st`, `st_succ_next`, `st_hrun`, `st_next`, `phase_le_791`.

The port uses the same route as Lean, not a `destruct` of `st`: `st_hrun` at `n = 1` identifies the first orbit state with the run state, then each branch peels `st` with `st_succ_next`. Two Rocq-specific points:
* the statement is `hrun c0 (S i) a c` rather than `hrun c0 (i + 1) a c`, because Rocq's `Nat.add` recurses on its **first** argument, so `i + 1` is not convertible to `S i` (Lean's `Nat.add` recurses on its second, so Lean's `i + 1` is definitionally `S i`). This is the only syntactic difference in the section;
* in the base case the orbit goal must be unfolded with `cbn [hrun]` **after** the index is already a constructor: full `cbn` reduces `2 * c1` to `c1 + (c1 + 0)` inside the `if` guard, after which `remember (orb (Nat.eqb a1 1) (Nat.leb (2 * c1) c0))` no longer matches syntactically.

**`halving_le_of_split` cut from both files.** With `halvingTimeBound_of_residual` splitting at `791` directly via `hrun_add` + `hsurvives_mono`, the general split lemma had no remaining user (checked across `rocq/` and `cryptids_a6/BusyBeaver/`). Removed from `M_758_TBudget.lean` and `BB33_758_TBudget.v` together with its `#print axioms` / `Print Assumptions` line.

Verification: Lean exit 0 (unchanged section 8 axioms: `st_hrun`/`st_next` `[propext]`; `phase_le_791` `[propext, Classical.choice, Quot.sound]`). Rocq exit 0, **45** `Print Assumptions`, all 45 `Closed under the global context` (44 before − `halving_le_of_split` + `st_next` + `phase_le_791`).

**Still open:** the residual bound inside `ResidualHalving` itself. The next step is applying `J_phase_le_293` to the orbit through `st`, exactly as `phase_le_791` applies `L_phase_le_791`, plus the per-cycle `phases <= 243` bookkeeping. `T <= 10000` is not proved; no halting/non-halting phrase applies.

## Eighth status (2026-11-18): the `J`-phase link at the family is proved; it has no consumer yet

**The prescribed route does not close.** `J_phase_le_293` is a statement about the *pure* `j`
recursion (`a' = 3*a+2`, `c' = c-a+1`). An orbit `J` phase is not pure `j`: it also uses rule
`i` (`a' = 3*a`, `c' = c-a+4`), and rule `h` (`a' = 1`) terminates the run. Scanning every
surviving family orbit at `k = 10..14` (`c < 2*3^k`, `c < 200000`) shows phases made only of `j`
are the exception, not the rule, and phases mixing `i` and `j` are common. So `J_phase_le_293`
cannot be applied to the orbit as it stands, and `phase_le_791`'s route is not transferable
verbatim.

**What was built instead (both files, declaration for declaration).** The `J`-side analogue of
`L_step` + `L_phase_budget` + `L_phase_le_791`, stated for what the orbit actually does:

* `step_even_J` - in the `J` region an even `a` stops the run at once (`g` halts, `h` lands on `a = 1`);
* `step_odd_J` - with `a` odd the step is rule `i` (even `c`) or rule `j` (odd `c`), as a closed form;
* `J_step` - both non-halting `J` rules give `3*a <= a'`, `c - a + 1 <= c'`, and `Q` rising by at least `2`;
* `hrun_one` - a surviving single halving step never lands on `a = 1` nor under the halving threshold;
* `three_pow_dominates_9` - `294 <= j` implies `6*3^292 + 9*j < 3^j`;
* `phase_le_293` - **if the orbit survives `n` steps from the post-`j` state `(2*3^k-1, c)`, stays in the `J` region (`a <= c`), and has `a` odd throughout, then `n <= 293`**, for `k <= 292`, `1 <= c`, `c < 2*3^k`.

`phase_le_293` is applied to the orbit exactly as `phase_le_791` applies `L_phase_le_791`: the
per-step link is `st_next`, and the telescoped budget is `Q(a_i,c_i) <= Q_0 + 9*i` from
`hrun_Q_le`, with `3*a_i <= Q_i` and `a_i >= 3^i` forcing `n <= 293`.

The `hodd` hypothesis is the `J`-side counterpart of `phase_le_791`'s `hne`: an even `a` in the
`J` region halts (`g`) or lands on `a = 1` (`h`), which stops the run, so a *surviving* phase has
odd `a` at every state; `hrun_one` records the single-step form of that fact. It is a genuine
side condition on the lemma, not a vacuity: it is what `J_step` consumes.

**Honest limit: the new brick has no consumer.** `ResidualHalving` is unchanged and `T <= 10000`
is still open. The reason is arithmetic, not formal: the per-phase maxima `791` (`L`) and `293`
(`J`) cannot be summed over `phases <= 243` to reach `10000` - `791 + 243*1084` is far above it -
so the "per-cycle phases <= 243 bookkeeping" the previous block called for cannot close the
residual on its own. What is still missing is a *telescoped alternation* bound: a quantity that
decreases monotonically across an `L`/`J` cycle by enough to pay for the cycle's length
(`BB33_758_ATTACK.md` section 14).

### Verification

* Lean: `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` exit 0, no `sorry`, no `sorryAx`.
  Axioms: `step_even_J`, `step_odd_J`, `three_pow_dominates_9` `[propext, Quot.sound]`;
  `J_step`, `hrun_one`, `phase_le_293` `[propext, Classical.choice, Quot.sound]`.
* Rocq: `rocq compile -Q . Top BB33_758_TBudget.v` exit 0, **51** `Print Assumptions`, all
  `Closed under the global context` (the six new ones included).

### Rocq pitfalls found here (both cost a hung compile)

* `cbn in hmain` where `hmain` mentions `st c 293 ...`: `cbn` unfolds the `st` recursion hundreds
  of levels deep and the compile stops making progress. Use
  `replace (294 - 1) with 293 in hmain by reflexivity` instead.
* `ring` on a goal containing `3 ^ 292`: same symptom. Prove big-power identities through
  `Nat2Z.inj` + `rewrite Nat2Z.inj_pow/inj_mul` + `vm_compute; reflexivity`.

**Still open:** the residual bound inside `ResidualHalving`. `T <= 10000` is not proved; no
halting/non-halting phrase applies.

## Ninth status (2026-11-18): the six `J`-phase lemmas cut; the residual is a *tail* obligation

Following the eighth block, the six `J`-phase lemmas (`step_even_J`, `step_odd_J`,
`J_step`, `hrun_one`, `three_pow_dominates_9`, `phase_le_293`) were **cut from both
files** rather than left as dead weight: `phase_le_293` cannot bound a tail (the
tail's first phase may be `L`, and its `J` phases start from states far outside
`c < 2*3^k`), so there was no consumer to wire them into. The statements are
recorded in `BB33_758_ATTACK.md` section 16 in case a future alternation proof
needs them restored.

**What the exact phase table shows (new).** The maximum run (`k = 289`,
`c0 = 2052`, `T = 844`) is `764 + 80`: the first `L` phase is 764 of the 844
steps (`c: 2052 -> 7.03e140`), and all 25 later phases together are 80 steps.
With `phase_le_791` proved, the remaining obligation is a *tail* of at most
`9209` steps, measured at 80. `phase_le_791` is therefore nearly tight on the
extremal, and per-phase maximum bookkeeping is the wrong shape because the run
has one huge phase, not many moderate ones.

**Shortcut refuted (new).** The half-gain accounting
`2*T*log(3/2) <= log(c_max/c_min) + log(a_max/a_min)` fails on the extremal
(684.3 vs 636.3, short by 48) because the rules carry additive constants
(`c' = 3c/2 + {2,5,8}`, `a' = 3a + {0,2}`); a formal proof needs the per-step
corrections, not just the two range logarithms. Exact per-step facts that do
hold (candidate bricks): `2c' >= 3c` at every `L` step, `a' >= 3a` at every `J`
step, and `rho = c/a` decreases at every `J` step and increases at every `L` step.

### Verification after the cut

* Lean: `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` exit 0, 0 errors, no
  `sorryAx`; section 8 axioms unchanged (`st_hrun`/`st_next` `[propext]`,
  `phase_le_791` `[propext, Classical.choice, Quot.sound]`).
* Rocq: `rocq compile -Q . Top BB33_758_TBudget.v` exit 0, **45** `Print
  Assumptions`, all `Closed under the global context`.

**Still open:** `ResidualHalving`, hence `T <= 10000`. Next target: the tail
bound after `phase_le_791` (pair each `L` phase's `c`-growth against the
following `J` phase's `c`-drop, with the additive-constant corrections). No
halting/non-halting conclusion; no required phrase applies.

## Tenth status (2026-11-18): the tail is measured; the coarse cycle bound is specified but not proved

**Measured (141,618 family members, exact `step`/`ht`).** `max T = 844`
(`k=289`, `c=2047` and `2052`), `max first L phase = 785`, **`max tail = 80`**
(same instance), max phases 28. With `phase_le_791` proved, the target leaves
`9209` for the tail — about 100x the measured value, so the remaining obligation
is a *coarse* bound, not the sharp `844` argument.

**Tail mechanism.** After the first `L` phase (`a <= c`) the run alternates `J`
phases (rule `j`: `a` triples, `c` drops by `a`) and `L` phases (rules `b`/`c`:
`c` multiplies by `3/2`, `a` drops by `c`). One full cycle multiplies `c` by
about `2/9` (measured 0.1-0.7), so `#cycles <= log(3*3^k/(c0/2))/log(4.5) <= 215`
and a cycle costs ~3-4 steps. Even the pathological cycle (`a` tiny at a cycle
start, `J` phase running its full `<=294` steps) is followed by cheap cycles.
`tail <= 294 + 4*215 = 1154`, hence `T <= 791 + 1154 = 1945 <= 10000`.

**Not proved.** The four coarse lemmas listed in `BB33_758_ATTACK.md` section 17
(cycle-start ratio bound, per-cycle `c`-contraction `<= 2/3`, cycle count, and
per-cycle length `<= 8` plus one long exception) are the concrete next-session
target. They are arithmetic facts about `step` built on the already-proved
`L_step` and `J_step`; no cookie-cutter machinery is needed for the *coarse*
bound. Nothing was added to the formal files this session, so both keep their
verified state:

* Lean `BusyBeaver/BB33/M_758_TBudget.lean`: exit 0, no `sorryAx`.
* Rocq `BB33_758_TBudget.v`: exit 0, 45 `Print Assumptions`, all `Closed under
  the global context`.

**Still open:** `ResidualHalving`, hence `T <= 10000`. No halting/non-halting
conclusion; no required phrase applies.

## Eleventh status (2026-11-18): the per-cycle `c`-contraction is FALSE, and that is now kernel-checked

The lemma this session was to prove — one `J` phase + one `L` phase contracts `c`,
`4*c_end <= 3*c_start + K` with the additive-constant corrections — is **false**.
Kernel-checked witness in both files:

```
(549,1196) --i--> (1647,651) --c--> (992,983) --c--> (5,1481)     a <= c at both ends
c grows 1196 -> 1481 (x1.238);  4*1481 - 3*1196 = 2336
```

Lean: `cycle_contraction_false`, `cycle_contraction_false_arith`, both
`does not depend on any axioms`.  Rocq: the same two lemmas, both `Closed under the
global context`.  Consequently no per-cycle monotone potential exists, and any
`4c' <= 3c + K` has the fixed point `c ~ 4K`, so it cannot bound the cycle count at
all.  (Measured: largest growth x1.24 over 115,138 pairs; aggregate drift is still
downward, tail <= 80.)

**What still blocks `T <= 10000`** (recorded in `BB33_758_ATTACK.md` section 18):
(1) a *window bound* — for every scale `tau`, at most `K` cycles with `c` in
`[tau, 2*tau]` — i.e. the alternation/cookie-cutter statement, which is not implied by
any per-cycle potential; (2) the small-`c` regime (`c <= tau0`, `a <= c`) is closable by
pigeonhole (`tau0*(tau0+1)/2` states, 5050 at `tau0 = 100`) but only after (1);
(3) both exits (halving test and rule `h` giving `a = 1`) must be covered.

Verification: Lean exit 0, 0 errors, no `sorryAx`; Rocq exit 0, **47** `Print
Assumptions`, all `Closed under the global context`.

**Still open:** `ResidualHalving`, hence `T <= 10000`. No halting/non-halting
conclusion; no required phrase applies.

## Twelfth status (2026-11-18): the window bound has no uniform gap, so the window+pigeonhole plan does not close 10^4

**Measured (exact `step`, `_win.py`).** Cycle ratios `r = c_end/c_start` approach 1 as the
scale grows: `|r-1| = 1.6e-4` at `c = 5.15e53`, `r = 1.00125` at `c = 5.15e53` and at
`c = 1.91e140` (a cycle that *increases* `c`).  A uniform window bound "at most `K` cycles
in `[tau,2tau]` for all `tau`" needs a scale-independent gap `|r-1| >= delta`; the gap
measured vanishes with scale, so the bound is not derivable from a ratio gap and would
need the cookie-cutter argument itself (sections 14, 18).

**The plan does not compose even granting a window bound.** With `|r-1| ~ 1.6e-4` a run
could spend ~555 cycles in one factor-2 window, and `log_2(3^292) ~ 460` windows, far
above the `9209` slack; a usable bound needs `K <= 4` per window, i.e. a gap of ~0.2 that
the measurement refutes.  The small-`c` pigeonhole half is also conditional: a run that
stays in `a <= c <= B` and repeats a state never stops, so pigeonhole yields
"`T <= B(B+1)/2` or the run loops forever"; excluding loops in the box is a ~5000-state
finite check that is not formalised, and without it the brick cannot be composed.

Empirical check for reference: on the family the longest stretch with `c` within a factor
2 of the value at the start of the stretch is 80 steps (the extremal run), consistent with
a small `K` on tested runs only.

**No formal changes this session** (the two candidate bricks are either false or
non-composable, and adding them would be dead weight).  Files keep their verified state:
Lean exit 0, no `sorryAx`; Rocq exit 0, 47 `Print Assumptions`, all `Closed under the
global context`.

**Still open:** `ResidualHalving`, hence `T <= 10000`. No halting/non-halting conclusion;
no required phrase applies.

## Thirteenth status (2026-11-18): coordinate normal form (u,d); shallow-cone phases are constant-length

**New (measured + structural).** In the coordinates `u = (a+2c-1)/2`, `d = (c-1)/2` the
region conditions are *linear* (`a <= c <=> u <= 3d+1`, `a = 1 <=> u = 2d+1`,
`2c' <= c0 <=> d' <= (c0-2)/4`, `a > 2c <=> u > 4d+1`) and both maps are affine with `u`
increasing by >= 2 per step: `J: (u+2, 3d-u+1)`, `L: (u+{5,7,9}, (9d+{20,26,29,35})/4)`.

Family sweep, splitting at the deep cone `a > 2c`:

```
max phase length with a <= 2c :  7 steps
max phase length with a >  2c : 784 steps  (the first L phase, bounded by phase_le_791)
max phases per run            : 37    (max deep-cone phases: 14)
```

So every phase outside the deep cone is at most 7 steps; only deep-cone phases are long,
and the first of those is already covered. This is the structural reason the extremal run
is `764 + 80`, and it turns the tail into a *counting* problem over constant-length phases.

**Still blocking:** within the shallow cone the per-cycle `c` multiplier still approaches 1
(section 19), so a wedge argument must count cycles. Untried tools recorded in
`BB33_758_ATTACK.md` section 20: quadratic/piecewise Lyapunov functions (section 18 only
refuted additive per-cycle inequalities), joint spectral radius / invariant ellipsoid for
`{L,J}` on the wedge, and rotation/three-gap structure of the crossing times.

**No formal changes** this session; files keep their verified state (Lean exit 0, no
`sorryAx`; Rocq exit 0, 47 `Print Assumptions`, all `Closed under the global context`).
`ResidualHalving` and `T <= 10000` remain unproved. No halting/non-halting conclusion; no
required phrase applies.

## Fourteenth status (2026-11-18): no quadratic Lyapunov function exists on the shallow cone

Searched `Phi = a^2 + beta*a*c + gamma*c^2` (positive on `a/c in [0,2]`) over 1995
shallow-cone cycles of the family, requiring `Phi(cycle end) <= lambda*Phi(cycle start)`.
Grid minimax: **min over (beta,gamma) of the max cycle ratio = 2.097** (at
`(0.88, 4.07)`), i.e. the best achievable worst-case growth is about 2.1 > 1. No positive
quadratic form contracts; log-linear and `(u,d)`-quadratic families behave the same.

Why: the shallow cone contains `(9,2291) -> ... -> (1334,1643)` (a x148, c x0.717, five
`j` steps then `c`) and `(23,29) -> (71,7) -> (60,17) -> (41,29) -> (10,47)` (c x1.62). The
first needs a form dominated by `c^2`, the second one dominated by `a^2`; the two
constraints pin `(beta,gamma)` to a sliver near `(-0.5433, 0.2352)` which the remaining
cycles break.

**Consequence:** route (1) of section 20 (single quadratic Lyapunov function) is dead.
Only the region-switched multiple-Lyapunov variant survives, and it must use different
forms per cone with cross-contraction at switches — the switching structure is exactly
where the alternation content sits.

**No formal changes** (the sought object does not exist, so there is nothing to prove).
Files keep their verified state: Lean exit 0, no `sorryAx`; Rocq exit 0, 47 `Print
Assumptions`, all `Closed under the global context`. `ResidualHalving` and `T <= 10000`
remain unproved; no halting/non-halting conclusion, no required phrase applies.

## Fifteenth status (2026-11-18): shallow-cone phase brick proved in its true (sharpened) form

**Superseded for the target (see the sixteenth status).**  The lemmas below were proved
and then removed: the `c < 355` hypothesis is not available (it is false at 95% of the
measured `J`-phase starts) and, even granted, a per-phase length bound gives no
`m + t <= 10000` bound because there is no phase count.

**The literal brick is false.** "In `a <= 2c` every phase has <= 7 steps" fails at
`(1,6561)`: shallow (`1 <= 2*6561`) and its `J` phase has eight steps
`(1,6561)->(5,6561)->(17,6557)->(53,6541)->(161,6489)->(485,6329)->(1457,5845)->
(4373,4389)->(13121,17)`, since each rule `j` triples `a` while `c` barely moves; in
general `(1, 3^n)` has an `n`-step `J` phase. The measured max of 6 over the family is a
reachability artefact (all reachable phase starts have `c <= 2280`).

**What is proved (both files, no sorry/Admitted):**

* `L_shallow_step`: in `c < a <= 2c` a non-halting `L` step ends the phase (`a' <= c'`)
  unless it is rule `e` (`a = c+2`), which sends `(c+2,c)` to `(3c+8,1)` — into the deep cone;
* `jrun_odd_step`: with `a` odd, `J` steps are only `i`,`j`; `a` stays odd, triples, and
  `c` rises by at most 3 (rule `h` needs `a` even, so it can fire at most once per phase);
* `jrun_odd`: a `J` phase of length `n+1` from odd `a` satisfies `3^n * a <= c + 3n`;
* `jrun_eight`: a `J` phase of length 8 forces `c >= 355`;
* `J_phase_le_seven`: in the `J` region with `c < 355`, every phase has length <= 7;
* `shallow_phase_eight`, `shallow_phase_eight_shallow`: the kernel-checked counterexample.

**Blocking case:** only a `J` phase that starts with rule `h` (a even, c odd): it resets
`a` to 1 with `c' = a/2 + c + 2`, so the phase is `1 + log_3(c)` long and the shallow cone
does not bound `c`. Everything else is closed. The brick becomes true with the extra
hypothesis `c < 355` (or any reachability bound on `c` at phase starts).

**Not proved:** `ResidualHalving`, `T <= 10000` (this brick is about phase shape only, not
phase counting). No halting/non-halting conclusion; no required phrase applies.

## Fifteenth-a: verification of the shallow-cone brick (2026-11-18)

Lean: `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` -> exit 0, no errors;
`#print axioms` for all nine new theorems (`le_three_half`, `le_three_half_pred`,
`L_shallow_step`, `jrun_odd_step`, `jrun_odd`, `jrun_eight`, `J_phase_le_seven`,
`shallow_phase_eight`, `shallow_phase_eight_shallow`) shows only `propext`/`Quot.sound`
(or nothing) — no `sorryAx`.

Rocq: `rocq compile -Q . Top BB33_758_TBudget.v` -> exit 0; **67** `Print Assumptions`
lines, all `Closed under the global context` (the original 47 plus 20 helpers added in
section 8d: `div2_le`, `mod2_one_pos`, `mod2_eq_one`, `mod4_eq_three`, `shallow_a_arith`,
`shallow_b_arith`, `shallow_c_arith`, `odd3`, `odd3_add2`, `eight_arith_h`,
`eight_arith_o`, `le_three_half`, `le_three_half_pred`, ...). No `Admitted`, no `Axiom`,
no `Parameter`.

Rocq technical notes for future work in this file (all cost compile cycles here):
`Nat.div_add_mod`/`Nat.div_le_self`/`Nat.add_mul_mod_self_left` do not exist in this
Stdlib; `lia` cannot handle `c / 2`, `c mod 4`, or numerals >= 1000 (`Nat.of_num_uint`);
use `set (k := c / 2)` before `lia`, prove modular facts by `destruct (c mod 4)` with
`Nat.mod_upper_bound`, and prove numeral inequalities by `apply leb_true_le; vm_compute`.

## Sixteenth status (2026-11-18): the `c < 355` brick does not feed `T <= 10000`; section 8d trimmed

**Verdict: the brick cannot feed the halving bound.**  Two reasons, each fatal on its own.

1. It needs a reachability invariant on `c` at phase starts, and that hypothesis is not merely
   unproved but false almost everywhere on the orbit: of **12252 `J`-phase starts** in the
   family sample (`_cj.py`), **only 571 have `c < 355`**.  `c` reaches 2280 in the small-`c`
   part (`(298,2129) -h-> (1,2280)` at `k=7, c0=7`) and is `~6e76` at `k=292`.  So the lemma
   cannot be applied to the phase starts the run actually produces.
2. Even granted, it bounds one region's phase *length* and says nothing about the *number* of
   phases, which is what `ResidualHalving` (`m + t <= 10000`) needs.  Measured rule counts
   (`_ph.py`, 141k runs): `a:6533 b:748511 c:710456 j:8113 h:6580`, max `L` phase 785 vs max
   `J` phase 6 — the length is in rules `b`/`c`, so capping `J` phases at 7 changes little and
   multiplies by nothing.

**Cut from section 8d in both files** (they served only the `c < 355` form): `jrun_eight`,
`J_phase_le_seven`, `shallow_phase_eight`, `shallow_phase_eight_shallow`, and the Rocq
arithmetic helpers `eight_arith_h`, `eight_arith_o`, with their `Print Assumptions` lines.

**Kept** (unconditional, no hypothesis on `c`): `JRun`, `L_shallow_step`, `jrun_odd_step`,
`jrun_odd`, and their arithmetic support (`div2_le`, `mod2_one_pos`, `mod2_eq_one`,
`mod4_eq_three`, `shallow_a_arith`, `shallow_b_arith`, `shallow_c_arith`, `odd3`,
`odd3_add2`, `le_three_half`, `le_three_half_pred`).  These are the handles on the missing
invariant on `c`: `jrun_odd` gives `3^n * a <= c + 3n`, and `L_shallow_step` sends a shallow
`L` step either out of the region or to `c' = 1`.

**Verification after the cut:** Lean `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` ->
exit 0, no errors, no `sorry`, `#print axioms` on the kept lemmas clean (no `sorryAx`).  Rocq
`rocq compile -Q . Top BB33_758_TBudget.v` -> exit 0, **61** `Print Assumptions`, all `Closed
under the global context`.  One earlier Rocq run failed with `Unexpected name ... in the
branch` at `destruct (jrun_odd_step ...) as [Ha' [H3a Hc]]`; that was a file-write race (the
`.v` was rewritten while `rocq compile` was reading it), and the clean rerun exits 0.  Do not
edit the `.v` during a compile.

**Open:** `ResidualHalving`, hence `T <= 10000`.  The gap is phase *counting*, not phase
shape.  No halting/non-halting conclusion; no required phrase applies.

## Seventeenth status (2026-11-18): phase counting -- the true bound, and why a count cannot close

**New lemmas (both files, no sorry/Admitted):** `flips n a c` (region changes along `n` steps),
`flips_le : flips n a c <= n`, `phases_le : flips n a c + 1 <= n + 1`,
`counting_budget_le : 9 <= NL -> 9 <= NJ -> 9209 < 878*NL + 293*NJ`,
`counting_budget_forces : 9 <= NL -> 878*NL + 293*NJ <= 9209 -> NJ <= 4`.

**The count bound is true but trivial:** one-step phases occur, so a count is the length up to
phase lengths and cannot replace a length bound.

**Why counting cannot close the residual:** `ResidualHalving` has `9209` steps after the first
phase (`10000 - 791`).  With the proved per-phase budgets `878` (post-`j` `L`) and `293` (`j`),
a residual with `NL` `L` and `NJ` `j` phases is bounded only by `878*NL + 293*NJ`.  Measured
worst residual (`_pc.py`, `k = 289, c0 = 2047`, total 844): 18 residual phases, 9 `L` + 9 `J`,
actual lengths `39 + 14 = 53`.  Then `878*9 + 293*9 = 10539 > 9209`, so even exact counts do not
fit; nine `L` phases would allow at most four `j` phases, and the measured residual has nine.

**Exact blocker:** no bound on the number of phases can close `ResidualHalving` while the
per-phase budgets stay at 878/293.  The per-phase bounds are ~100x the actual lengths, and
tightening them is the phase-length brick (sixteenth status), false unconditionally.  What is
missing is a per-phase bound in terms of that phase's own `c` -- a halving-time statement, not
a count.

**Open:** `ResidualHalving`, `T <= 10000`.  No halting/non-halting conclusion; no required
phrase applies.

## Eighteenth status (2026-11-18): phase composition proved; the charging breaks at phase 2

**New lemmas (both files, no sorry/Admitted):** `ssum`, `sL`, `sJ` (phase-length sum and the
two tag counts over one index) with `ssum_succ`/`sL_succ`/`sJ_succ`;
`phase_composition : ssum len N <= 878 * sL tag N + 293 * sJ tag N` given per-phase charges
(an induction on the phase sequence); `residual_counting_forces` (charge fits + `NL >= 9` =>
`t <= 9209` and `NJ <= 4`); `L_phase_le_878_gen` (the `L` charge at an arbitrary phase start,
`a0 <= 2*3^292`), with `L_phase_le_878` reduced to a corollary of it; `postJ_charge`
(`1 <= a`, `a <= 2*3^292`, `a + 2c <= 6*3^292` all follow from `k <= 292`, `1 <= c`,
`c < 2*3^k`); `postJ_charge_extremal`; `phase_two_breaks`.
Rocq also has symbolic helpers `pow3_succ`, `pow3_293`, `two_mul_pred_odd`,
`phase_two_breaks_gen` (crossing proved for abstract `u >= 1`, then instantiated at
`u = 3^292`): `vm_compute` on the 465-bit numeral runs out of memory and `lia` on it
fails with 'Cannot find witness', so nothing touches the numeral.

**The composition is closed as arithmetic:** `t <= 878*NL + 293*NJ` is now a theorem from the
per-phase charges, and `residual_counting_forces` composes it with `counting_budget_forces`.

**Carrying the post-`j` hypothesis through reaches exactly one phase.**  `postJ_charge`
discharges both charges at the post-`j` state, so phase 1 is charged unconditionally.
`phase_two_breaks`: from `(2*3^292-1, 2*3^292-1)` one rule-`j` step gives `(2*3^293-1, 1)`,
where `2*3^292 < 2*3^293-1` and `6*3^292 < (2*3^293-1)+2` -- **both** caps fail.  The charges
are fixed-constant statements about the post-`j` family, while `Q` rises by >= 3 per step and
a rule-`j` step triples `a+1`.

**Which phase breaks it:** the second (the first phase whose start is not the post-`j` state).
`ResidualHalving` starts 791 steps in, so the composition charges at most one phase there.  The
inequality is true on every measured run (844 steps, `(NL,NJ) = (9,9)`, charge 10539); what
fails is its derivation from the two proved per-phase budgets plus the post-`j` hypothesis.
Closing the residual still needs the `c`-dependent per-phase budget (seventeenth status).

**Open:** `ResidualHalving`, `T <= 10000`.  No halting/non-halting conclusion; no required
phrase applies.

**Nineteenth pass -- the phase list built from the run; per-start budgets.**  `cutLen` +
`ssum_cutLen` (`ssum (cutLen b) N = b N - b 0`), `reg`, `phaseTag`, `cut_mono_le`,
`hrun_phase_composition` (`n <= 878*NL+293*NJ` for a real `hrun`, plus
`st c0 n a c = (a',c')`), `hrun_phase_counting`.  `residual_counting_forces` was CUT from
both files: it was `phase_composition` + `counting_budget_forces` + omega, no content;
`hrun_phase_counting` now consumes `counting_budget_forces`.  New per-start budgets
`L_phase_len_c0` (`n*c0 <= a0+2*c0`) and `J_phase_len_own` (`2*(m*a0) <= a0+2*c0+2*m`), with
helpers `n_mul_pow2_le`, `three_pow_ge_lin` and (Rocq) `le_of_mul_le_mul_l`.  Both files
green: Lean exit 0, nine new lemmas `propext`/`Quot.sound` only; Rocq exit 0, 85
`Print Assumptions` closed, no `Axioms:`.  These bounds are linear in `Q0` where the cap
constants are logarithmic, so they do not close the residual; the missing piece is the
product/alternation bound.  Open: `ResidualHalving`, `T <= 10000`.

**Twentieth pass -- what `T <= 10000` means and where its content lives.**  `HalvingTimeBound`
= every post-`j` halving run stops within 10000 accelerated steps (on a halt, on `a' = 1`, or on
`2c' <= c`).  Measured (`_ht_scan.py`, `_ht_tail.py`): exhaustive `k <= 8` max 41; sampled
`k = 30..292` max 790 at `k = 292` (certified record 844) -- so 10000 has 12x slack and the
constant is not the obstacle.  Every extremal run is `T = first phase + tail` with the first
phase `<= 791` (already proved) and the tail `5..36` steps over ~13 phases; exit census over
1200 runs: `a' = 1` 935, halt 174, `2c' <= c` 91.  In the tail `c` is `1.5^t1 * c_0`, so the
halving exit is dead and the only live exits are parity events: an even `a` with `a <= c` stops
the run immediately (rule `g` halts, rule `h` gives `a' = 1`), rules `i`/`j` keep both parities
odd, `L` rules `b`/`c` keep `c` odd and flip `a`'s parity, so the run stops at the first `L`
phase closing on even `a`.  Hence tail length is a parity-coincidence time, not a size --
the reason the `Q`-budget (provably requires `T <= 3333`), the per-phase budgets and the
counting route all stall.  Next bricks (unconditional, not yet formalised): `hrun_odd_of_le`,
`tail_odd`, `exit_parity`; then the open core is bounding the wrong-parity `L` phases.  Both
files still green from the nineteenth pass; no new proofs claimed, nothing `Admitted`.
`ResidualHalving`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Twenty-first pass -- the parity invariants, proved in both files, and the sharp bound on
wrong-parity closes.**  Section 8h of `M_758_TBudget.lean` and of `BB33_758_TBudget.v` now
holds `hrun_odd_of_le` (a surviving `a <= c` state has odd `a`), `J_step_odd` (rules `i`/`j`
keep both parities odd), `L_step_odd` (with `c` odd, `c'` stays odd and `(a' + a) % 2 = 1`,
except rule `e` landing on `c' = 1`), `hrun_stop_of_L_close` (an `L` close on even `a` stops
the run: `hrun c0 1 a c = none`), `tail_step_odd` (the same facts on the run's own orbit
`st`), `L_budget_down` (the `L`-phase budget is downward closed in the length) and
`survives_forbids_wrong_close`.  Audits closed: Lean 18 new `#print axioms`, all
`[propext, Quot.sound]`; Rocq 22 new `Print Assumptions`, no `Axioms:`.  The mod arithmetic
was factored into `mod_two_of_mod_four_{even,one,three}`, `mod_four_three`,
`half_mod_two_of_mod_four_{one,three}`, `three_mul_add_{five,eight}_odd`, `flip_two`,
`flip_four`, because the subtraction form `a' % 2 = 1 - a % 2` and bare `by omega` on the
compound branch goals pull `Classical.choice` in (the older `L_step` still carries it).
`flip_four` needs `a != c+1, c+2, c+3`: at `a = c+3` rule `c`'s drop is `0` and the flip
fails.  The bound on wrong-parity `L` phases is sharp and zero:
`survives_forbids_wrong_close` says no state before the last one of a run of length `L` is an
`L` close on even `a`, so a wrong-parity close is terminal and a run has at most one.  What
blocks `T <= 10000` is therefore not parity but the phase count `NL`, `NJ` in
`878*NL + 293*NJ`: both budgets bound a phase's length by a logarithm of its own start and are
downward closed (`L_budget_down`), so they constrain size, never the number of phases, and
`run_Q` only gives `Q >= Q_start + 3*steps` -- no telescoping over an unbounded number of
phases; equivalently the residual is `HBudget 30000`, which needs `T <= 3333`.
`ResidualHalving`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Twenty-second pass -- `L_step` audit-clean, and the phase-count bound refuted.**  Both files
now state the per-rule arithmetic of `L_step` as separate lemmas (`L_drop`, `L_grow_a`,
`L_grow_b`, `L_grow_c`, with the residue facts `mod_two_of_mod_four_{even,one,three}` and
`mod_four_three` moved to section 2b), and `L_step` only dispatches:
`exact <L_drop ..., L_grow_...>`.  Reason: `omega` on a *conjunction* goal decides the split
and pulls in `Classical.choice`, while the two halves proved separately are
`[propext, Quot.sound]`; `L_step` is now `[propext, Quot.sound]` and so is `phase_le_791`,
which inherited the axiom through it.  Rocq's `L_step` was already closed and is restated in
the same shape.  The phase-count bound of the twenty-first pass is **false**, not merely
unproved: the new counter `pcnt c0 n a c` (walks `step` under `hrun`'s stopping rule and
counts phase starts) gives `pcnt 24 41 (2*3^7 - 1) 24 = (8, 8)` -- the family state
`(4373, 24)` has 8 `L` and 8 `J` phases in 40 surviving steps (`witness_phase_counts`,
`witness_run_stops`, `phase_count_bound_false`, kernel `decide` / `vm_compute`, no axioms).
The measured maximum over `k <= 8` exhaustively is `(8, 8)`; the certified 844-step trace
(`k = 289, c0 = 2047`) has `(13, 13)`.  Consequence: with the proved charges 878/293 the
residual needs `878*NL + 293*NJ <= 9209`, and the witness already charges `9368 > 9209`
(`counting_budget_le_8`, `witness_charge_exceeds`), so **no count bound can close
`ResidualHalving`** at these budgets -- the missing brick is a per-phase *length* bound at the
phase's own start, not a count.  `ResidualHalving`, `T <= 10000` remain open; no
halting/non-halting conclusion.

**Twenty-third pass -- the residual retargeted onto the per-phase own-start charge, with the composition proved.**  Section 10 of both files states the per-phase length bound the way section 28 said it has to be stated: at the phase's *own* start.  `lAdm`/`jAdm` are the two budgets as admissibility predicates; `lLen a0 c0` and `jLen a0 c0` are the largest admissible lengths (bounded scans `lScan`/`jScan`, fuel `a0+2*c0+2`), i.e. `log_{3/2}((a0+2*c0)/(2*c0))` and `log_3` of the `j` budget as integers.  `LPhaseAt C n a0 c0` / `JPhaseAt C m a0 c0` are real phases of a halving run at their own start, and `l_phase_len_at` / `j_phase_len_at` prove `n <= lLen a0 c0` and `m <= jLen a0 c0` unconditionally -- `L_phase_budget`/`J_phase_budget` on the orbit through `st_next`, no `878`, no `293`, no `phase_two_breaks`.  The retargeted residual is `PhaseLedger`: every post-`j` family run admits a phase-aligned cut whose own-start charges `phaseCharge` sum to at most `10000`, and `halvingTimeBound_of_phase_ledger : PhaseLedger -> HalvingTimeBound` is the composition (phase lengths add to `n` by `ssum_cutLen`, each is at most its own charge, charges fit in `10000`; no phase count anywhere).  The gap is exactly `PhaseLedger`, in two separated parts: the cut exists (bookkeeping -- `pcnt` already walks the phases) and the charge sum fits (section 27's alternation bound in additive form).  The sum is not derivable from the per-phase budgets because they are downward closed (`L_budget_down`), but it is true on every measured run: `_ledger.py` gives max ledger 42 over the exhaustive `k <= 8` family (19673 runs) and max 844 over 19952 runs including large-`k` samples, tight at the certified record trace (`k=289, c0=2047`: ledger 844 = T, 26 phases, first charge 764 vs its 791 bound) and 42 vs T=41 at the `k=7, c=24` witness -- 11.8x slack against 10000.  Audits: Lean exit 0, 24 new `#print axioms`, 12 axiom-free (`lAdm`...`PhaseLedger`) and 12 `[propext, Quot.sound]`, no `Classical.choice`; Rocq exit 0, 26 new `Print Assumptions`, all closed, no `Axioms:`.  `ResidualHalving`, `T <= 10000` remain open; the remaining hypothesis is `PhaseLedger`; no halting/non-halting conclusion.

**Twenty-fourth pass -- the near-state brick: `c < a <= c + 3` dies in two steps.**  Section 11 is new in both files.  `hrun_two_halt`, `hrun_two_stop`, `hrun_two_step` are the length-two unfolding of `hrun` (`hrun_S` in Rocq) and `hrun_near` is the theorem:

    c0 >= 2 -> c < a -> a <= c + 3 -> hrun c0 2 a c = none

So a near state cannot be survived.  The case analysis is by `a - c` and `c mod 4`: `step_f`/`step_halt1`/`step_halt3` halt; `step_a` lands on `a' = 0` or `a' = 1`; `step_b` lands on `a' = 0` or `a' = 1`; `step_e` lands on `c' = 1` and `2*1 <= c0` is exactly `2 <= c0`; the `a' = 0` and `a' = 2` cases go to `hrun_stops_of_even_le`.  Why it matters: an `L` step's drop is `a - c - r`, and the offsets `a - c in {1,2,3}` are now proved terminal, so a phase start with `a` far below `c` can only come from `a = c + 4` with `c mod 4 in {0,2}`, which lands on `a' = 3`.  That is the Diophantine bottleneck the ratio lower bound `a >= c/K` (section 30 of the attack notes) has to pass, and it is now a single residue class of a single offset rather than a size statement.  Audits: Lean exit 0, `hrun_near` and the three `hrun_two_*` helpers `[propext]`-only, no `Classical.choice`, no `sorry`; Rocq `rocq compile` clean, `hrun_near`, `hrun_two_*`, `orb_mod4_*` all closed, no `Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Twenty-fifth pass -- the `L`-start gap, and the collapse pinned to `a = c + 4`.**  Section 12 is new in both files.  Section 30's target `a >= c/K` at *every* phase start is false at `j` starts (a `j` start has `a <= c`, and the tail reaches `(3, 3*(c/2)+2)` with `a/c ~ 1/c`), so the object proved is the gap `a - c` at `L` starts: an `L` step sends `(a,c)` to `a' = a - c - r`, so the next `j` start's `a'` is exactly the previous `L` start's gap minus `r`.

    hrun_two_gap_four_odd :  c mod 4 = 1 \/ c mod 4 = 3  ->  hrun c0 2 (c+4) c = None
    L_gap_ge_four         :  2 <= c0 -> c < a -> HSurvives c0 2 a c -> c + 4 <= a
    L_gap_four_shape      :  2 <= c0 -> c < a -> a = c+4 -> HSurvives c0 2 a c ->
                                (c mod 4 = 0 \/ c mod 4 = 2) /\ st c0 1 a c = (3, 3*(c/2)+2)
    lLen_gap_four         :  3 <= c -> lLen (c+4) c = 1
    phaseCharge_gap_four  :  3 <= c -> phaseCharge (c+4) c = 1

`L_gap_ge_four` is `hrun_near` contrapositive.  `L_gap_four_shape` is the reduction section 30 asked for: at gap four the odd residues die within two steps (rule `b` -> `a' = 2`, rule `c` -> `a' = 0`, both even in `J`, `hrun_stops_of_even_le`), so a surviving gap-4 state has `c` even and steps by rule `a` onto `(3, 3*(c/2)+2)`.  `lLen_gap_four`/`phaseCharge_gap_four` say that phase is charged exactly one, so every collapse is `one L step of charge 1` followed by `a j phase from (3, 3*(c/2)+2)`, the latter being the only place the walk can be expensive (`jLen 3 c0 ~ log_3(c0/2)`, up to ~458 steps at the record scale).  New scan machinery: `lScan_stop` (the scan stops when the next length is inadmissible) and `lScan_step` (it steps when admissible), both axiom-free in Lean.  Audits: Lean exit 0, section 12 lemmas `[propext, Quot.sound]`, no `Classical.choice`, no `sorry`; Rocq `rocq compile` clean, all new `Print Assumptions` closed, no `Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Twenty-sixth pass -- signature cleanup and the formal ledger link.**  `L_gap_four_shape` drops the redundant `2 <= c0` hypothesis in both files (its proof only uses `hrun_two_gap_four_odd`, which needs no bound on `c0`), and `L_gap_four_ledger` is added: `3 <= c -> HSurvives c0 2 (c+4) c -> (c mod 4 = 0 \/ c mod 4 = 2) /\ st c0 1 (c+4) c = (3, 3*(c/2)+2) /\ phaseCharge (c+4) c = 1`, i.e. the collapse shape and its charge of exactly one in a single theorem.  Lean exit 0, both `[propext, Quot.sound]`, no `sorry`; Rocq exit 0, 160 `Print Assumptions` closed, no `Axioms:`.  `PhaseLedger` remains open.

**Twenty-seventh pass -- the collapse count: at most half of a run's states.**  Section 13 is new in both files.  Measurement first (`_g4.py`): over the exhaustive `k <= 8` family (19673 runs) and 400 large-`k` samples, at most **one** gap-4 `L` state per run (34 runs have one: 31 odd-`c` hits that `hrun_two_gap_four_odd` kills within two steps, and 3 even-`c`, `c >= 3` hits that are genuine surviving collapse candidates), never two.  Theorems: `g4 a c := c < a /\ a = c + 4`; `g4cnt c0 n a c` counts gap-4 states along the run; `g4_step_le_three : g4 a c -> step a c = Next a' c' -> a' <= 3` (rule `a` gives 3, rule `b` gives 2, rule `c` gives 0, and the halting branches are excluded since `a = c + 4` is neither `c + 1` nor `c + 3`); `g4_succ_not` (no two consecutive gap-4 states); `g4cnt_le`/`g4cnt_le_half : 2 * g4cnt c0 n a c <= n + 1` (division-free, with the refinement `~ g4 a c -> 2 * count <= n`); and `g4_charge`, which is `L_gap_four_ledger` read at a run state: `g4 a c -> 3 <= c -> HSurvives c0 2 a c -> st c0 1 a c = (3, 3*(c/2)+2) /\ phaseCharge a c = 1`, so the counted states are exactly the ones charged one.  Consequence: at most `(n+1)/2` collapses per run, i.e. at most 5000 if `T <= 10000`; it does not close `PhaseLedger`, because each collapse is followed by a `j` phase from `(3, .)` whose charge this count does not bound.  Audits: Lean exit 0, all five `[propext, Quot.sound]`, no `Classical.choice`, no `sorry`; Rocq exit 0, 166 `Print Assumptions` closed, no `Axioms:`.  `PhaseLedger` remains open; no halting/non-halting conclusion.

**Twenty-eighth pass -- odd-`c` gap sharpening (gaps 4 and 6 dead; gap 5 pinned to `c % 4 = 1`).**  Section 14 is new in both files.  Because every reachable post-`j` state has `c` odd (rules `a` and `g` are unreachable), `a = c + 4` is unconditionally dead within 2 steps on odd-`c` orbits (`L_gap_ge_five_odd : c + 5 <= a`), `a = c + 5` with `c % 4 = 3` stops immediately on `a' = 1` (`hrun_two_gap_five_mod3`), `a = c + 6` with `c` odd dies within 2 steps (`hrun_two_gap_six_odd`: rule `b` lands on `a' = 4`, rule `c` on `a' = 2`), and `L_gap_five_or_ge_seven_odd` pins every surviving odd-`c` `L` state to either `a = c + 5, c % 4 = 1` (stepping to `(3, 3*((c-1)/2)+5)`) or `c + 7 <= a`.  Also tested exact affine cycle-skipping forward acceleration from `1.059e15`: skips 254B chains (`bcjjch`) to `1,079,817,520,122,241` in 0.01s before entering the `bcjjj...` L-phase chaotic zone (`n_L ~ 60`, `2^{n_L} > c`), and verified exact periodic-ray drift `s* * dQ / 2` is non-integral for all short surviving cycles (`bbj..bbbbjj`) and adversarial `s* = 8/23, 32/227` shadowing at `k = 292` dies by `T = 623`.  Audits: Lean exit 0, all four `[propext, Quot.sound]`, no `Classical.choice`, no `sorry`; Rocq exit 0, all `Print Assumptions` closed, no `Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Twenty-ninth pass -- odd-`c` invariance along `hrun`, shallow odd-`a` kill band, and `g4cnt = 0`.**  Section 15 of `M_758_TBudget.lean` and companion module `rocq/BB33_758_OddC.v` (imports `BB33_758_TBudget`, compiles in 2s) prove: `step_odd_c` and `hrun_odd_c` (`c` stays odd throughout every surviving halving run started at odd `c`); `hrun_two_odd_a_shallow` (on odd `c`, *every* odd `a` in the entire shallow-L band `c < a <= (5*c + 11)/2` dies in at most two steps, subsuming all even gaps `a = c + 2m` up to `2.5*c + 5`); and `g4cnt_zero_of_odd_survives` (`g4cnt c0 n a c = 0` on every surviving odd-`c` run of length `n + 1`, replacing Pass 27's `2 * g4cnt <= n + 1` with exact `0`).  Audits: Lean exit 0, all four `[propext, Quot.sound]`, no `Classical.choice`, no `sorry`; Rocq `BB33_758_OddC.v` exit 0, all 9 `Print Assumptions` `Closed under the global context`, no `Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open; no halting/non-halting conclusion.

**Thirtieth pass -- surviving `L`-phase length `>= 2` and the `5/11` `J`-exit ratio bound.**  Section 16 of `M_758_TBudget.lean` and `rocq/BB33_758_OddC.v` prove: `hrun_two_odd_a_mod3_wide` (when `c % 4 = 3` and `a` is odd, the 2-step kill band extends to `2 * a <= 5 * c + 21`); `surviving_L_start_ratio` (every surviving odd-`a`, odd-`c` `L`-start satisfies `5 * c + 13 <= 2 * a`, i.e. `s < 4/9`); `surviving_L_next_in_L` (every surviving odd-`a`, odd-`c` `L`-start remains in `L` after step 1 with even `a'` and odd `c'`, forcing every surviving tail `L`-phase to have length `>= 2`); and `surviving_J_exit_ratio` (every surviving `J -> L` exit satisfies `5 * c + 14 <= 11 * a`, i.e. `a > (5/11) * c`).  Audits: Lean exit 0 (`[propext, Quot.sound]`, no `sorry`, no `Classical.choice`); Rocq `BB33_758_OddC.v` exit 0 (all 13 `Print Assumptions` `Closed under the global context`, no `Axioms:`).  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open; no halting/non-halting conclusion.

