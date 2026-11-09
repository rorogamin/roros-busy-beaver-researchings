# Independent Verification Report — BBWork Directory

**Date:** 2026-11-09  
**Verifier:** Gemini 3.8 Flash (Independent Automated Auditor)  
**Verification Standard:** Kernel-checked formal proofs only (Lean 4.35.0 / Rocq 9.1.0) and direct binary executions. Zero unverified assertions, zero `sorry`, zero `admit`, zero hallucinated proofs. Every claim is strictly demarcated as either **PROVED** (with explicit axiom sets), **CONDITIONAL / REDUCTION**, **EMPIRICAL BOUND**, or **OPEN / OBSTRUCTED**.

---

## 1. Executive Summary of Verifications

| Component | Target Machine / Scope | Method | Status | Axioms / Result |
|---|---|---|---|---|
| **Cryptids A6** | BB(6) Holdout 92633 (`1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`) | `lake env lean artifacts/a6/Audit.lean` | **PROVED NON-HALTING** | `[propext, Classical.choice, Quot.sound]`, 0 `sorry`, 0 `native_decide` |
| **Lean22 / 60-list** | 20 nonhalting machines in `solved22.txt` | `verify_holdout_map.py` & build logs | **VERIFIED** | 20/20 in 60-list, 0/20 in formal 37-list; #32 mirror verified exact |
| **Lean M14** | BB(2,5) Holdout 14 (`1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`) | `lean Machine14*.lean` (Bridge, Phase, Counter, Assembly) | **OBSTRUCTION PROVED** | Proves partition invariant holds but supplied rules get stuck at `gt_R_stuck`. No false non-halting claim. |
| **Lean TM25** | BB(2,5) Holdout 7 (`1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`) | `lean TM25.lean` (20 theorems) | **CONDITIONAL REDUCTION** | Proves non-halting conditional on `A3Shield` & `B1Safe`. Finite certificate to $10^8$ steps (`native_decide`). |
| **Native Shield C** | BB(2,5) Holdout 7 | `leftshield.exe`, `leftshield_deep.exe` | **EMPIRICAL PASS** | $10^8$ steps in 2s: 0 violations of `A3_left`, 0 violations of `B1_left1`. |
| **BB(3,3) Merge** | 153 vs 758 | `merge.py`, `iso.py` | **PROVED ISOMORPHIC & MERGED** | Isomorphic under $A \to C \to B \to A$, $1 \leftrightarrow 2$, mirror=True. Merges at 153@1,790,901 / 758@1,841,608. |
| **BB(3,3) Divergence**| 531 vs 532, 397 | `iso.py`, `mergefind.exe` | **CONFIRMED NOT ISOMORPHIC** | Transient match at step 29k/20k diverges 2 steps later upon reading (C,1). |
| **Holdout Symmetries**| 37, 60, 608, 6 lists | `canon.py` | **VERIFIED DEDUPLICATED** | 37/37, 60/60, 608/608, 6/6 unique classes; 37 $\subset$ 60 confirmed. |
| **Wallmemo 758** | Exploding wall $H$ | `wallmemo.exe` | **VERIFIED BOUND** | Selftest pass ($k=1$ 7,391 chains, $k=2$ 4,162 chains); verified 1,000 values in 1s. |
| **LongAcc Engine** | Holdout 1 (`1RB3RB---3LA1RA_2LA3RA4LB0LB1LB`) | `node longacc_run.mjs` (Wasm) | **VERIFIED COMPRESSED MACRO** | Ran to row 6713 (step width 6737) in 5s; configuration output intact. |

---

## 2. Detailed Findings by Sub-Project

### 2.1 Cryptids A6 (BB(6) Holdout 92633)
* **File:** `cryptids_a6/artifacts/a6/Audit.lean`
* **Execution:** Ran `lake env lean artifacts/a6/Audit.lean` using Lean 4.35.0.
* **Result:** Exit code 0.
* **Kernel Axioms:**
  ```lean
  BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.is_not_halt :
    BusyBeaver.IsNotHalt BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.target
  'BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.is_not_halt' depends on axioms:
    [propext, Classical.choice, Quot.sound]
  'BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.not_halts' depends on axioms:
    [propext, Classical.choice, Quot.sound]
  ```
* **Verdict:** Unconditional non-halting theorem for Holdout 92633 is genuine, fully checked, and relies only on foundational standard Lean axioms without `sorry`, `admit`, or `native_decide`.

---

### 2.2 Machine 14 (BB(2,5) Holdout 14)
* **Files:** `lean/Machine14.lean`, `lean/Machine14Bridge.lean`, `lean/Machine14Phase.lean`, `lean/Machine14Counter.lean`, `lean/Machine14Assembly.lean`
* **Execution:** Executed `lean` across all five modules with `LEAN_PATH="."`.
* **Result:** All files compile with exit code 0.
* **Kernel Axioms:**
  * `M14.raw_prefix_14`: No axioms.
  * `M14.raw_first_macro`: No axioms.
  * `M14.gt_R_stuck`: `[propext]`.
  * `M14.partition_insufficient`: `[propext]`.
  * `M14.stepB_inv`: `[propext]`.
  * `M14.rawRun_bridges_runB`: `[propext]`.
  * `M14.safe_checked_million`: `[propext, safe_checked_million._native.native_decide.ax_1_1]`.
* **Verdict:** Rigorous, honest formal development. It does **not** claim to prove Holdout 14 nonhalting; instead, it machine-checks that the candidate block partition holds, and proves that the obstruction to completing the nonhalting proof is the missing rule for `>` reading `R` (`gt_R_stuck`).

---

### 2.3 Machine 25 (Holdout 7 — Deep Shield Reduction)
* **File:** `lean/TM25.lean`
* **Execution:** Executed `lean TM25.lean` on all 20 exported theorems.
* **Result:** Exit code 0 after kernel verification of the $10^8$-step certificate.
* **Kernel Axioms:**
  * `TM25.not_halts_of_A3Shield_B1Safe`: `[propext, Quot.sound]`.
  * `TM25.not_halts_of_A3ShieldDeep_B1Safe`: `[propext, Quot.sound]`.
  * `TM25.invariants_checked_to_hundred_million`: `[propext, native_decide.ax]`.
  * `TM25.cascade_dies_of_not_cantor`: `[propext, Quot.sound]`.
  * `TM25.halt_needs_left_arrival`: `[propext, Quot.sound]`.
* **Independent C Validation:**
  * `leftshield.exe 100000000`: `steps=100000000 A3_left=386 violA3=0 B_left=49999613 B1=227 B1_left1=0`.
  * `leftshield_deep.exe 100000000`: `steps=100000000 A3_left=386 violA3=0 deepViol=0 B_left=49999613 B1=227 B1_left1=0`.
* **Verdict:** The mathematical reduction from nonhalting to the two shield invariants is sound. However, the nonhalting theorem itself remains strictly **conditional**; Holdout 7 is documented in `audit36_likely_halting.md` as **HALT-LIKELY** by harmonic-series arguments, so any claim of an unconditional nonhalting proof would be mathematically unsound.

---

### 2.4 Holdout List Reconciliation (Lean22)
* **File:** `lean22/verify_holdout_map.py`
* **Execution:** Ran `python verify_holdout_map.py`.
* **Result:**
  * 60-list entries: 60.
  * 37-list entries: 37.
  * Nonhalting claims in batch: 20.
  * Claims in 60-list: 20/20.
  * Claims in 37-list: 0/20.
  * Machine #32 exact mirror relation verified.
* **Verdict:** Confirms that the 20 resolved machines belong entirely to the disputed 23 machines separating the 60-list from the formal 37-list, leaving the core 37 formal holdouts intact.

---

### 2.5 BB(3,3) Equivalence & Isomorphisms
* **Files:** `merge.py`, `iso.py`, `reach.py`, `sim.c` / `sim.exe`
* **Execution:** Executed Python and C verification scripts.
* **Results:**
  * **153 ≡ 758:** Isomorphism confirmed with permutation $((2,0,1), (0,2,1), \text{mirror}=\text{True})$. Configuration merge confirmed at 153@1,790,901 and 758@1,841,608 with normalized length 681 and head offset 170.
  * **531 ≢ 532:** Machines are not isomorphic. Transient tape match at step 29,156 diverges 2 steps later upon reading $(C,1)$.
  * **Reachability:** All six BB(3,3) holdouts visit 8/9 transitions; Bigfoot never reads $(2,0)$.
  * **Simulation:** `sim.exe` verified $10^6$ steps across all 6 machines with zero halts.

---

## 3. Issues and Caveats Found During Verification

1. **Interrupted $10^{11}$ Cycle Runs:**
   * Directories `cycle37_1e11/logs` and `cycle37_1e11_coarse/logs` contain zero-byte `.out` files. The previous run was killed before recording completed status lines.
2. **Path Dependency in `canon.py`:**
   * Running `python canon.py` from the root workspace fails with `FileNotFoundError` because it looks for `Bb2x5_informalLast37.txt` in the current working directory. It must be run with working directory set to `bbwork/`.
3. **Module Search Path for `Machine14Bridge.lean`:**
   * Direct invocation via `lean Machine14Bridge.lean` fails to resolve `Machine14TwoSided.olean` unless `LEAN_PATH="."` is set.
4. **`bigfoot_formal` Mathlib Checkout:**
   * `bbwork/bigfoot_formal/` does not have pre-built packages or a committed manifest, meaning running `lake build` triggers network downloads of mathlib4 and verso revisions.

---

## 4. Integrity Statement

No automated proofs were fabricated. No unresolved mathematical cryptid was asserted to be solved. All verified results recorded above reflect actual kernel or binary outputs generated on this machine.
