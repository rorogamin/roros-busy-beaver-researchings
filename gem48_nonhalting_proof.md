# Empirical Recurrence & Non-Halting Analysis of gem48 (Proof Sketch / Conjecture)

**Machine:** `gem48.morphett(2).txt` / `rocq/gemini_epsilon1_tm_48s_v2_fix.v`  
**Specification:** 48 states, 2 symbols (`_` = 0, `1` = 1), 96 transitions.  
**Start Configuration:** Blank tape, state 0 (`S01`), head at 0.  
**Status:** **EMPIRICAL PATTERN / UNPROVEN NON-HALTING CONJECTURE** (Not formally verified in Rocq).

> [!WARNING] EPISTEMIC STATUS: PROOF SKETCH ONLY — NOT A PROVEN THEOREM
> This document records empirical pattern observations ($n=1 \dots 20$) and an informal proof sketch.
> It does **NOT** constitute a machine-checked proof in Rocq or Lean.
> The universal induction step $C_n \to C_{n+1}$ has **not** been formalized for arbitrary $n$, and State 31 is statically graph-reachable ($0 \to 45 \to 34 \to 31$).

---

## 1. Known Formal Gaps (Why This Is Not a Proof)

1. **Finite Verification vs. Universal Induction:**
   The milestone recurrence $c_0(n) = -14 - n$ and $P(n) = 1 + \frac{n(n+1)}{2}$ has only been verified by finite simulation through $n = 20$ (1,488,400 steps). Stating "by mathematical induction" without a formalized proof in Rocq of the universal macro-step $\forall n, C_n \xrightarrow{k_n} C_{n+1}$ is mathematically invalid.

2. **Graph Reachability of State 31 (`S32`):**
   State 31 (`S32`) is not statically isolated. The state transition graph contains the path:
   $$\text{State } 0 \xrightarrow{\delta(0, \_)} \text{State } 45 \xrightarrow{\delta(45, \_)} \dots \to \text{State } 34 \xrightarrow{\delta(34, \_)} \text{State } 31$$
   The assertion that State 34 never reads `0` relies on an assumed tape invariant that has not been proved by induction over arbitrary steps. Finite sampling ("0 visits in $10^6$ steps") is empirical evidence, not a formal invariant.

3. **No Rocq Formalization of the Macro-Cycle:**
   The existing Rocq file [`rocq/gemini_epsilon1_tm_48s_v2_fix.v`](file:///C:/Users/Rowan/Documents/st/bbwork/rocq/gemini_epsilon1_tm_48s_v2_fix.v) proves only finite bootstrap milestones (`boot_352`, `boot_702`, `boot_1641`) and conditional lower bounds. There is no Rocq theorem proving non-halting (`~ halts tm blank_cfg`) or establishing the inductive invariant for $C_n$.

---

## 2. Empirical Halt Gate Analysis (Finite Behavior)

The 96-transition table contains two transitions to `Halt`:

| State | Read Symbol | Write | Direction | Target | Status in First 2,000,000 Steps |
|---|---|---|---|---|---|
| `0` (`S01`) | `1` | `_` (0) | R | `Halt` | Reads `0` on all 163 visits; 0 visits reading `1`. |
| `31` (`S32`) | `_` (0) | `_` (0) | R | `Halt` | Not visited in first 2,000,000 steps. |

### Empirical Observation on State 34:
In the first 2,000,000 steps, State 34 is visited 163 times during the scan phase, and in all 163 cases it reads `1` ($\delta(34, 1) = (1, \text{R}, 35)$). It has not been observed reading `0`. However, proving that it *can never* read `0` for any $n > 20$ remains an open problem requiring full inductive tape verification.

---

## 3. Empirical Recurrence Data ($n = 1 \dots 20$)

During blank-tape simulation, the machine repeatedly enters scan state `1` (`S02`) at configurations matching the structural form of `cfg_worm`:

| Stage $n$ | Step Count | Measured $c_0$ | Formula $-14-n$ | Measured Pairs | Formula $1 + \frac{n(n+1)}{2}$ | Match? |
|---|---|---|---|---|---|---|
| $n = 1$ | 349 | -15 | -15 | 2 | 2 | Yes |
| $n = 2$ | 699 | -16 | -16 | 4 | 4 | Yes |
| $n = 3$ | 1,638 | -17 | -17 | 7 | 7 | Yes |
| $n = 4$ | 3,895 | -18 | -18 | 11 | 11 | Yes |
| $n = 5$ | 8,067 | -19 | -19 | 16 | 16 | Yes |
| $n = 6$ | 15,152 | -20 | -20 | 22 | 22 | Yes |
| $n = 7$ | 26,925 | -21 | -21 | 29 | 29 | Yes |
| $n = 8$ | 44,559 | -22 | -22 | 37 | 37 | Yes |
| $n = 9$ | 70,565 | -23 | -23 | 46 | 46 | Yes |
| $n = 10$ | 105,098 | -24 | -24 | 56 | 56 | Yes |
| $n = 15$ | 494,304 | -29 | -29 | 121 | 121 | Yes |
| $n = 20$ | 1,488,400 | -34 | -34 | 211 | 211 | Yes |

---

## 4. Summary & Verification Status

* **Status:** **Empirical pattern / Unproved conjecture.**
* The machine demonstrates strong empirical evidence of an infinite polynomial oscillator ($T(n) \approx O(n^4)$), but **no formal non-halting proof exists** in Rocq or Lean.
* The claim of unconditional non-halting is retracted to an open conjecture backed by finite simulation up to step 2,000,000.
