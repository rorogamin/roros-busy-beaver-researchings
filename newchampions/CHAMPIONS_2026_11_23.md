> **RETRACTED 2026-11-23.** The 38 machines below are kernel-verified halting
> proofs, but most are *not* champions: the bbchallenge Champions table lists a
> stronger machine for their cell. See `WIKI_CROSSCHECK_2026_11_23.md` for the
> cell-by-cell comparison and the 9 machines that do beat the record.

# Busy Beaver Champions — 2026-11-23 batch

38 machines, each one an exact blank-tape bootstrap into a proven Busy Beaver core, with a kernel-checked Lean 4 certificate.

## Method

1. Every core in `search/bbcores_plus.txt` (96 cores, up to `fe1_8` = f_{ε₁}) was run against every reachable `(states, symbols)` cell with `bbsearch_mc`, 4 strongest-fitting cores per cell, 1.2e8-step budget, 20,000-cell tape cap.
2. A hit is kept only if the exact Python mirror of `BB/TM.lean` reproduces the landed landmark, every state and every symbol occurs in the run (irreducibility), and the machine survives 5,000 steps past the landmark.
3. A cell is claimed only if it is empty in the 51-machine Nov 21 batch and the Rocq `BB<n>_<m>.v` corpus, or if the new bound is strictly higher in the ordinal hierarchy.

## Champions

| cell | bound | core | landmark step |
|---|---|---|---|
| **BB(7,3)** | `> f_{ω+1}(3)` | `fw1_3` | 752 |
| **BB(10,3)** | `> f_{ω}(14)` | `fw_3` | 313 |
| **BB(11,3)** | `> f_{ω}(18)` | `fw_3` | 1003 |
| **BB(12,3)** | `> f_{ω}(12)` | `fw_3` | 418 |
| **BB(13,3)** | `> f_{ω}(14)` | `fw_3` | 626 |
| **BB(14,3)** | `> f_{ω×2}(1)` | `fwm2_3` | 124 |
| **BB(15,3)** | `> f_{ω}(18)` | `fw_3` | 988 |
| **BB(3,4)** | `> f_{ω}(3)` | `fw_4` | 241 |
| **BB(4,4)** | `> f_{ω}(1)` | `fw_4` | 374 |
| **BB(5,4)** | `> f_{ω+1}(13)` | `fw1_4` | 236 |
| **BB(6,4)** | `> f_{ω+1}(1)` | `fw1_4` | 210 |
| **BB(7,4)** | `> f_{ω+3}(1)` | `fw3_4` | 68 |
| **BB(8,4)** | `> f_{ω×2}(1)` | `fwm2_3` | 90 |
| **BB(9,4)** | `> f_{ω^2}(4)` | `fwp2_4` | 23 |
| **BB(11,4)** | `> f_{ω^2+2}(1)` | `fwp22_4` | 13 |
| **BB(19,4)** | `> f_{ω^2+6}(1)` | `fwp26_4` | 72 |
| **BB(20,4)** | `> f_{ω^2+5}(1)` | `fwp25_4` | 141 |
| **BB(21,4)** | `> f_{ω^2+4}(2)` | `fwp24_4` | 254 |
| **BB(3,5)** | `> f_{ω}(2)` | `fw_4` | 263 |
| **BB(4,5)** | `> f_{ω+1}(3)` | `fw1_4` | 308 |
| **BB(5,5)** | `> f_{ω+2}(3)` | `fw2_5` | 50 |
| **BB(6,5)** | `> f_{ω×2}(2)` | `fwm2_5` | 131 |
| **BB(8,5)** | `> f_{ω×2+1}(2)` | `fwm21_5` | 82 |
| **BB(9,5)** | `> f_{ω×2+1}(1)` | `fwm21_5` | 124 |
| **BB(10,5)** | `> f_{ω^2+2}(1)` | `fwp22_5_sw` | 51 |
| **BB(12,5)** | `> f_{ω^ω}(4)` | `fwpw_5` | 125 |
| **BB(4,6)** | `> f_{ω+1}(1)` | `fw1_4` | 317 |
| **BB(5,6)** | `> f_{ω+2}(1)` | `fw2_5` | 17045 |
| **BB(8,6)** | `> f_{ω^2+1}(2)` | `fwp21_6` | 222 |
| **BB(10,6)** | `> f_{ω^2+2}(2)` | `fwp22_5_sw` | 185 |
| **BB(11,6)** | `> f_{ω^2+2}(1)` | `fwp22_5_sw` | 204 |
| **BB(18,6)** | `> f_{ω^ω+3}(1)` | `fwpw3_6` | 602 |
| **BB(3,7)** | `> f_{ω+1}(14)` | `fw1_6` | 312 |
| **BB(4,7)** | `> f_{ω+3}(2)` | `fw3_7` | 108 |
| **BB(5,7)** | `> f_{ω×2+1}(2)` | `fwm21_7` | 56 |
| **BB(6,8)** | `> f_{ω×2+1}(1)` | `fwm21_8_blank` | 131 |
| **BB(6,9)** | `> f_{ω×2+1}(2)` | `fwm21_8_blank` | 182 |
| **BB(9,9)** | `> f_{ω^ω}(32)` | `fwpw_8_blank` | 1529 |

## Certificates

Each machine has, in `lean/BB/Champions2026_11_23_S<m>.lean`:

- `tm_<n>_<m> : TM` — the exact transition table;
- `valid_<n>_<m> : ValidTM <n> <m> tm_<n>_<m>` — every write and target state is in range and everything outside the domain is `none`;
- `landmark_<n>_<m> : Config` and `reaches_landmark_<n>_<m> : steps tm <n>_<m> K initConfig = some landmark_<n>_<m>` — exact `K`-step execution from the blank tape, proved by 35-step `rfl` chunks glued with `steps_add`, the same structure as the Nov 21 batch.

The reach theorem is what turns the machine into a champion: the landmark is the input configuration of the core, so the core's halting theorem (`Fe1_6_halts`, `Fe1_7_halts`, `Fe1_8_halts`, `Fwpw_*`, `Fwp2_*`, …) applies and gives `HaltsIn tm ... t` with `t` above the stated ordinal bound. The bound column is that core bound evaluated at the landmark counters.

## Verification

- `verify_champions_2026_11_23.py` re-simulates every machine from `0^inf A> 0^inf`, checks the exact landmark, 5,000 post-landmark steps, irreducibility, and cell disjointness against the Nov 21 batch.
- Every Lean module compiles with `lean -j 1 -M 4096`, and every theorem is `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no `native_decide`).

## Caveat

The Lean certificate proves the machine is a valid n×m machine and reaches the core landmark in exactly K steps. The *halting* and the ordinal lower bound follow from the core theorem, whose formal proof lives in the Rocq `Fe1.v` / `Fwpw_*.v` / `Fwp2_*.v` files; those theorems are parameterized by a core-containment predicate, so a machine whose landmark carries extra non-blank tape beyond the matched prefix needs the core predicate checked for that exact tape before the composition is formal end-to-end.
