# Holdout 118184 — halving-kernel probe (2026-11-10)

Machine: `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` (BB(6) holdout 118184).
Upstream repository clone: `bbwork/.tmp_rwst/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
(commit `a9581b9`). The upstream `halving_loop.lean` is unmodified.

## What is already proved upstream

`halving_loop.lean` proves, axiom-free and without `sorry`:

* `halving_round`: for odd `c ≥ 5`,
  `M([], c, d::R') ↦ M([], (c-1)/2, 1 :: (d + (c-1)/2) :: R')`, so `c + 1` halves
  at every round while `c` stays odd;
* `doom_mersenne`: `M([], 2^v - 1, d::R')` halts for every `v ≥ 2`
  (the `v = 2` case is `M([], 3, _)`, which halts in 31 raw steps);
* `never_halts_iff_kernel`: non-halting is **equivalent** to

  ```lean
  HalvingKernel :=
    ∀ c R, OrbitReachable (.M [] c R) → c % 2 = 1 → ¬ IsPow2 (c + 1)
  ```

`reach_M_nil_3` (the `M([], 3, R)` unreachability axiom, "R1") remains the only
custom axiom. Because of the equivalence, no proof of non-halting can avoid the
kernel: the kernel is not a stepping stone, it is the halting statement in
disguise.

## Probe

`era-sim` (the Rust port of `macro_sim.py` in the clone) was instrumented with a
`--halving-log` option that records every left-empty config `M([], c, R)` with
odd `c` — i.e. every entry into a halving chain. Each record carries the macro
step, raw step, era, `c`, `ν₂(c+1)`, the odd part of `c+1`, and the head/length/
sum of `R`.

| run | macro steps | raw steps | entries | max `c` |
|---|---|---|---|---|
| A | 1.0 × 10⁹ | 5.76 × 10¹³ | 5 284 | 195 509 |
| B | stopped early | — | 29 337 | 1 256 909 |

Run B was stopped deliberately: per-entry cost grows with era size, and 29 K
entries already determine the distribution (run A matches it to two decimals).

Analyzer: `era-sim/halving_analyze.py`. Logs: `era-sim/hv1e9.jsonl`,
`era-sim/hv1e11.jsonl`.

## Result: no modular obstruction

* `ν₂(c+1)` is exactly geometric over 29 337 entries:
  49.96 % / 24.71 % / 12.50 % / 6.21 % / 3.18 % / 1.64 % / 0.86 % / 0.43 % /
  0.24 % / 0.14 % / 0.07 % / 0.03 % / 0.01 % / 0.01 % / 0.00 % for
  `ν₂ = 1 … 15`. This is the distribution of a random even integer, to the
  measured precision.
* **Zero** entries have `c + 1` a power of two (the kernel holds on the sample).
  The smallest odd part seen is 3, never 1.
* The odd part of `c + 1` realises **every** residue class modulo
  3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 25, 31, 33, 35 — in particular the class
  `1`, which any power of two would have to occupy for some modulus. So no
  congruence on the odd part can exclude powers of two.
* For every modulus `M ∈ {3, 5, 7, 9, 11, 13, 15, 17, 31, 33, 63, 65, 127, 129}`
  the set of observed entry cursors `c mod M` intersects the Mersenne residue
  set `{2^v − 1 mod M}`. So no congruence on the cursor itself separates the
  orbit from the halting diagonal either.

## Conclusion

The reduction in `halving_loop.lean` is correct and sharp, but it does not make
R1 easier: it identifies R1 with a Collatz-style statement about the whole
orbit, and the orbit is 2-adically equidistributed at every scale we can
measure. Any proof must use more than finite congruence data — it needs a
genuine invariant of the era dynamics, not a residue class. R1 therefore stays
open, and this file records the negative result rather than a solution.

The same probe makes the earlier `ν₂ ≤ 11` remark quantitative: `ν₂` reaches 15
by `c ≈ 1.26 × 10⁶`, with the geometric tail intact, so any "bounded ν₂" route
is refuted.

## Reproduce

```sh
cd bbwork/.tmp_rwst/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/era-sim
cargo build --release
./target/release/era-sim.exe -n 1000000000 --halving-log hv1e9.jsonl
python halving_analyze.py hv1e9.jsonl
```

The probe is local to the clone (`src/main.rs` gained `--halving-log`,
`halving_analyze.py` is new); nothing upstream was changed and nothing here is
committed.
