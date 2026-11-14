# CET(3) `residue_s18.txt` Analysis & Rocq Verification Report

## 1. Dataset Overview
- **Input**: `bb-variants/CET/s18/residue_s18.txt` — **19,000** unique CET(3) holdout pairs (`2,560` with `---` entries, `16,440` complete tables).
- **Distinct agents**: `4,912` distinct Agent 1 tables and `3,082` distinct Agent 2 tables.
- **Model**: Standard Catch-Em-Turing `CET(3)` partial semantics (bi-infinite all-`0` tape, Agent 1 at `0` in `StA`, Agent 2 at `2` in `StA`, simultaneous read before write, Agent 1 write priority on same cell, halt only on `pos1' = pos2'`, `---` undefined).

## 2. 2,000,000-Step Simulation & Structural Classification
Running `solve_pass1.exe` for `2,000,000` steps on `[-524288, +524287]` across all `19,000` holdouts yielded:
- **Halted (`<= 2,000,000` steps)**: `0`
- **Undefined `---` (`<= 2,000,000` steps)**: `0`
- **Escaped / OOB (`|pos| >= 524,288` within 2M steps)**: `1,192`
  - `617` are already disjoint after `t = 10,000` (`max_p1 < min_p2`, e.g. `#347` and `#348` where Agent 1 escapes left in a translated cycle and Agent 2 is in a period-`6144` fixed cycle).
  - `575` remain in `oob_rem.txt`, of which `18` have both heads escaping together (`|p1 - p2| < 200`).
- **Bounded within `[-524288, +524287]` at 2M steps**: `17,808`
  - `< 30` cells: `221`
  - `30–99` cells: `910`
  - `100–499` cells: `107`
  - `500–4999` cells: `11,843` (quadratic bouncers / bells)
  - `>= 5000` cells: `4,727`

Testing all `1,131` small-width (`< 100` cells) machines with `check_small_cycles.exe` up to `2,000,000` steps found **0 fixed cycles**—all `1,131` are logarithmic-growth binary counters (or separated counter + other), grouped into `500` distinct Agent 1 tables and `332` distinct Agent 2 tables.

## 3. Rocq Verification Infrastructure (`CET3_Cert.v`)
`bb-variants/CET/s18/CET3_Cert.v` compiles cleanly with `coqc` (Rocq 9.1) with **zero axioms and zero admits**, providing:
1. Exact partial CET(3) semantics (`step_opt`, `step_res`, `run_N_opt`, `never_halts`, `halts_at_exact`, `hits_undef_at`).
2. Fast radix-2 binary tree tape (`btree`) proved equivalent to `Tape := Z -> bool` (`run_N_fast_equiv`).
3. Formally proved certificate checkers:
   - `check_halt_cert_sound`
   - `check_undef_cert_sound`
   - `check_joint_cycle_cert_sound` (handles both fixed `dx = 0` and translated `dx != 0` cycles with exact read-window bounds and outside-window blankness).
