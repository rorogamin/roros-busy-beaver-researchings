# CET(4) Pentational (`f_3`) Machine — Design & Roadmap

## Goal
Construct an explicit `CET(4)` machine (2 agents, 4 states each, 2 symbols) that:
1. Halts by exact first head collision (`pos1 = pos2`) in **pentational** (`> 10 ↑↑↑ 3`, `f_3`-level) steps.
2. Is formally verified in Rocq 9.1 with zero axioms/admits (`Print Assumptions` closed), satisfying `AGENTS.md`.

## Architecture: Tetrational Inner Engine (`ag1`) + Outer Glider (`ag2`)
- **Agent 1 (4 states, 2 symbols)**: A `L -> 2↑↑L` (or `L -> 2^(2^L)`) inner engine.
  - Given a tape block of width `L`, `ag1` runs for `>= 2↑↑L` steps before exiting rightward.
- **Agent 2 (4 states, 2 symbols)**: A `P, D, M` glider that bounces `ag1` back `R >= 3` times.
  - Round 1: `L_1` -> `L_2 >= 2↑↑L_1`
  - Round 2: `L_2` -> `L_3 >= 2↑↑L_2 >= 2↑↑(2↑↑L_1)`
  - Round 3+: `HALT` at `> 10 ↑↑↑ 3` steps.

## Phases
1. **Phase 1 (Current)**: Construct or search for a 4-state, 2-symbol `ag1` with `>= 2^(2^L)` or `2↑↑L` growth on `1^L`.
2. **Phase 2**: Pair `ag1` with a 4-state `ag2` glider and verify `R >= 3` rounds + `HALT` in Python.
3. **Phase 3**: Formalize the `CET(4)` halting proof in Rocq 9.1.
