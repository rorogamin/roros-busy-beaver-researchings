# Summary of changes for run fc1e5c4e-1c84-4600-bb32-b1eb0ee75012
**The machine `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---` halts, and this is proved in Lean.** The theorem is `BCM.halts : BCM.Halts` in `RequestProject/Halt/Verified.lean`. `#print axioms` gives `propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler`. The last two come from a single `native_decide` check (about 80 s), so the Lean compiler is trusted for this one theorem. All other results use only the standard axioms. The project builds with no `sorry`, no new axioms and no `implemented_by`. `ANALYSIS.md` is the full write-up.

I could download your two linked projects and followed their method.

**Removing the bouncer (`Wall.lean`, proved).** The left half of the tape is a wall that gains one `144` block every five visits. It has five phases, with excursions of 10n+1, 1, 10n+3, 1 and 10n+9 steps. `wall_excursion` proves that each excursion never reads the right half and returns the head to cell 0 in states B, A, B, A, B. So cell 0 receives the input stream `A (BABAB)^ω`.

**Reduction to the counter (`Cascade.lean`, `Levels.lean`, proved).**
- Every cell to the right is the same small transducer, `cell1`.
- `halts_iff`: the machine halts iff this chain of transducers halts on some finite prefix of the input stream.
- `cellDies_blank_iff`: a blank cell halts exactly when its input word begins with `BABA`.
- `not_halts_of_no_BABA` (the non-halting criterion) and `halts_of_BABA` (the converse, which needs the extra condition that the chain dies out) turn this into a statement about the machine.

**The chaotic counter (`Counter.lean`, proved).**
- **Digit encoding:** once a cell has visited its right neighbour it holds 1, 2 or 3 forever and can never halt. It acts as one binary digit: 2 is 0, 1 and 3 are a 1 in two colours. A is an increment.
- **B signal:** a B at 0 passes on "BA". At a 1 it flips the colour, and it sends an A (a carry) when it flips colour b back to colour a.
- `phase_law`: the digit is the parity of the number of A's read. B's and colours never change it.
- `token_zero` / `token_one`: cut the input at its A's into pieces B^r A. A 0-digit turns B^r A into (BA)^r. A 1-digit turns B^s A into A^(s/2) followed by A if s is even, B if s is odd. The parity of the B-runs is the only source of chaos.
- `BABA_preimage`: the next cell halts iff this cell's input begins with ABBAAA, ABBAABB, BBBBAAA or BBBBAABB.

**Numerical findings (C/Python, not proved in Lean).**
- **Period law:** if a cell's repeating block has an odd number of A's, the next cell's block covers two copies of it; if even, one copy. I have exact length formulas, checked for cells 0–54.
- **Unlike your other counter machine**, the parity of A's is not preserved (92 odd vs 79 even over cells 0–170). The block length therefore performs a multiplicative random walk, growing about 1.13× per cell on average.
- **The halt:** exact words of cells 0–170 contain no halt. Streaming them upward from cells 160, 165 and 170 always gives the same halt: cell 237 receives `ABBAABB`, so cell 238 receives `BABA`. Earlier near misses were cells 12, 212, 235 and 86, 95.
- **Halting time:** about 5.6·10^53 steps. This is an estimate only.

**The Lean halting proof.** I adapted the verified engine from your `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` project. The soundness proofs carried over with small edits. `HaltEngine.check 170 1 80 524288` computes the exact word of cell 170 (a block of 3,831,101,441 letters) and streams it through cells 170–249. It finds a halt before the halting cell sends anything onward, which is what the soundness theorem `Eng.halts_of_check` needs to conclude `Halts`.

**Files:** the exploration code and its output are in `tools/` (not verified; see `tools/README.md`). The engine is in `HaltEngine.lean`, compiled natively via a second library entry in `lakefile.toml`. `lake build` builds everything; `RequestProject.Halt.Verified` takes about 1.5 minutes and the other modules take seconds.