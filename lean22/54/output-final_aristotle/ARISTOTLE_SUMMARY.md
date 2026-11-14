# Summary of changes for run 9b6a3b43-d83e-49bc-93ce-515411b7b962
The proof is correct, and I've cut the project down to only what the non-halting proof needs. I kept it in Lean and did not port it to Rocq, as you asked.

**Checking the original proof**
- The original project built cleanly with no `sorry`.
- `not_halts_init : ¬ Halts init` used only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- I compared the transition table in the code against `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB` entry by entry. It matches, and so do the step rule (moving left and right on a blank-extended tape), the start configuration (state A, blank tape) and the definitions of `Reaches` and `Halts`.
- I also read the main argument; it holds up. After 681 steps (checked by kernel computation) and 41 macro steps (each covered by a correctness proof, with the chain checked by kernel computation), the machine reaches a loop configuration. From there, `loop_not_halts` shows each cycle only makes the run of 2s one longer, so the machine never halts.

**What changed**
- **Only the needed code is left.** I traced which declarations `not_halts_init` actually uses and deleted everything else. That includes the side results that verified other parts of your description but aren't needed for non-halting: the blocked and aligned cycle theorems, the absorption rules, the odd-cycle rule and the halting mechanism. The Lean code went from 11 files and about 1,900 lines to 4 files and about 1,250 lines. These results are still in the git history.
- **No Mathlib.** The project now needs only the Lean toolchain. `Reaches` is now its own two-rule definition (reflexive-transitive closure of `step`), and I rewrote the proofs without Mathlib tactics. A build from scratch now takes about 10 seconds, instead of first downloading and building Mathlib.
- **Rechecked.** After these changes, `lake build` succeeds with no errors or warnings. There is no `sorry` or axiom declaration in the project, and `not_halts_init` still uses only the same three standard axioms.

**What's left in the project**
- `RequestProject/Machine.lean` has the entire statement you need to trust: the transition table, `step`, `Reaches`, `Halts` and `init`, plus the basic sweep lemmas.
- `RequestProject/Cycles.lean` has the binary and ternary encodings and the individual moves within a cycle.
- `RequestProject/Macro.lean` has the carry rules for cell pairs, `carryF`, and the proof that the macro step is correct (`macroStep_sound`).
- `RequestProject/NonHalt.lean` has the loop argument, the concrete run and `not_halts_init`.
- `RequestProject.lean`, `lakefile.toml`, `lake-manifest.json` (now with no dependencies) and `lean-toolchain` are the build files.
- `README.md` now has a short proof outline and a file map. I removed `ANALYSIS.md`, since it described the deleted results, and left `ARISTOTLE_SUMMARY.md` unchanged.

The Properties table now lists only the main theorem, the loop theorem, the macro-step correctness theorem and the definitions they're stated in, all pointing to the new files.

# Summary of changes for run ca4ede97-582d-4f49-bdf1-b702fd1cca39
I proved in Lean that `1RB2LA0RB---4LA_1LA3LA1RA4RA1LB` never halts from the blank tape (`not_halts_init : ¬ Halts init` in `RequestProject/NonHalt.lean`). The whole project builds with no `sorry`, and the proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. `ANALYSIS.md` Section 5 has the full write-up.

**Odd `p`, now proved** (`OddCycle.lean`, `odd_cycle_absorb`)
- The odd-`p` rule that was only simulated before is now a theorem: for `p = 2r+3`, if the digits after the aligned cycle are `2^k 0 rest`, then five cycles later the zone of 2s has `2(p+4+k)` cells.
- In the counter `4 | rest`, `rest` has received `2^k·(2^(p+2)-2)/3` increments.
- The five cycles are: an offset count, a blocked cycle, an even aligned cycle in which the offset counter absorbs every carry, an absorbing misaligned count, and a blocked cycle.

**The "offset counter", in counter terms** (`MacroCarry.lean`)
When the ternary counter is read with the wrong parity, its cells pair up into a small set of pair types. Each reacts to a carry in a fixed way, and each rule is proved:

| pair | effect of a carry |
|---|---|
| `24`, `11`, `21` | ordinary ternary digits 0, 1, 2 |
| `12` | takes one carry and becomes `22` |
| `22` | passes every carry on twice (a doubler) |
| a pair starting with `4` | a wall: carries are lost |
| blank | behaves like endless digits 1 |

`carryF` computes `N` carries at once by arithmetic, and `carryF_sound` proves it matches the machine.

**Fast simulator with a correctness proof** (`MacroStep.lean`)
- `macroStep` jumps from one event to the next by counter arithmetic. This covers both odd `p` and a 1 at the bottom of the counter.
- `macroStep_sound` proves that the machine really reaches each computed event.
- It returns "unknown" only in the two situations that can lead to halting (see below).

**Why it never halts** (`NonHalt.lean`)
1. After 681 steps the machine is at 13 twos followed by `4 | 24 21 21`.
2. After 41 more macro steps (`run_macro41`, checked by kernel computation, with counts up to about `2^50`) it is at 100 twos, then `1 1 2222 4`, then an ordinary 26-digit ternary counter.
3. `loop_not_halts` covers every configuration of the form "`2n` twos, then `1 1 2^a 4`, then an ordinary ternary counter" with `n = 6s+2`. Each cycle sends `1 + (2^n-4)/6` carries rightward:
   - The first carry turns the leading `12` into a doubler.
   - Every later carry is doubled and then hits either a wall (lost) or a `24` digit.
   - That digit receives a multiple of 3 carries because `2^n ≡ 4 (mod 18)`, so it stays `24`.
   - The binary counter overflows the same way each time. The run of 2s grows by one per cycle, the binary counter never gets longer, and nothing ever reaches the end of the tape.
4. Because the machine is deterministic, this means it never halts.

**How halting can happen**
In the fast simulator there are only two routes to a halt:
- **No blocking 0:** a misaligned cycle absorbs the whole counter and runs into blank tape. `even_cycle_halts` is the proved case.
- **Parity mismatch at the end:** an offset counter's parity doesn't match the end of the tape, so a carry reaches a single last cell and writes the `3` that halts the machine. This explains your halting examples where a 0 was still present.

What is proved here is that the simulator is correct whenever it returns a result. That these two routes always end in a halt was only seen in simulation, not proved. So I haven't proved an exact halting criterion for arbitrary starting tapes. For the blank-tape run the question is settled: the run enters the loop above and provably never halts.

The Properties table has the new results: `not-halts-init`, `loop-not-halts`, `macro-step-sound` and `odd-cycle-absorb`.

# Summary of changes for run 1c28dcf2-87a0-4a18-84eb-b10bac8fdfdc
Your analysis holds up, and I turned its main parts into Lean theorems in `RequestProject/`. The build passes with no `sorry` and only the standard axioms. I did not prove whether the machine halts from the blank tape. `ANALYSIS.md` has the full write-up.

**Exact encodings behind your description**
- **Binary counter:** cells come in pairs, with the lowest bit at the right end. Bit 0 is the pair `10` and bit 1 is `11`. The leftward A sweep carries by turning `11` into `22`, stops at the first `10`, and the rightward sweep turns the `22`s back into `10`.
- **Ternary counter:** the lowest digit is at the left end. Digit 0 is `24`, digit 1 is `11` and digit 2 is `21`. The lowest digit is a single cell: `4` for 0, `1` for 1, and `3` only briefly during a carry.
- **Blank tape:** past the end of the ternary counter, blank cells act like an endless run of digit 1s, so a carry into them writes `21`.
- **Halting:** the machine halts only when state A reads a `3` (`step_eq_none_iff`).

Below, "`2p` twos" means the run of 2s between the left end and the ternary counter.

**Proved results**
1. **Blocked cycle** (`blocked_cycle`): with an odd number `2p+1` of 2s followed by a `4`, the binary counter runs through all `2^p` values without ever getting past the `4`. On overflow the parity flips and the rest of the tape is unchanged. This confirms that in a misaligned cycle a digit 0 stops everything to its right.
2. **Aligned cycle** (`aligned_cycle_odd`, `aligned_cycle_even`): starting from `2p` twos and a ternary counter whose lowest cell is `4`, one full binary cycle adds exactly `2^(p-1)` to the ternary counter when `p` is odd, and `2^(p-1) - 1` when `p` is even. In each round the binary counter gains 6 while the ternary counter gains 3. The two parities also end in different configurations.
3. **Absorption** (`even_cycle_then_absorb`): after an even-`p` aligned cycle, suppose the digits are `2…2 0 rest`. The next misaligned cycle does not skip the 2s. It absorbs them, together with the lowest cell, into the binary counter as extra bits, then is blocked by the 0. The part after that 0 becomes the new aligned counter, and the run of 2s grows to `2(p+k+2)` cells, where `k` is the number of 2s absorbed. This is the precise form of "the next part gets aligned again".
4. **Halting** (`even_cycle_halts`): if, after an even-`p` aligned cycle, every digit is 2 (no 0), the next cycle absorbs the whole counter, leaves a `3` in the blank area, and the machine halts. This proves your halting mechanism, but only for `p` even with all digits 2.
5. **Link to the real run** (`init_reaches_after_first_cycles`): from the blank tape the machine reaches this regime after 681 steps (checked by kernel computation). It then does a blocked cycle and an aligned cycle with `p = 7`, which adds 64 to the ternary counter. The result matches direct simulation at step 1957.

**Simulation only, not proved**
- **Odd-`p` rule:** a rule for what follows an odd-`p` aligned cycle whose digits are `2^k 0 rest` matched in 96 random cases. The run of 2s grows to `2(p+4+k)` and `rest` receives `2^k·(2^(p+2)-2)/3` increments.
- **Lowest non-2 digit equal to 1:** this is your offset-counter regime. The tape develops patterns that are not clean ternary digits, and small cases sometimes halt a cycle or two later even though a 0 is present. I have not characterised this case, and most of the real run's later cycles fall into it.
- **Long run:** direct simulation went 3·10^10 steps without halting.
- **Heuristic:** the machine probably never halts, but this is only a probability-style guess.