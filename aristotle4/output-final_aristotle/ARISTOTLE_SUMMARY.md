# Summary of changes for run bde2dda3-12bc-4bcb-8fbb-5b905412b852
I found the archive and picked up the work on the Turing machine `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`, started on a blank tape. **I could not settle whether it halts.** Simulation suggests it never halts, but I have no proof either way. The full project builds with `lake build` and contains no `sorry`.

**Lean results (all proved and built):**
- **GPT's two drafts now compile.** These are `tm_mixed_radix_result/RequestProject/MixedRadix.lean` and `tm_overflow_progress/RequestProject/Overflow.lean`. I repaired a few small proof steps and left every statement unchanged. This proves two of GPT's results:
  - `mrAdd_single_sound`: GPT's single-carry shortcut always matches what the machine actually does.
  - `productive_return`: once the tape is in GPT's "productive" form, it keeps coming back to that form. This does not show that the blank-tape run ever reaches that form.
- **`Accel/Exhaust.lean`, `exh_spec`:** a formal version of GPT's "exhaustion normal form". For any token word it gives the exact number of returns, the word left behind, and the step count.
- **`Accel/Drain.lean`, `drain`:** GPT's "physical event theorem", proved with exact step counts. It describes how the base-3 counter absorbs a token word.
- **`Accel/Sim.lean`:** a fast simulator built on these rules, with `runAccel_sound` proving it agrees with the real machine.
- **`Accel/Bound.lean`, `not_halted_within_ten_pow_thousand`:** the machine does not halt within its first \(10^{1000}\) steps. This relies on `native_decide`, which means trusting Lean's compiler, and takes about 70 s to build. I also ran the proved simulator to \(10^{3000}\) steps without a halt, but that is not stated as a theorem.

**Fast C simulators (not proved in Lean):** `tools/fastsim.c` and `tools/fastsim2.c` (the second also speeds up the main counter). Build with `gcc -O2 -o fastsim fastsim.c -l:libgmp.so.10`.
- **Checks:** they match step-by-step simulation at \(10^8\) and \(10^9\) steps and GPT's Python event machine at about \(10^{300}\). The two programs agree with each other at \(10^{3000}\) and \(10^{10000}\), and they match GPT's checkpoint at \(10^{1000}\).
- **Reach:** no halt within \(10^{100000}\) steps (about 88 minutes). Logs are in `tools/runs/`.

**What the runs show:** the tape is a dense base-3 counter plus a sparse region to its right. Up to \(10^{60000}\) steps, only 21 carry chains reached into the counter, and none went deeper than 9 digits. The counter is about 126k–210k digits wide.

The full write-up is in `TM_PROGRESS.md`: GPT checks, Lean results, simulation table, structural observations, the heuristic case for non-halting, and possible next steps. One next step is a simulator that also compresses repeated blocks in the right-hand region, which might reach around \(10^{10^6}\) steps.

# Summary of changes for run 95e44066-f530-4df3-bb71-2b792f677e18
I can see your project. You asked what I see, so I only looked around: I didn't change, build or verify anything.

**What's in the project**
- It's a Lean 4 project named `RequestProject`, using Mathlib `v4.28.0`. The `lakefile.toml` sets up two libraries, `tm_mixed_radix_result` and `tm_overflow_progress`. Git history has just one commit ("Initial commit").
- Both folders are about the same Turing machine: the 2-state, 5-symbol machine `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`, started on a blank tape.
- **`tm_mixed_radix_result/`** has `RequestProject/MixedRadix.lean` (243 lines), which sets out "return excursion" rules such as \(F(42x)=44x\), \(F(44x)=42F(x)\) and \(F(2x)=2F(F(F(x)))\). It also has Python and C++ programs that speed up the simulation, saved checkpoints and a `RESULTS.md`. Its README says the machine runs exactly \(10^{100}\) steps without halting.
- **`tm_overflow_progress/`** has `RequestProject/Overflow.lean` (269 lines), with rules for overflow and boundary entry and a family of "productive tails". It also has Python and C++ tools and checkpoints up to \(10^{1000}\) steps.
- Neither README claims to decide whether the machine halts from a blank tape. Both say the Lean files are **uncompiled drafts**.

**Problems I noticed**
- **Both Lean files will fail to build as they stand.** Each starts with `import RequestProject.Macro`, but that file isn't in the project; it seems to come from an earlier project that wasn't uploaded. That earlier project is also missing from the build setup.
- Neither Lean file contains `sorry`. That doesn't show they're complete, because they have never been compiled.
- The step counts (\(10^{100}\), \(10^{1000}\)) come from your Python and C++ runs. Lean hasn't checked them.

**What I'd need to go further**
If you want me to compile and check these files, or prove the rules they state, please upload the missing `RequestProject/Macro.lean` and anything it depends on.