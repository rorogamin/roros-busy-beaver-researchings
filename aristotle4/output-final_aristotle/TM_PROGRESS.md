# `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA` from the blank tape: progress report

**Halting is still open.** Nothing here proves that the machine halts, or that it
runs forever. This report covers what was checked, what is now proved in Lean,
and what the faster simulations show.

## 1. Project layout

| Path | Contents | Status |
|---|---|---|
| `RequestProject/` | The earlier Lean development, unpacked from the archive (`Machine`, `Counter`, `Macro`, `RoundTrip`, `Binary`, `Pass`, `Shield`, `Frontier`) | builds, no `sorry` |
| `aristotle_archive/` | The archived `ANALYSIS.md`, earlier summaries, and helper-tool sources | documentation / unverified tools |
| `tm_mixed_radix_result/`, `tm_overflow_progress/` | GPT's two packages | Lean files now **compile** (see §2) |
| `Accel/Exhaust.lean` | Exhaustion normal form of token words (`exh_spec`) | proved |
| `Accel/Drain.lean` | Counter-driven drain with exact step count (`drain`) | proved |
| `Accel/Sim.lean` | Certified accelerated simulator (`runAccel`, `runAccel_sound`) | proved |
| `Accel/Bound.lean` | `not_halted_within_ten_pow_thousand` | proved (uses `native_decide`) |
| `tools/fastsim.c`, `tools/fastsim2.c` | Fast exact C simulators (GMP) | unverified, cross-checked |
| `tools/runs/` | Logs of the long runs | data |

Run `lake build` to build everything. `Accel.Bound` takes about 70 seconds.

## 2. Checking GPT's results

* **Lean drafts.** Both `MixedRadix.lean` and `Overflow.lean` failed only because
  `RequestProject.Macro` was missing. With the archive restored they compile with
  no `sorry` and only the standard axioms. Five proof steps needed the same small
  repair: `simp only [List.cons_append]` before `cases u ++ r <;> rfl`. No
  statement was changed. Among other things, this gives `mrAdd_single_sound`, the
  rational value law `mrAdd_value`, the A-exit families `collide32` and
  `fresh_overflow`, and the closure of the productive family `productive_return`.
* **Exhaustion normal form and physical event theorem** (Sections 3–4 of
  `tm_overflow_progress/RESULTS.md`). GPT proved these on paper only. They are
  now Lean theorems, `exh_spec` and `drain`, with the exact step count. In the
  Lean version the rules for `40` and `43`, including the edge cases of `43` with
  suffix capacity 0 or 1, are proved for arbitrary surrounding tape.
* **GPT's checkpoints.** Our C simulator, written independently and using only the
  drain rule:
  - agrees exactly with a literal simulation at \(10^8\) and \(10^9\) steps;
  - agrees with GPT's Python event machine on the complete configuration at a
    time with 301 decimal digits;
  - gives `lo = -2150` and `hi = 6643` just after \(10^{1000}\) steps, the same
    values as GPT's \(10^{1000}\) checkpoint.
* **Not established by GPT, and still not established:** that the blank-tape run
  ever enters the productive family. Any global invariant.

## 3. New Lean results

* `TM2x5.exh_spec`: for every word `w` over the tokens `2, 40, 42, 43, 44`,
  `exh w = (C, H, T)` is exact. The word admits exactly `C` complete returns;
  then an entering `A` leaves it on the right, having rewritten it to `H`. The
  total time is `T`.
* `TM2x5.drain`: a counter `N` of width `m` with a frontier `1` on the left, the
  token word on the right, and state `A`. After `T₀ + T` steps the configuration
  is counter `N + C`, word `H`, head just past the word in state `A`. Here
  `T + s₃(N+C) = 2C + s₃(N) + 2(m' − m)`, where `s₃` is the base-3 digit sum. The
  width can only grow (`m' > m`) if the tape left of the frontier is blank.
* `TM2x5.runAccel_sound` / `no_halt_of_runAccel`: one simulator step is a drain
  whenever its preconditions hold, checked at run time, and a literal step
  otherwise. Every simulator step is an exact run of the machine.
* `TM2x5.not_halted_within_ten_pow_thousand`: `∀ n ≤ 10^1000, run n ≠ none`.
  Before this, the largest Lean-checked bound was \(10^8\). The same certified
  simulator reaches \(10^{3000}\) in about 11 minutes. That longer run was done
  once by evaluation but is not included as a theorem, to keep build times short.

## 4. Fast simulation (unverified, but cross-checked)

`tools/fastsim.c` uses the drain as its only macro and runs everything else
literally. It is exact: GMP integers are used for the step count. Big-number work
on runs of pair tokens is batched 56 tokens at a time. `tools/fastsim2.c` also
keeps the main counter in binary and writes its digits to the tape only when the
head walks into them. Both give identical full configurations at \(10^{3000}\)
and \(10^{10000}\).

| Steps reached without halting | Time (one core) |
|---|---|
| \(10^{1000}\) | 0.25 s (`fastsim2`) |
| \(10^{10000}\) | 20–30 s (`fastsim2` / `fastsim`) |
| \(10^{60000}\) (log in `tools/runs/`) | 32 min (`fastsim`, with logging of counter entries) |
| \(10^{100000}\) (log in `tools/runs/`) | 88 min (`fastsim2`, sharing the machine with another run) |

Build with `gcc -O2 -o fastsim fastsim.c -l:libgmp.so.10` and run
`./fastsim DIGITS [SECONDS] [DUMP.json]`.

How the run time grows: the tape width is about \(8.7\) cells per decimal digit
of the step count. There are about 5 drains per decimal digit. Each drain and
each sweep costs time proportional to the tape width, so the total cost is
roughly quadratic in the number of digits. To go much further one would need a
run-length tape with shift rules (see §6).

## 5. What the simulations show about halting

* **Structure.** At \(10^{10000}\) steps the tape is: a dense base-3 counter of
  about 21 000 digits, then a region of about 66 000 cells made of only about 60
  runs. The runs are a `20`/`02` background with isolated markers (`3`, `42`,
  `0`), and their lengths grow roughly geometrically (…, 1232, 2461, 11071, 16608).
  Before each big drain the word right of the counter has the form
  `2 B₁ 2 B₂ … 2 B_k 42 44 3 2 0`. Each `B_i` is a long binary block, mostly `42`
  with a few `44`. The block lengths grow slowly from cycle to cycle.
* **Where cascades are stopped.** The drain replaces every pair token by `20` (or
  `24`) and every `2`-token by the ternary digit `dsym(c mod 3)`, where `c` is the
  return capacity of its suffix. A left-moving cascade crosses the `20`
  background. It is stopped by a `4`, or by a `00`, which arises from a residue 2.
  This matches the stopper lemmas already in `Shield.lean`.
* **Cascades that reach the counter.** Up to \(10^{60000}\) steps (299 000 drains,
  counter width about 126 000 digits), exactly 21 cascades entered the counter.
  This happened at drains 7, 26, 78, 596, 819, 946, 1392, 1435, 1886, 2224,
  2712, 5205, 5207, 7224, 21376, 27528, 27530, 40491, 114606, 158738 and 259035.
  None got more than 9 digits deep. A halt needs a cascade to cross *every* digit
  of the counter. By `cross_digits_iff` (in `Counter.lean`) this requires all
  digits to avoid `1` and to contain no `22`. For a counter of \(m\) digits
  without special structure, the chance of that is about \((1.618/3)^m\).
* Up to \(10^{100000}\) steps (`fastsim2`, 498 000 drains, tape width 874 000, counter
  width about 210 000 digits) there was still no halt, and no cascade got deeper than
  9 counter digits.
* **Heuristic conclusion (not a proof).** The machine almost certainly runs
  forever. A proof would need control of the low base-3 digits of the counter at
  the rare times a cascade reaches it. That is a statement about the arithmetic of
  a recursively defined sequence, of the same kind as Collatz-type problems. We
  do not see a route to it with the current tools.

## 6. Possible next steps

1. Write a run-length simulator with generic shift rules over runs of the `20`
   and `42` blocks, a drain that acts on whole runs of identical tokens, and a
   binary counter. Each cycle would then cost about O(number of runs) instead of
   O(width), which could reach roughly \(10^{10^6}\) steps.
2. Describe a whole cycle (drain → right end → return sweep) as a map on the
   compact data: counter value, block lengths and markers. If the map can be found,
   prove it in Lean as one macro.
3. Try to find a property of the counter value at the times a cascade reaches it
   that rules out crossing the whole counter. That is the missing global
   invariant.
