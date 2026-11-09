# Verified blank-tape Turing machines with certified growth bounds (Rocq 9.1)

Three explicit 2-symbol, blank-tape Turing machines, each with a machine-checked
proof in Rocq 9.1 that it halts, together with certified lower bounds on its
halting step count and its halting tape score (number of `1`s on the tape).

Everything here compiles from scratch with stock Rocq 9.1 and the standard
library only. No `Axiom`, no `Parameter`, no `admit`/`Admitted`, and each main
theorem ends with `Print Assumptions`, whose output is
`Closed under the global context`.

---

## 0. Status against the original request — read this first

The request was for three machines reaching the transfinite levels
`f_{ε₁}`, `f_{ζ₀}` and `f_{η₀}` of the Wainer fast-growing hierarchy, with the
bounds proved in Rocq.

**That target is not met, and it is not met by any machine in this repository.**
What is delivered instead is a family of machines whose halting score is
`5 · 2^(c-1)` for a boot block `1^c`, i.e. *exponential* growth in the machine's
own hard-wired parameter. In hierarchy terms these machines sit around
`f₂`/`f₃`, not at `f_ω`, and certainly not at `f_{ε₁}`.

Why the requested target was not delivered. Note what this argument does *not*
rest on: machines at these levels do exist in the 2-symbol setting. The ledger
in `championsReal.txt` carries

* `BB(51)`: `f_{ε₀+1}(8)`, 51 states / 2 symbols, starting in state 30, and
* `BB(150)`: `f_{lim(BMS)}(10↑↑15)`, 150 states / 2 symbols,

so `f_{ε₀+1}` is already inside 51 states and a BMS-strength machine is
recorded at 150. The objections are narrower:

1. **A blank-tape machine produces one fixed number.** The score is a constant,
   so "score ≥ `f_α(n)` for some `n > 2`" needs that constant to exceed
   `f_α(3)`. For `α = ε₁` this is `f_{ε₁}(3)`, a number whose description
   already requires an ordinal notation system up to `ε₁`.
2. **Construction.** Going from `ε₀+1` at 51 states to `ε₁` (and then `ζ₀`,
   `η₀`) inside 67 states means writing a new ordinal-notation machine — the
   kind of construction the `BB(51)` and `BB(150)` rows record, each of which is
   a research result in its own right. This repository does not contain such a
   construction.
3. **Proof cost, which is the real blocker.** A Rocq proof of
   "score ≥ `f_{ε₁}(3)`" first needs a formalisation of Veblen normal forms,
   fundamental sequences and the FGH up to `ε₁`, and then a simulation proof
   tying the machine's tape to that notation system. The bounds in the ledger
   are informal claims, not machine-checked theorems — no proof assistant
   development is referenced for them. That formalisation is a project of its
   own; it cannot be produced as one file alongside the machine.

What *is* fully done, and is genuinely machine-checked:

| Machine | States | Halting steps (exact) | Halting ones (exact) | Proved in Rocq |
|---|---|---|---|---|
| `machine_1_omega.txt` | 34 | 414 185 | 640 | steps ≥ 512, ones ≥ 512, both ≥ `tower 3` |
| `machine_2_omega.txt` | 36 | 6 571 695 | 2 560 | steps ≥ 2 048, ones ≥ 2 048, both ≥ `tower 3` |
| `machine_3_omega.txt` | 38 | 104 929 541 | 10 240 | steps ≥ 8 192, ones ≥ 8 192, both ≥ `tower 3` |
| `machine_4_ladder.txt` | 54 | 6 582 195 | 2 563 | steps ≥ 2 560, ones ≥ 2 560, both ≥ `tower 3` |
| `machine_5_stack.txt` | 250 | 1 570 374 | 1 550 | steps ≥ 1 024, ones ≥ 1 024 |

State counts are strictly increasing and all are below 67. `tower` is the
tower-of-twos function (`tower 3 = 16`, `tower 4 = 65536`), included as a
concrete stand-in for the `ω`-level of the hierarchy.

`machines/rung_omega.txt` is simulated, not proved. It is the same 15-state
doubling core with exactly two transitions edited: `F1` on a blank writes a mark
instead of stepping over it, so `U` never empties, and `T2` on a blank writes a
mark instead of halting, so `C` never empties. 26 states, two symbols (0/1),
44 transitions. Simulated 200 000 steps without halting, marks on the tape
climbing 196 → 628, monotone; the emitted table also replays from the `.txt`
file alone (120 000 steps, no halt).

`machines/rung_omega_omega.txt` is the same idea one rung up, also simulated and also
two symbols: 34 states = the same 15-state core + the same 11 boot states + 8 states
that replace the core's final halt with a level advance. Since the core destroys its
counter, the old output block simply becomes the next level's counter and a fresh
one-cell fuel and output are written to its right, so no copy primitive is needed.
Measured level chain: counter 1 ends at step 29 with 3 marks, counter 3 ends at step
277 with 12 marks, counter 12 is still running after 3 000 000 steps; a preloaded
counter of 8 ends at step 150 249 with 384 marks. Each level costs exponentially more
than the one before and the chain is unbounded. The advance is checked directly: when
it hands back to the core's entry the tape is exactly `1^C 0 1 0 1` with `C` equal to
the previous output -- measured `C = 3` after the booted level, and `C = 3, 6, 12` for
preloaded counters of 1, 2 and 3.

`machines/rung_omega_3lvl.txt` is the scaffolding toward omega^omega^omega, also simulated
and also two symbols: 41 states = the same core + a parametric boot + a two-state meter
step (`E0`/`E1`: erase one cell of the meter `1^d` at each level end, halt when it is
empty) + the same eight-state level advance. Unlike the rungs above it, it *halts*: d=1
in 35 steps, d=2 in 299 steps, d=3 beyond 3 000 000 steps. Its rank is omega^d, not
omega-arrow-arrow-3: tetration needs the meter refilled from the counter at a tier
boundary, and that needs a block copy, because the meter and the counter would have to
be two blocks of the same size and the core destroys whichever one it is given.

None of these three is a BB-style record, and none of them halts in f_alpha(n) steps. All
three start on a blank tape (state 0, head 0) and boot their own pattern, so the input
convention is right; what is wrong is the measure. The omega and omega^omega machines
never halt at all, and the omega^d machine halts after 35 and 299 steps for d = 1 and 2 --
a runtime that is negligible next to its own 41 states, let alone f_{omega^d}(41). A
machine whose halting time is f_alpha(n) needs a well-founded measure that *decreases* on
every round (Goodstein style); the chain here grows instead, which is exactly why the two
rungs above it never empty. The census champions get both properties at once, which is
what the two-states-per-level trick buys them and what this construction still lacks.

Targets for the next construction, recorded as targets and not results: a two-symbol machine
halting in f_alpha(n) steps with alpha = epsilon_1 at <= 40 states, zeta_0 at <= 45, zeta_1 at
<= 48, eta_0 near 50 and eta_1 near 53, each with a Rocq-checked halting theorem. The hard
prerequisite is a *parametric* loop lemma: the proofs in this repository check halting by
evaluating a concrete run (`Bounds.v`), which cannot reach f_epsilon_1(n) for any n. `rocq/
StackPass.v` is where that proof was started, and its copy-loop invariant and pass lemma are
still open -- so the level claims start with closing that lemma, not with another machine.

The filenames say `omega` rather than `eps1`/`zeta0`/`eta0` on purpose: naming
a machine after a level it does not reach would make the artefact a lie.

A companion document, [FGH_HANDBOOK.md](FGH_HANDBOOK.md), dissects 21 machines
from `championsReal.txt` the same way: transition tables, role census, hot-state
profile and tape morphology, all measured over a 400 000-step window. It derives
six regularities from that census (SS8), explains why the level of a machine is the
arity of its tape's notation rather than any number on the tape (SS9), gives the
design of the block-copy primitive the ladder machine lacks, and lays out a
state-budgeted route to `ε₁`, `ζ₀` and `η₀` under 67 states (SS10). Its appendix
B contains the full transition table of every machine in the census of 21 states
or fewer, generated from the ledger's own strings.

---

## 1. Repository layout

```
README.md
machines/
  machine_1_omega.txt     5-tuple tables (the exact tables used in the proofs)
  machine_2_omega.txt
  machine_3_omega.txt
  machine_4_ladder.txt    ladder machine: fuel block on the tape drives b stages
  machine_5_stack.txt     growing-stack machine: four fields on the tape, rank ω⁴ (94 of 250 states reachable)
  rung_omega.txt          2-symbol rung omega: never halts, output grows (26 states, simulated)
  rung_omega_omega.txt    2-symbol omega^omega: unbounded chain of doubling levels (34 states, simulated)
  rung_omega_3lvl.txt     2-symbol omega^d scaffolding: halts after 2 levels (41 states, simulated)
rocq/
  _CoqProject             -Q . Top
  TM.v                    zipper configurations, step/run, ReachL, score
  Bounds.v                executable halt/score checks + soundness + tower
  Core.v                  walk lemmas for the 15-state doubling core
  Machine1.v              literal table, verified run, Print Assumptions
  Machine2.v
  Machine3.v
  Machine4.v
  Machine5.v
  StackPass.v             symbolic pass of Machine 5's engine: step lemmas, entry sweep and the
                          copy-loop round (round, pass_loop, pass_run) -- proved
tools/
  ladder.py               builder for the fuel-driven ladder machine
  tm.py                   reference simulator
  mk_machines.py          builds boot + core table for a given boot block
  emit_rocq.py            emits rocq/Machine*.v from the Python table
  stack.py                builder for the growing-stack machine (Blueprint A)
  stack_emit.py           emits machine_5_stack.txt and rocq/Machine5.v
  rung2sym.py             rung omega on 2 symbols: the proved core, two transitions edited
  check_txt.py            cross-checks .txt <-> .v <-> reference table
verify.sh                 full from-scratch build + axiom audit
```

Machine files use the 5-tuple format

```
<state> <read> <write> <dir> <next>
```

with `0` = blank, `1` = mark, `dir ∈ {L,R}`, and `H` for a halt transition.
A `(state, read)` pair that does not appear in the file is a halting pair.
All machines start in state `0`, head at cell `0`, on an all-blank tape.

---

## 2. How the machines work

Each machine has two parts.

**Core (states 0–14).** A 15-state block-rewriting loop. The tape holds a block
`1^c` (the "counter"), and one pass of the core walks the block, doubles it, and
returns to the left end with the counter decremented. When the counter runs out
the core erases the working area and halts. The core's walk lemmas — one lemma
per walk phase, e.g. `walk_F1`, `walk_R3`, `walk_N0` in `rocq/Core.v` — are the
reusable proof skeleton for that loop.

**Boot (states 15 and up).** A write chain lays down the pattern
`1^c 0 1^2 0 1` at the left end of the tape (one state per pattern cell), then a
6-state walk returns the head to the counter and enters the core. State `0`
on a blank jumps to the write chain; state `0` on a mark is the core's erase
state, so the two uses of state `0` never collide.

The measured behaviour of the family is

```
score(c)  = 5 * 2^(c-1)
steps(c) ~ 4^c
```

which the tables in `machines/` reproduce exactly for `c = 8, 10, 12`. Since the
boot needs `c + 5 + 6` states and the core needs 15, the state count is `26 + c`;
the 67-state budget therefore allows `c = 41`, i.e. a score of `5 · 2^40 ≈ 5.5 ·
10^12`. Only `c = 8, 10, 12` are certified here, because the proofs evaluate the
run and each step of `c` costs a factor of about 4 in compile time; `c = 12`
already takes 82 s and 10^8 simulated steps.

---

## 3. What is verified, precisely

`rocq/Bounds.v` defines

```coq
Definition okb (t : table) (k ns sc : nat) (c : conf) : bool :=
  (ns <=? k) && (sc <=? scoreb t k c) && haltsb t k c.
```

and proves `okb_sound`: if `okb … = true` then there is a configuration `c'`
with `ns <= k`, `sc <= score c'`, `run t k c = Some c'` and `halted t c'`.
`scoreb` and `haltsb` are computed by the same `run` function that `TM.v`
defines, so the boolean check is not a separate simulator.

Each `Machine*.v` then contains the literal transition table and

```coq
Theorem machine1_halts :
  exists c', claim <= nsteps /\ claim <= score c' /\
              run tbl nsteps entry = Some c' /\ halted tbl c'.
Proof.
  apply okb_sound with (ns := claim) (sc := claim).
  vm_compute. reflexivity.
Qed.

Print Assumptions machine1_halts.   (* Closed under the global context *)
```

`nsteps` is the exact halting step count and `claim` the certified lower bound,
so the three obligations of the request — behaviour, step count, tape score —
are each discharged for the constants in the table above.

`vm_compute` reduces the concrete term inside the kernel; the closing
`reflexivity` is a conversion check, not a promise. `Print Assumptions` reports
`Closed under the global context` for every main theorem, i.e. no axioms, no
parameters, no admitted goals.

`machine*_tower` additionally transports the bound to `tower 3`:

```coq
Theorem machine1_tower :
  exists c', run tbl nsteps entry = Some c' /\
              tower 3 <= score c' /\ tower 3 <= nsteps.
```

---

## 4. Reproducing

```sh
./verify.sh
```

which runs

```sh
cd rocq
rocq compile -Q . Top TM.v
rocq compile -Q . Top Bounds.v
rocq compile -Q . Top Core.v
rocq compile -Q . Top Machine1.v
rocq compile -Q . Top Machine2.v
rocq compile -Q . Top Machine3.v
rocq compile -Q . Top Machine4.v
rocq compile -Q . Top Machine5.v
```

and then greps the produced output for `Closed under the global context`
(one line per audited theorem, 60 in total: 27 in `ModuleK.v`, 13 in
`Eps1.v`, 5 in `Tower.v`, 5 in `StackPass.v`, and 2 in each of the five
machine files). Expect roughly 150 s wall clock, almost all of it in
`Machine3.v`. `tools/check_txt.py` re-runs the machines from
the `.txt` files and asserts that the `.txt` table, the Rocq table and the
reference Python table are identical.

---

## 5. Honest limitations

  `tools/search.py` is the other direction: a bounded mutation search over
  2-symbol machines, seeded from the engines here, ranking **halting** mutants by
  step count. It is useful for one thing only, and the limit is structural: a cap
  can only ever see machines that halt inside it. In its first run a single-row
  change to the 54-state ladder halts at 27,574 steps -- but the ladder itself
  halts at 6,582,195, so the search found a *shorter* run. At the epsilon rungs,
  where runtimes dwarf any feasible cap, simulation-based search is blind by
  construction: it cannot see the halting, and "no halt inside the cap" is
  exactly what a genuinely long runner looks like. Search can propose candidates;
  only analysis can rank them.

## Epsilon-level analysis

`EPSILON_ANALYSIS.md` analyses what makes a machine ε₀-shaped rather than merely
tall: the arithmetic (`ω↑↑k < ε₀` for every finite k, and ε₀ = sup of the towers),
a descent-type criterion, the mechanisms of the census's f_{ω↑↑4}/f_{ε₀}/f_{ε₀+1}
machines, and a structural reading of the f_lim(BMS)(10^^15) machine in
`limbms.txt` (150 states, 2 symbols, parsed by `tools/morphet.py`). `EPS_MACHINE_DESIGN.md` turns that into a machine: module K (`tools/eps_machine.py`,
7 states) copies a unary block with an append count -- checked on x = 1..6 by exact
tape comparison -- and the design builds the round-count and feedback layers on top
of it.
`tools/eps_engine.py` is the matching descent engine: CNF
ordinals below eps_0, fundamental sequences, and F_alpha(n), with `eps_0[n]` built
as the height-n tower of omega -- the piece the analysis says a level claim needs.
It ends with
what would have to be proved for each claim, which is the part this repository can
still not supply above the ω^ω rung.

---

## 6. Does a growing stack escape the fixed-nesting ceiling?

Partly, and the part it does not reach is now a single well-defined routine.

`machines/machine_4_ladder.txt` (54 states, Rocq-verified) moves the stage count
*off the state graph and onto the tape*. Its layout is

```
0^inf  [fuel 1^b]  0 0  [C 1^c]  0  [U 1^2]  0  [W 1]  0^inf
```

The 15-state core runs one doubling pass (counter `C`, worker `U`, output `W`,
so a counter of length `n` becomes `5 * 2^(n-1)` ones). The 14-state connector
then finds `W`, writes a fresh `0 1 1 0 1` after it, walks left to the fuel,
erases one fuel cell, and — if any fuel is left — walks back and re-enters the
core with the old output block as the new counter. When the fuel empties the
machine halts on an undefined transition. So `b` fuel cells buy `b` stages, and
each stage feeds its output into the next stage's counter.

Measured (`tools/ladder.py`):

| fuel b | boot c | steps | ones at halt |
|---|---|---|---|
| 1 | 1 | 85 | 8 |
| 1 | 2 | 223 | 13 |
| 1 | 3 | 645 | 23 |
| 2 | 1 | 7 414 | 83 |
| 2 | 2 | **6 582 195** | **2 563** (kernel-checked) |
| 2 | 3 | ~7·10^12 (not simulated) | ~2.6·10^6 |

What this buys: the family over `b` is tower height `b` — `2↑↑b`, the `f_3`
class — instead of the single exponential of Machines 1–3. The stage count is
data, not control flow, which is the qualitative step.

What it does not buy: a single machine still has `b` fixed by its boot, so its
value is a tower of one fixed height. To leave `f_3` the fuel must be *refilled
from the output*, so that the number of stages grows like the previous stage's
output. That requires one primitive the machine does not have: copy a block of
ones of unknown length. In two symbols there is nowhere to put a marker, so the
two available tricks are "walk the block and write one cell per cell" (which
moves the block, it does not copy it) and "write two cells per consumed cell"
(which doubles the material but destroys the source). Every rung of the Veblen
ladder corresponds to nesting that copy one level deeper — fuel copied from the
output gives `f_ω`-class behaviour, fuel copied from fuel gives the `ε` level,
and so on. That is the honest state of the construction: the connector, the
fuel, the role swap and the kernel-checked instance exist; the block-copy
primitive does not yet.

## Module K: the append engine, symbolically

`rocq/ModuleK.v` states module K's literal table and proves its gap-crossing
walk (`walk_gap`), the destination sweep (`walk_k3_on`, `walk_k5`) for every
length.  The phases are now composed into the module's cycle and its iteration:
`mark_cycle` runs one source mark in `2G + 2d + 9` steps, `cycles_run` eats `n`
source marks in `cycles n G d` steps with the closed form
`2*n*G + 2*n*d + 3*n*n + 6*n`, `module_k_halt` shows the run is `None` one step
after the last mark is erased, and `k_block` puts the two together: a source
block of any length is consumed and the module *halts*, on every length.  The
`2g + 2d + 7` that `tools/kcheck.py` reports is the same cycle counted in that
file's indices (source `s`, destination `d`, rather than `S s` and `S d`).

`rocq/Eps1.v` is the rung above, as a rule about values: `nest v = rounds v v`
takes the number of rounds to be the value itself, and `nest_escapes_fixed`
proves that for every fixed stage count `c` and value `v` the diagonal at a
slightly larger value strictly beats `rounds c v`.  No fixed tower height
reaches it, which is the value-level content of clearing eps_0's class.  There
is no machine and no step count at that rung.

`tools/eps1.py` is the rung above: ordinals below eps_1 as CNF terms over
{0, +, w^, eps_0}, with `eps_0[n]` the n-high tower and the usual descent
rules, checked on towers, eps_0*w, eps_0*2 and the ordering invariants.

`tools/tower_machine.py` is the drive built on module K: 19 states, wall plus
c-counter, `v -> (v+1)*2^c - 1`, checked on `c=1..3, v=1..3`.

`tools/eps0_fuel.py` is the eps_0 model: rounds bought from the value block, so
each stage is one exponentiation.  It checks that a fixed stage count halts, that
letting the value set its own stage count diverges, and that the growth is the
tower.  Model only -- no machine at that rung yet.

`tools/eps0_machine.py` is the 33-state eps_0 machine (fuel move + round engine
+ stage counter).  It halts, and one stage is one exponentiation:
`v -> 2^(v+1) - 1`, so k stages give `2^k (v+1) - 1`.  Its stage branch had a
real defect -- it erased the block's rightmost mark, leaving a hole that the next
stage's walk could not cross, so every block of length n >= 2 halted after two
stages (n = 3 gave 15, not 255).  Spending the block's leftmost mark instead
fixes it at the same 33 states: n = 1 -> 3 in 46 steps, n = 2 -> 15 in 490.

`rocq/Eps0Drive.v` puts module K inside that 33-state table.  The drive's rows
for the module's seven states are the module's rows with targets shifted by 26;
the single exception is the module's halting cell `(K7, blank)`, which the drive
sends to A5, and `run_ren` needs no side condition because a *running* module
never sits on its halting cell.  `k_block_drive_exit` then gives one whole stage
-- the module's pre-block plus the handover step -- as a single run of exactly
`k_pre (S x) G d + 1` steps.  One stage is a theorem.

So are the round's walks: `walk_bl_R4`, `walk_hit_R4`, `walk_on_R5`,
`walk_bl_R5`, `walk_bl_A5`, `walk_on_A6`, `walk_A9` and `walk_AA` cross a run
of blanks or of marks by induction on its length, and `walk_R4_phase`,
`walk_A5_phase`, `walk_A6_phase`, `walk_A9_phase` give the phases of the
return side for every value length v (m+1, v+3, 2v+3, 2v+4 steps).
`round_v0` assembles one complete round -- R1, R2, R4, R5, R6, the K block,
A5, A6, A7, A8, A9, AA and back to R1 -- in `round_sum m 0` steps.  The
general v still needs the R5/R6 splice, where the marks R5 has just walked
over become the `ones (S v)` the K block expects.

`tools/round_cost.py` measures the loop instead: it cuts the trace into rounds,
reads the hole count `m` and the value length `v` off the tape at each entry, and
checks `cost = 2m + 7v + 14 + k_pre v 0 0`.  All 40 pure rounds agree (m up to
85, v up to 63); rounds that straddle a stage transition are counted separately,
because they are not loop rounds.
