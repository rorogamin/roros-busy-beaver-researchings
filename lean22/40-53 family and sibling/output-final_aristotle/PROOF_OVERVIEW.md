# BB(2,5) family `1RB2LA0RB1LB---_1LA3RA1RA4LB---`: proof overview

This is the current map of the Lean development. It covers the 13 family
members plus the `4RB/0LB` sibling. Every file listed here is on the path to
one of the non-halting theorems. Exploratory material from earlier sessions
(simulators, traces, `f`-value experiments, phase maps) has been removed; it
is still in the git history. `ANALYSIS.md` is the historical research log and
names files that no longer exist.

## The statements

`RequestProject/BB25/Check.lean` states each result for the machine written as
its bbchallenge string:

```
theorem not_halts_0RB : ¬ Halts (fromStd "1RB2LA0RB1LB---_1LA3RA1RA4LB0RB") init
```

The file has one such theorem for each of the 13 members
(`2LB 2RB 1LB 1RB 0LB 0RB 3RA 2LA 2RA 1LA 1RA 0LA 0RA`) and one for the sibling
`1RB2LA0RB1LB---_1LA3RA1RA4RB0LB`.
`fromStd` decodes the string into a transition table. For each machine, a
cell-by-cell check (`table`) shows that this table is the one used in the proof.
All 14 theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

Semantics (`Machine.lean`):

- A configuration `⟨l, q, d, r⟩` uses directed-head notation. `l` and `r` list
  the cells to the left and right of the head's edge, nearest first. All other
  cells are `0`.
- `step` returns `none` exactly on an undefined transition, i.e. a halt.
- `Halts m c := ∃ n, steps m n c = none`.
- `init` is the blank tape with the head in state `A`, facing right.

## Layers

| Layer | Files | Content |
|---|---|---|
| Machine | `Machine`, `Nonhalt` | TM semantics; the family `M b4`; the left-end `<B1` spinout |
| Blocks | `Blocks`, `Runs` | block configurations and `bstep b4` with its soundness `bstep_sound`; block runs `BRun`; counter `cval`, stacks `CStack`, decrement `cdec`, overflow `ofw` and their machine runs (`brun_cdec_of`, `brun_overflow_of`) |
| Words | `Prefix/Word`, `Expand`, `Slack`, `Stack`, `Reset`, `Strict` | the right-word digits `Y V X`, decoder `rrun`/`trun`, Dyck prefixes, stack invariants `Adm`/`Good`/`Strict`, the reset transducer `tfold` |
| Returns | `Prefix/Drain`, `Bottom`, `DrainWord`, `Return`, `Except`, `Marker` | safe checkpoints `SafeCP`, the drain and paid-reset runs, the return theorem `cp_returns` for a member whose `A> 241` case `WCase b4` holds |
| 10 members | `Prefix/Bit` (1RA), `Zero` (0LA), `Two` (2LB), `Marker` (0RA, 2RB), `One` (1LB), `K0` (2RA), `JOne` (1RB), `Return` (3RA, 2LA via `wcase_of_gBit`); `Prefix/Main` | each member's `WCase`; the 156-step seed `seed_run`; the ten theorems |
| 1LA | `Prefix/LA`, `LA/Debt`, `Chi`, `Direct`, `Exact`, `Final` | the `Ready` scan; the `01` branch `zreadyS` (for every `b4`) → `zready`; `not_halts_1LA` |
| 0RB | `Prefix/RB/*` | checkpoints `CP0`, words `Gen`, pops `rb_pop_episode`/`first_episode`; Lemma A (`LemmaA`, `Families`, `Classify`, `Credit`, `Debt`), the gap and clock lemmas; the `01` branch `zevenS` (for every `b4`) → `zeven`; `not_halts_0RB` |
| 0LB | `Prefix/LB0/*` | energy (`Energy`, `Clock`), the four-decrement pop (`Scan`), the invariant `ZInv` with return `zinv_return` (`Return`), the 931-step entry and `not_halts_0LB` (`Final`) |
| Sibling | `Sibling/Local`, `Transfer`, `Pop`, `Final` | the machine; transfer of `bstep none` runs (`BRun.sib`, `BRun.sib_frame`); the `043` pop; sweep and `not_halts_sibling` |

## Shared argument

Every proof has the same shape:

1. A finite run from blank reaches a checkpoint `L s <B1 22 1$`. This is the
   `156`-step run for all members except 0LB, which uses the `931`-step run.
2. A return theorem shows that from every checkpoint in an invariant class,
   the machine either reaches another checkpoint of the class in at least one
   base step, or enters a spinout that provably never halts.
3. A descent on a hypothetical halting time turns this into
   `¬ Halts … init`.

The invariant classes are:

- `SafeCP`: the ten members of `Prefix/Main`.
- `ReadyCP`: 1LA.
- `CP0`: 0RB and the sibling.
- `ZInv`: 0LB.

Machine runs are almost always built from block steps (`bstep b4`) and are
generic in `b4`. Only the `A> 241` rule and the pop depend on the member.

## Finite computations

These are the only kernel computations, all checked by `rfl` or `decide`:

- `seed_run`, 156 base steps (`Prefix/Main`, and again in `Sibling/Local`
  for the sibling's table).
- `entry_run`, 931 base steps (`Prefix/LB0/Final`).
- The single rules, each a few base steps: every case of `bstep_sound`, the
  sibling's `bstep_none_sound_sib`, its marker rules and the spinouts.
- The table checks in `Check.lean`.

There is no bounded-simulation certificate or trace computation.

## Notes for a translation

- The whole development imports Mathlib, but it only uses basic lists,
  naturals, integers, `omega`, `simp` and `ring`.
- `bstep` is one large pattern match. Its soundness is one `rfl` per rule.
- The sibling is not an instance of `M b4`. `Sibling/Transfer.lean` explains
  how the block lemmas are reused anyway: run them at `b4 = none` and track
  the number of `F`/`G` blocks.
