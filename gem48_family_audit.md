# Audit: the gem48 / gemini eps2-zeta0 family is not a champion family

Date: 2026-11-10.  Scope: `rocq/gemini_epsilon1_tm_48s_v2_fix.v`,
`rocq/gemini_epsilon2_zeta0_tm.v`, `rocq/FGH_Eps2_Zeta0_Eta0.v`, and the
ledger row "ADD: gem48" in `championsReal.txt`.

## 1. The claims

The machine is one fixed table: 48 states, 2 symbols, blank tape, start S01.
The table itself is unchanged from gemini's original (the ledger records it
verbatim); `gemini_epsilon1_tm_48s_v2_fix.v` is the zero-axiom compiling copy.

Two claim layers sit on that one table:

* gem48 (eps1): halting step
  `T = 1641 + f_eps0(f_eps1[0](f_eps1[1](f_om^2(f_eps1[2](f_om^3(f_eps1(3)))))))`,
  claimed `> f_eps1(3)`.  Ledger status: INFORMAL, halt not witnessed.
* eps2 / zeta0: blank tape reaches the worm `W_0 = [(0,0);(0,2)]` (= zeta0)
  at step 352, the eps2 spine `W_1 = [(0,0);(0,1);(1,1);(2,1)]` at step 702,
  and an eps3 spine at step 1641; then
  `blank_halting_run_exceeds_f_eps2_2` and `..._f_zeta0_1` conclude
  `f_eps2 2 < T` / `f_zeta0 1 < T`.

## 2. What is genuinely kernel-checked

All of the following are `vm_compute; reflexivity` or closed proofs, no axioms:

* the milestone equalities `boot_352_zeta0`, `campaign_expand_zeta0_to_eps2`,
  `campaign_expand_eps2_to_eps3` (steps 352, 702, 1641 exact);
* the evaluation lower bounds `worm_702_eval_ge_f_eps2` and
  `worm_352_eval_ge_f_zeta0`, i.e. `eval(rev W_1) >= f_eps2 2` and
  `eval(rev W_0) >= f_zeta0 1`;
* 15 theorems in `FGH_Eps2_Zeta0_Eta0.v` and 12 in
  `gemini_epsilon2_zeta0_tm.v`, all `Print Assumptions` = closed.

What is **not** checked, and does not exist anywhere in the tree:

* any term inhabiting `worm_chain_fgh`.  `grep -rn worm_chain_fgh rocq/`
  finds only the inductive definition, the soundness lemma, and the
  hypotheses of the two runtime theorems.  No chain is constructed.

`worm_chain_fgh_sound` is therefore a conditional statement: *if* a chain
exists, *then* the run halts in at least the evaluated number of steps.
`Print Assumptions` being closed says the proof uses no axioms; it says
nothing about whether the hypothesis can be satisfied.

## 3. What the machine actually does (new measurement, this audit)

Blank tape, exact table, run to 5,000,000 steps:

| steps | tape span | head | ones | halted |
|---|---|---|---|---|
| 100,000 | 395 | 192 | 281 | no |
| 500,000 | 865 | 756 | 620 | no |
| 1,000,000 | 1,238 | 78 | 889 | no |
| 2,000,000 | 1,735 | 418 | 1,242 | no |
| 5,000,000 | 2,743 | 1,532 | 1,970 | no |

`span / sqrt(steps)` is 1.25, 1.22, 1.24, 1.23, 1.23 across the five points:
the span obeys `span ~ 1.23 * sqrt(steps)` to two digits over a factor of 50
in time.  That is the signature of a quadratic-time bouncer, not of a
descent.  Compare the BB(2,5) holdout #36 (`holdout36_macro_analysis.md`),
whose span grows as `1.33 * sqrt(steps)`: gem48 is in the same dynamical
class as the undecided bouncer, only with more states.

This matches the recorded milestone recurrence (c0 = -14 - n, pair count
`1 + n(n+1)/2`, cost per cycle growing like n^4): the head walks left and the
pair block grows, so the "worm" gains structure rather than losing it.

## 4. Why the chain hypothesis is not satisfied

`WCC_Step_FGH` requires, for each snapshot pair,

    eval(rev w) n  <=  dc + eval(rev w') n'

where `dc` is the number of TM steps between the two snapshots.

The audit test (`python tools/_audit_fgh_halting.py`) finds the trajectory

* step 3895: worm of 11 pairs, including the eps3 pair `(3,1)`;
* step 4126: worm `[(0,0);(0,1)]`, i.e. value 1.

That transition takes **231 steps**.  The worm at the left end contains the
`(3,1)` pair, which `worm_eval_full` sends through `f_eps_k 3`; the right end
is `[(0,0);(0,1)]`, which evaluates to 1.  So the left side is an
eps3-indexed value, astronomically larger than `231 + 1`, while `dc = 231`.
The inequality fails by an astronomical margin.  Any chain that followed the
actual trajectory would have to replace `dc = 231` by a number of that
astronomical size, i.e. skip the collapse entirely and sample the run only
at far-separated times; and it must still finish at a `WCC_Halt_FGH` step,
which requires an actual halting configuration.  None is observed in
5,000,000 steps, and the measured dynamics are those of an oscillator
whose block grows without bound.

So the two runtime theorems assert nothing about this machine unless it
halts, and the observed behaviour is the opposite of the descent they would
need.  The eps1 claim in the ledger has the same shape (no campaign-chain
witness; T not proven).

## 5. Consequence under the project rule

AGENTS.md requires that an FGH-level machine **halt** in the specified
ordinal under `f_ordinal(n)` steps, correctly verified in Rocq with the
rules.  On the evidence above:

* gem48 does not halt on the recorded runs (5M steps, span ~ sqrt t), so it
  has no halting step count and cannot satisfy the rule at any level;
* the eps2/zeta0 theorems are conditional on a chain that is not merely
  unproved but contradicted by the machine's own trajectory;
* therefore gem48 cannot be registered as a champion, and building "more
  machines like gem48" would multiply claims of exactly this kind: tables
  that bootstrap a big ordinal into the tape, then run an oscillator
  forever while a conditional theorem names a level.

The high-(n,k) rows elsewhere in `championsReal.txt` (loader3229's
`f_{w*2}`, `f_{w+2}`, `f_{lim(BMS)}` claims) are honest about this: they
are recorded as the claimant's informal estimates, checked only for parse
and 2M steps without halt.  They are claims, not verified results, and the
same applies to gem48.

## 6. What a real champion needs

1. A halting proof that is parametric in the tape's notation, not a
   concrete run evaluated by `vm_compute` (the repo's `Bounds.v` can only
   reach runs of ~10^8 steps).
2. A well-founded measure that **decreases every round** (Goodstein /
   Hardy style).  gem48's worm gains pairs; it is an ascension.
3. A runtime lower bound whose witness is *constructed*, not assumed.  A
   theorem of the form `chain -> bound` with no chain is vacuous.
4. Zero axioms and `Print Assumptions` closed on the **unconditional**
   theorem, not on a conditional one.
5. Notation of the right arity: a finite list of `(a,b)` pairs is an
   omega^omega-level object at best.  eps2 needs an eps2 notation on the
   tape, and the machine must consume it, not merely write it once.

## 7. Where the repository actually stands

* Verified halting ladder: `Machine1`-`Machine5` (34, 36, 38, 54, 250
  states, 2 symbols), all zero-axiom, all halting, at the `f_2`/`f_3`
  class.  These are real machines, but they are not BB records: BB(n) for
  n >= 34 is astronomically beyond their step counts.
* The next rung is `f_omega`: the stage count must be refilled from the
  previous output.  That needs a block copy of unknown length in two
  symbols; `ModuleK.v` copies but consumes the source, and the parametric
  loop lemma in `StackPass.v` is still open.  This is the blocker, not the
  table.
* The 150-state eps1 table (`tools/eps1_table.py`) implements the eps1
  chain spec and halts on the tested starts, but it exceeds the 67-state
  cap, its eps1-sized halt has never been run, and no Rocq theorem covers
  the table itself.
* `rocq compile -Q . Top gemini_epsilon2_zeta0_tm.v` fails on the
  unqualified `Require Import gemini_epsilon1_tm_48s_v2_fix` (the file was
  built with `coqc -I .`, as `tools/_check_eps2_zeta0.py` does).  The
  artifact is reproducible only through that checker script, not through
  the repo's standard `-Q . Top` workflow.

## 8. Recommendation

Do not add a gem48-family champion row.  The honest next champion attempt
is the `f_omega` rung: define the level claim and the Rocq obligation
first (a constructed chain and a parametric round lemma), then build the
copy/refill primitive, then the table.  Extending the gemini family with
more states or symbols would reproduce the same failure at a larger size.

## Reproduce

    python tools/_audit_fgh_halting.py          # 231-step collapse + 100k no-halt
    python tools/_check_eps2_zeta0.py           # 15 + 12 closed theorems + milestones

The 5M-step table is produced by parsing `Definition trans` in
`rocq/gemini_epsilon1_tm_48s_v2_fix.v` and stepping the exact table with a
set of marked cells; no other simulator is involved.
