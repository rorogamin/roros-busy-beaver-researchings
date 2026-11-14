> **Note (current state).** This file is the historical research log of the
> project, kept section by section as the work progressed.  Many sections refer
> to exploratory Lean files (`Phase.lean`, `Overflow.lean`, `FValue.lean`,
> `Trace.lean`, `FTrace.lean`, `Simulation.lean`, …) that have since been
> removed because no non-halting proof depends on them; they remain in the git
> history.  For the current structure of the proofs see `PROOF_OVERVIEW.md`
> and the audit file `RequestProject/BB25/Check.lean`.

# The 13 unsolved BB(2,5) machines `1RB2LA0RB1LB---_1LA3RA1RA4LB---`

This document summarises what has been **verified in Lean** about the family,
what the verification says about the notes that were supplied
(`2x5 family.txt`, `bb25_family_notes.txt`, `2x5 family longitudinal.xlsx`,
`bb25_family_2RB.rs`), and what is still open.

Everything below marked *verified* is backed by a machine-checked proof in
`RequestProject/BB25/`; the whole development builds with no `sorry` and uses
only the standard axioms.

## 0. Setting

`Machine.lean` defines the family directly from its transition table:

```
        0     1     2     3     4
  A    1RB   2LA   0RB   1LB   ---
  B    1LA   3RA   1RA   4LB    b4
```

with `b4` ranging over the 13 values `2LB, 2RB, 1LB, 1RB, 0LB, 0RB, 3RA, 2LA,
2RA, 1LA, 1RA, 0LA, 0RA`.  A configuration is a pair of lists (the tape on
either side of the head, each listed *nearest the head first*), a state, and
the side the head is reading.  `init` is the blank tape, and
`init_five` verifies the remark at the end of the notes: after 5 steps the
machine is at `^11 A> 1$`, the configuration from which the longitudinal
analysis starts.

The only halting transition is `A4`, so a member halts exactly when the head
reads a `4` in state `A`, and a `4` is only ever written by `B3 = 4LB` —
inside a block `141` (`F`) or `241` (`G`).

## 1. The longitudinal table (verified)

`Rules.lean` proves every rule of the shared longitudinal table, with its
exact base-step count, for **all** members simultaneously (the rules never use
the `B4` transition).  For example

| rule | steps | Lean name |
|---|---|---|
| `03 <A → <A 11` | 2 | `rule_W_A` |
| `01 <A → 11 A>` | 3 | `rule_Z_A` |
| `11 <A → <A 22` | 2 | `rule_X_A` |
| `03 <B1 → <A 141` | 2 | `rule_W_B1` |
| `01 <B1 → <A 11 2>` | 4 | `rule_Z_B1` |
| `11 <B1 → <B1 22` | 6 | `rule_X_B1` |
| `A> 11 → <A 21` | 1 | `rule_A_X` |
| `A> 21 → 03 A>` | 2 | `rule_A_V` |
| `A> 22 → 01 A>` | 2 | `rule_A_Y` |
| `A> 12 → <A 22` | 1 | `rule_A_U` |
| `A> 141 → <A 241` | 1 | `rule_A_F` |
| `A> $ → <A 21 $` | 3 | `rule_A_R` |
| `A> 1$ → <A 2$` | 1 | `rule_A_R1` |
| `A> 2$ → <B1 22 1$` | 11 | `rule_A_R2` |
| `^11 <A → ^11 A> 2>` | 4 | `rule_L_A` |

In particular the two facts singled out in the notes — *"12 turns into 22"*
(`rule_A_U`) and the way `22` is handled (`rule_A_Y`, `rule_X_A`) — are
verified.

`Family.lean` proves the 13 different `A> 241` rules, each with its step
count (3, 3, 3, 3, 3, 3, 5, 7, 5, 9, 6, 5, 5 respectively), together with the
auxiliary rules they generate (`023 <A`, `013 <A`, `003 <A`, `001 <A`,
`011 <A`, `A> 101`, `A> 201`).

## 2. The "head passes through n times" rules (verified)

`Stride.lean` formalises the `↪xn` summary rules of the notes as an inductive
"multi-visit" relation and proves all five:

```
03 ↪xn      →  ↪x(2n) 03 >
11 ↪x(2n)   →  ↪xn 11 >
11 ↪x(2n+1) →  ↪x(n+1) 01 >
01 ↪x(2n)   →  ↪xn 01 >
01 ↪x(2n+1) →  ↪xn 11 >
```

(`mvisit_W`, `mvisit_X_even`, `mvisit_X_odd`, `mvisit_Z_even`, `mvisit_Z_odd`).
These are packaged into an executable *stride* (`strideN`, `stride_visit`)
which replays a whole excursion of the head into the left-hand counter in one
go, and `worked_example` reproduces the worked example of the notes
(steps 268 → 355, 87 base steps) exactly.

## 3. Linked block pairs (verified)

`Pairing.lean` formalises the "linked / remotely linked blocks" observation.
A pair `(g, h)` — a group `g` of left blocks and a group `h` of right blocks —
is **transparent** (`BB25.Transparent`) when

* a `<A` head entering `g` from the right traverses it completely and leaves
  `h` behind: `g rest <A rt ⟶* rest <A h rt`, and
* an `A>` head meeting `h` swallows it and rebuilds `g`:
  `lt A> h rt ⟶* lt g A> rt`.

Proved for every member:

* `transparent_nil` — the empty group is transparent;
* `Transparent.wrapZ` — wrapping a transparent group in `01 … 03` is
  transparent, with image `22 … 21`.  With the empty group this is exactly
  `01 03 <A ⟶* <A 22 21` and its converse `A> 22 21 ⟶* 01 03 A>`;
* `Transparent.wrapX` — wrapping in `11 … 03` is transparent, with image
  `22 … 11`; with the empty group, `11 03 <A ⟶* <A 22 11` and its converse;
* `Transparent.append` — two transparent groups side by side are transparent
  (the right-hand images concatenate in the opposite order).

These three rules generate exactly the pairings described in the notes;
`transparent_remote` is the example `01 (11 03) 03`.  Note the small
correction the formal proof forces: when a transparent group `m` with image
`hm` is wrapped, the image of the wrapped group is `22 hm 21` (resp.
`22 hm 11`) — the inner group is *not* invisible, it deposits its own image
in the middle.  It is invisible in the sense that matters: it does not change
which outer blocks pair up.

The consequence that matters for halting is
`transparent_reaches_left_end`: if everything to the left of the head is a
transparent group resting on `^11`, the head walks all the way down and comes
back out as `^11 A> 2>`, i.e. a pending digit is created.

## 4. Halting criteria (verified)

`Halting.lean`.  A pending digit shifts the phase of the block decomposition,
so that the head can enter a `141`/`241` block on its *second* symbol.  This
is fatal:

* `bhalt_P2_F`, `bhalt_P2_G` — `A> 2> 141` and `A> 2> 241` halt in 3 steps;
* `halt_leftend_F`, `halt_leftend_G` — `^11 <A 141` and `^11 <A 241` halt in
  7 steps (the head bounces off the left end as `^11 A> 2>`);
* `halt_leftend_03_B1` — `^11 03 <B1` halts in 9 steps (`03 <B1 → <A 141`
  creates the `F` right at the left end).

`Family.lean` also records `halt_P1_F`, `halt_P1_G`: `A> 1> 141` and
`A> 1> 241` are not immediately fatal, they turn the head around and leave
the fatal patterns `2> 141`, `2> 241` behind.

## 5. Non-halting criteria (verified)

`Nonhalt.lean`.

* `not_halts_spinout` — the configuration `<A 1122…` at the blank left region
  is periodic with period 8 and drifts left forever;
* `not_halts_leftend_B1` — if the head ever reaches the left end `^11` in
  state `<B1`, the machine never halts.  (So the `<B1` head reaching the
  bottom of the counter is fatal only when it first meets a `03`; if it
  reaches `^11` itself, the machine spins out.)

## 6. The block simulator, and the reduction (verified)

`Blocks.lean` turns the whole longitudinal table into an executable block
simulator `bstep` on block configurations `BCfg` (left blocks
`L, W, X, Z, J, J1, J0, K0, K1`, right blocks `R, R1, R2, U, V, X, Y, F, G,
P1, P2, N1, N2`, head states `A>, <A, <B1`), together with the accelerated
left stride, and proves it **sound**: `bstep_sound`, `bsteps_sound`,
`bstepFast_sound` — one block step is exactly the announced number of base
Turing machine steps.  `bstep` is undefined precisely on the patterns where
the longitudinal analysis breaks down.

`Reduction.lean` proves the qualitative consequence:

> **`not_halts_of_neverStuck`** — if the block simulation of a member never
> gets stuck, that member never halts.

This is not automatic, because the pending-digit rules `1>`, `2>` are pure
re-parsings costing `0` base steps; the proof supplies a measure
(`pmeasure`) that strictly decreases along every zero-cost block step, so
that arbitrarily large numbers of base steps are always covered.

Together with `bstep`, this turns the halting problem for each of the 13
machines into a purely combinatorial reachability question in the block
system.

## 7. Certified running times (verified)

`Simulation.lean` runs the sound accelerated simulator **inside the Lean
kernel** for 2000 block steps for each member, yielding certified lower
bounds on the running time:

| member | `long_run_*` bound | member | bound |
|---|---|---|---|
| `2LB` | `2^54` | `2RA` | `2^55` |
| `2RB` | `2^79` | `1LA` | `2^66` |
| `1LB` | `2^54` | `1RA` | `2^52` |
| `1RB` | `2^46` | `0LA` | `2^52` |
| `0LB` | `2^29` | `0RA` | `2^79` |
| `0RB` | `2^55` | `3RA` | `2^54` |
| `2LA` | `2^39` | | |

(The bounds are what 2000 kernel-checked block steps happen to reach; they
are not intrinsic to the machines.)

## 8. Unverified, exploratory observations

The following came out of the reference simulators in `tools/` and are **not**
machine-checked; they are recorded as a guide for further work.

* The block rules were cross-checked step by step against the base machine
  for all 13 members (`tools/blocksim.py`), and the accelerated simulation was
  run for 50,000 block steps per member without getting stuck (base step
  counts of the order `10^422` … `10^663`).  This is consistent with, but of
  course does not prove, non-halting.
* `2RB` and `0RA` produce identical block runs, confirming the remark in the
  notes that these two members look equivalent.
* Structure of the dynamics.  On the left of the head the blocks are
  `03, 11, 01` over the left end `^11`; on the right they are `21, 22, 11,
  12` over the right end.  A leftward sweep passes `03` (leaving `11`) and
  `11` (leaving `22`) and *turns around* at the first `01`; a rightward sweep
  passes `21` (creating `03`) and `22` (creating `01`) and *turns around* at
  the first `11` or `12`.  This is the "shift-overflow mixed digit counter"
  behaviour: the head bounces between the lowest `01` on the left and the
  nearest `11`/`12` on the right.
* Where the danger comes from.  `F = 141` is created only by `03 <B1 → <A 141`
  and is then always the block nearest to the head on its right; the head
  cannot cross it (`A> 141 → <A 241`), and for the members whose `A> 241` rule
  bounces the head back to the left it is consumed in place.  Consequently the
  simulation appears to always keep at most one `141`/`241` block, and a
  pending digit is never created to its left — except through
  `^11 <A → ^11 A> 2>`.  Making this an inductive invariant would, by
  `not_halts_of_neverStuck`, prove non-halting; this is exactly the gap that
  the notes describe as open, and it remains open here.  Sections 9–11 below
  turn the parts of this picture that *are* local into machine-checked
  statements, and isolate precisely what is left.

## 9. The three sweeps (verified)

`Sweep.lean` introduces multi-step block runs (`BB25.BRun b4 c c' k`: the block
simulation gets from `c` to `c'` at a cost of exactly `k` base steps) and
analyses the three sweeps that make up the dynamics.

**The `<B1` sweep — the only source of `F = 141`.**  `11 <B1 → <B1 22` lets the
`<B1` head walk left through the run of `11` blocks at the top of the left
stack (`brun_Bt_Xrun`); its fate is then decided by the first block that is not
an `11`:

| first non-`11` block | what happens | Lean name |
|---|---|---|
| `03` | the `F = 141` block is created | `brun_Bt_of_dropX_W` |
| `01` | the head is defused into `<A 11 2>`, no `F` | `brun_Bt_of_dropX_Z` |
| none (left end) | the machine spins out, never halts | `not_halts_Bt_of_dropX_L` |
| `023`, `013`, `003` | the machine **halts** (3, 3, 5 steps) | `halts_Bt_of_dropX_J{,1,0}` |

The last line is new: for the three members that push a `023`/`013`/`003`
block onto the left stack (`2RB`, `1RB`, `0RB`), a later `<B1` sweep reaching
such a block is fatal — the head reads the `3`, `B3 = 4LB` writes the `4` next
to it, and the head bounces straight back onto it in state `A`
(`halt_J_B1`, `halt_J1_B1`, `halt_J0_B1` in `Halting.lean`).

So the criterion of the notes — *`F` is created exactly when the leftmost
non-`11` block of the left stack is a `03`* — is verified, for all 13 members.

**The `<A` sweep.**  `brun_Lt_WXrun` walks the `<A` head left through a run of
`03`/`11` blocks, leaving `11`/`22` blocks behind; it turns around at the first
`01`, which becomes an `11` (`brun_Lt_turn_Z`), and if there is no `01` at all
it reaches the left end and a pending digit `2>` is created
(`brun_Lt_reach_L`).  This is the formal version of the observation that *the
head reaches `^11` only when the left stack contains no `01`*.

**The rightward sweep of a pending `2>`.**  `brun_P2_cross`: a pending `2`
crosses `22` and `12` blocks unharmed (pushing `01`, resp. `03`, onto the left
stack) and is still pending afterwards.  Consequently the halting criterion of
§4 can be sharpened: the `141`/`241` block need not sit next to the left end,
it is enough that only `22`/`12` blocks separate it from it
(`halts_leftend_YU_F`, `halts_leftend_YU_G`).

**An `F` created above nothing but `11` blocks is fatal.**  Combining the three
sweeps: if the `<B1` sweep starts when the left stack has the form
`11^n 03 11^a ^11`, so that the `03` which creates the `F` has nothing but
`11` blocks below it, then the machine halts
(`halts_Bt_of_no_Z_below_W`; the intermediate step is `halts_Lt_Xrun_F`).  The
`<A` head finds no `01` to turn around at, walks down to the left end, and the
pending `2>` created there crosses the `22`s it has just deposited and reads
the `4`.  This holds for all 13 members.

**The counter step.**  `brun_round_trip` puts the pieces together into one
round trip of the head, exactly as described in the notes:

```
  11^m 01 <A 11   ⟶   01^m 11 <A 21        (4m + 4 base steps)
```

the head turns at the lowest `01` (which becomes `11`), and on the way back
turns every `11` above it into a `01` and stops at the first `11` on the right,
which becomes a `21`.  One excursion therefore *spends* one `01` but the return
leg can *mint* several: the supply of `01`s is not monotone, which is why the
budget argument sketched in the notes does not close by itself.

`bstep` also gained two rules in this round: `A> 1> 141 → <A 2> 141` and
`A> 1> 241 → <A 2> 241` (one base step each, `halt_P1_F`/`halt_P1_G`).  A
pending `1` in front of a `141` block is *not* fatal — the head turns around —
so this is a genuine rule of the longitudinal table rather than a breakdown of
the analysis.

## 10. A well-formedness invariant, and what "stuck" can mean (verified)

`Invariant.lean`.  Call a member **tame** (`BB25.Tame`) when its `A> 241` rule
is defined and keeps block configurations inside the shared alphabet.  The five
members whose `A> 241` rule bounces the head back to the left without pushing a
new kind of left block are tame:

```
  2LB   A> 241 → <A 12 1>        2LA   A> 241 → <A 22 2>
  1LB   A> 241 → <A 11 1>        0LA   A> 241 → <A 21 1>
  3RA   A> 241 → <A 11 2>
```

(`tame_2LB`, `tame_1LB`, `tame_3RA`, `tame_2LA`, `tame_0LA`).

For these, the predicate `BB25.WF` — the left stack is a stack of `03`/`11`/`01`
blocks resting on `^11`; the right stack uses only `12, 21, 11, 22, 141, 241`
and the pending digits; **at most one `141`/`241` block is present**, and there
is **none while the head is in state `<B1`** — is an *inductive invariant*
(`Tame.wf_bstep`, `Tame.wf_bsteps`), and it holds at the start (`wf_binit`).
This verifies the first half of the last bullet of §8.

Its payoff is a classification of the ways the longitudinal analysis can break
down (`wf_stuck`): a well-formed configuration on which `bstep` is undefined is
either

* **dangerous** (`BB25.Danger`): the head is `A>`, and the right stack begins
  with a pending `2>` in front of a `141`/`241` block.  Then the machine halts
  in three steps (`halts_of_danger`); or
* the head at the left end in state `<B1` — and then the machine spins out and
  never halts.

Hence the sharpened reduction

> **`not_halts_of_no_danger`** — a tame member never halts as soon as its block
> simulation never reaches a dangerous configuration.

This is strictly stronger than `not_halts_of_neverStuck` (the simulation is now
allowed to get stuck, provided it gets stuck at the left end in state `<B1`),
and it reduces halting of each of these five machines to a single question:

> can a pending `2>` ever come to stand immediately in front of the `141`/`241`
> block?

## 11. What is still open

Everything above is local.  The remaining question is a genuine statement about
the counter dynamics, and it is where an inductive invariant would have to do
real work.

After an `F` is created, the right stack is `141 22^n …` and the head is to its
left.  A pending `2>` is produced only at the left end (`^11 <A → ^11 A> 2>`)
or by the `A> 241` rule of `3RA`/`2LA`, and by §9 it is harmful only if nothing
but `22`/`12` blocks separate it from the `141`.  So one wants an invariant of
the shape

> whenever a `141`/`241` block is present, the head reaches it (and consumes
> it) before it reaches `^11` — equivalently, at that moment the left stack
> still contains enough `01` blocks.

The obstruction is exactly the non-monotonicity of §9: turning around at a `01`
spends it, but the return leg mints one `01` for each `11` between that `01`
and the next `03` below it, and the head then stops at the image of that `03`
rather than at the `141`.  Whether the supply can be driven to zero at the
wrong moment is the overflow behaviour of the counter, and it does not seem to
follow from any purely local invariant.

And indeed no local invariant can suffice, because *having a `01` below is not
enough*: the left stack `03 01 ^11` under the `03` that creates the `F` also
kills the machine, in 20 base steps (`halts_WZL_F`, `halts_Bt_WWZL`, verified).
The fate of an `F` depends on the whole "arena" between the left end and the
`141` block; `tools/arena.py` runs that arena for every short left stack and
finds both outcomes in abundance (exploratory, not machine-checked: of the
1093 left stacks of length at most 6, 831 survive, 133 halt, 129 do not decide
within the step budget).  So the answer for a given member depends on which
counter states its own dynamics actually reaches -- which is exactly the
question the notes leave open.

Exploratory evidence (not machine-checked, `tools/blocksim.py`): for each of
the five tame members, 200 000 unaccelerated block steps contain only 3 or 4
creations of an `F`, never more than one `141`/`241` at a time (as now proved),
and no dangerous configuration; the accelerated simulation of all 13 members
survives 20 000 block steps, by which point the base step counts are of the
order `10^123` … `10^228`.

## 12. The shift-overflow counter itself (verified)

Everything above describes the *rules*; this section describes the *counter*
they implement, and is the machine-checked version of the "shift-overflow
mixed-digit counter" reading of the family.  All of it is in
`RequestProject/BB25/Counter.lean`.

**The counter value.**  Read the left stack from the top (nearest the head)
downwards; `cval` is defined by

| block | as a digit | effect on the value |
|---|---|---|
| `11` (`X`) | bit `0` | `v ↦ 2v` |
| `01` (`Z`) | bit `1` | `v ↦ 2v + 1` |
| `03` (`W`) | shift | `v ↦ v / 2` |
| `^11` (`L`) | bottom | `0` |

so a stack without `03` is a plain binary numeral, and every `03` is a *shift*
digit — a mixed-digit counter in the literal sense.  `CStack` says the stack is
well formed (`03`/`11`/`01` blocks resting on the left end).

**The two theorems that make it a counter.**  For a well-formed stack:

* `cval_decrement` — if `cval lt ≥ 1`, the head that enters the stack in state
  `<A` comes back out in state `A>`, the right-hand tape untouched, the stack
  again well formed and of the same length, and `cval` exactly one smaller;
* `cval_overflow` — if `cval lt = 0`, the head does *not* come back out: it
  runs off the bottom of the stack and reaches the left end `^11`.

So `cval` is exactly the number of further round trips the head can make, and
"the counter reaches `0`" is literally "the head reaches the left end".  This
is the fact all the empirical accounting in the notes was circling around.

**The phases.**  The pending digit `1>`/`2>` is the *parsing offset*, and it is
what the wiki's shift-overflow counters call the phase:

* *counter phase* (`countStep`, `brun_count`): no pending digit, the parse of
  the tape is fixed, and the head marches right swallowing one block per
  digit —
  `22 ↦ v ↦ 2v+1`, `21 ↦ v ↦ v/2`, and `11`, `12` in addition turn the head
  around, which costs one excursion: `11 ↦ v ↦ (v−1)/2`, `12 ↦ v ↦ 2(v−1)+1`.
  If the counter is exhausted at such a turn, the head runs off the bottom of
  the stack: that is the overflow, and it starts the
* *reset phase* (`resetStep`, `brun_reset`): the overflow creates a pending
  digit at the left end, which marches right and **re-parses** the tape it
  crosses, one block at a time, each re-parsed block being swallowed
  immediately.  With the offset shifted the roles of `21` and `12` are
  exchanged — `21` is now a bit and `12` a shift — which is where the counter
  regains its digits.  The phase itself (`1>` or `2>`) is carried along by the
  arithmetic, and `1>` costs one extra excursion per block.

This is precisely the wiki's counter-phase/reset-phase alternation: a phase
change here *is* a change of the block offsets, and the reset phase *is* the
re-parse of the tape contents into a new counter.

**Predicting the overflow.**  Because the counter phase is arithmetic, the
overflow can be predicted rather than simulated.  At the right end the head
does a fixed round trip that maps `v ↦ v/2 − 1` while pushing one shift digit,
so the number of round trips before the overflow is `drainCycles v`, and
`two_pow_drainCycles_le` bounds it: `2 ^ drainCycles v ≤ v + 2`, i.e. the
overflow happens after at most `log₂(v+2)` round trips (`brun_drain`).  The
same is true of a whole word: `countRun`/`resetRun` compute the counter value
after an arbitrary word of blocks in one go, and `brun_count`/`brun_reset` say
that the machine really does what the arithmetic says.  This is the sense in
which the analysis reduces to the overflow and the reset: the counter phase
in between never has to be looked at.

The dichotomy is complete: when the arithmetic of a phase *fails* — the counter
is exhausted at a turn — the machine does not get stuck either, it overflows.
`brun_count_overflow` and `brun_reset_overflow` prove that in that case the
head really does reach the left end, which is where the next pending digit,
and so the next reset phase, is created.  So a run of any member is exactly an
alternation of counter phases and reset phases, each of them a piece of
arithmetic, punctuated by the `<B1` events.

**The single danger point, sharply.**  The `<B1` sweep is the only source of a
`141` block, and for the five members whose `A> 241` bounces (`Bounces`:
`2LB`, `1LB`, `3RA`, `2LA`, `0LA`) `brun_Bt_clear` proves that a `<B1` sweep
started with `cval ≥ 1` is survived *completely*: the sweep, the creation of
the `141`, its conversion to `241` and its consumption all happen, and the
configuration afterwards again has a well-formed counter stack and contains no
`141`/`241` at all.  Hence, for those members:

> if the counter is never `0` when a `<B1` sweep starts, the machine never
> halts.

The converse is *not* true and is not claimed: a `<B1` sweep started with the
counter at `0` can also run off the left end of the tape, which is the spinout
of §5 and never halts.  A counter of `0` at a `<B1` sweep is the only *chance*
of halting, not a guarantee of it; which of the two happens is the "arena"
question of §11.

The two packaged cycles are `brun_count_cycle` (a counter phase followed by its
`<B1` event, safe as soon as the predicted value is `≥ 2`) and
`brun_reset_cycle` (a reset phase from the left end followed by its `<B1`
event, safe as soon as the predicted value is `≥ 1`, or `≥ 2` in phase `1>`).

## 13. Two of the thirteen members are the same machine here (verified)

`2RB` writes `023` onto the left stack in its `A> 241` rule, `0RA` writes
`011`; the two blocks behave identically in every block rule (under `<A` both
become `11` and send the head right with a pending `2>`; neither has a `<B1`
rule).  `RequestProject/BB25/Twins.lean` proves that renaming `023 ↦ 011` is an
isomorphism of the two block simulations (`bstep_twin`), so their longitudinal
analyses are literally the same computation and non-halting obtained from the
block analysis of either member transfers to the other (`not_halts_twins`).
Their accelerated simulations do agree word for word at every overflow
(exploratory, `tools/leftwords.py`).

## 14. Growth at the overflow events, and the "Fibonacci" coincidence (exploratory)

`tools/leftwords.py` logs the tape word at every left-end event (every
overflow).  Writing `D = #22 + #21 − #11` for the word at that moment (bits
minus shifts, which is roughly the bit length of the counter the next reset
phase will build), for `2LB` the successive values are

```
0, 1, 3, 6, 6, 8, 20, 28, 48, 82, 136, 216, 364, 608, 1078, 1974, 3628
```

and the tape lengths are `2, 4, 6, 7, 13, 23, 35, 59, 91, 143, 229, 369, 589,
957, 1569, 2651, 4629`.  The Fibonacci-looking coincidences (`8 + 20 = 28`,
`20 + 28 = 48`) are a consequence of the growth ratio passing through the
golden ratio: `D` grows geometrically, and where the ratio `D_{n+1}/D_n`
happens to sit near `φ ≈ 1.618` one automatically gets
`D_{n−1} + D_n ≈ D_n(1/φ + 1) = D_n·φ ≈ D_{n+1}`.  The rule is not exact and
does not persist: the measured ratios for `2LB` drift upwards through
`1.40, 1.71, 1.71, 1.66, 1.59, 1.69, 1.67, 1.77, 1.83, 1.84`, and the defect
`D_{n−1} + D_n − D_{n+1}` runs `0, −6, −6, 2, −12, −28, −106, −288, −576`.  The
same drift shows for the other members, with member-dependent rates (`2RB` and
`0RA` grow by a factor of over `2` per overflow), so there is no universal
Fibonacci law — only a geometric growth whose rate is near `φ` for a few
members over a few events.

Running the accelerated simulator further (`tools/one.py`, exploratory, not
machine-checked): all 13 members survive 60 000 accelerated block steps with no
dangerous configuration, no halt and no spinout — the left stacks are then a
few thousand blocks long.

Two further exploratory observations from the same data, neither
machine-checked: from the fourth overflow onwards `D` is always even, for every
member; and `D` is positive and growing at every overflow, which is why no
member has yet come near the `cval = 0` at a `<B1` sweep that §12 shows to be
the only way to halt.  A search for exact linear conserved quantities of the
block dynamics (`tools/conserved.py`) found only trivial ones, and the letter
counts at successive overflows are not related by any fixed linear map (checked
for all 13 members on the first twelve overflows), so the word at one overflow
is not the image of the previous one under a letter substitution and none of
the standard "closed-form" accelerations applies.

## 15. Status

No member of the family has been decided, and nothing above claims otherwise.
What §12 buys is that the question is now a purely arithmetical one for the
five bouncing members — *is the counter ever `0` when a `<B1` sweep starts?* —
with the counter, its decrement, its overflow and both phases proved to behave
as the arithmetic says.  The obstruction to going further is the one in §11:
the words that the reset phase re-parses look pseudo-random, the survival
margin is not given by any local invariant, and the growth of `D` (§14) is
evidence, not a proof.

## 16. The two counters, the overflow and the reset (verified)

Sections 12–14 followed the *left* counter.  This section is about the right
half of the tape as a counter in its own right, and about the two events that
join the two halves: the **overflow** and the **reset**.  Everything called
verified here is in `RequestProject/BB25/Phase.lean` and
`RequestProject/BB25/Overflow.lean` and is machine-checked with no `sorry`
(axioms `propext`, `Classical.choice`, `Quot.sound` only).

### 16.1 It is a two-sided counter, and the two sides use different digit tables

`cval` (§12) is the value of the **left** counter only.  The word of digit
blocks lying to the right of the head is the **right** counter, and it now has
a value of its own — with, as the wiki's shift-overflow reading predicts, a
*different digit representation on each side and in each phase*.  The
representations are (`digit_roles_swap`):

| block | counter phase | reset phase (`2>`) |
|---|---|---|
| `22` (`Y`) | bit `1` (`v ↦ 2v+1`) | bit `1` (`v ↦ 2v+1`) |
| `21` (`V`) | shift (`v ↦ v/2`) | **bit** `1` (`v ↦ 2v+1`) |
| `12` (`U`) | **bit** `1`, one excursion (`v ↦ 2(v−1)+1`) | shift (`v ↦ v/2`) |
| `11` (`X`) | shift, one excursion (`v ↦ (v−1)/2`) | shift (`v ↦ v/2`) |

so `21` and `12` swap roles between the phases: the same tape carries two
different numerals depending on which phase reads it.  A single `cval`-style
number could not express this, which is why the right-hand value is carried by
a **shift map** instead:

```
    SMap ⟨c, d, e, f⟩ :   v ↦ ((v − c) / 2^d) · 2^e + f          (defined for v ≥ c)
```

* `f` — the value of the right-hand counter: the numeral the word carries in
  the representation the current phase uses;
* `e` — its number of digits (`f < 2^e`, `SMap.WF`);
* `d` — how many digits of the *left* counter the word consumes;
* `c` — the exact threshold: the phase runs to the end of the word iff the
  left counter is at least `c`.

`cmap w` computes it for the counter phase and `rmap ph w` for the reset phase
(together with the phase the word ends in).  The theorems that make this the
law joining the two counters are `countRun_cmap` / `resetRun_rmap` (the
arithmetic) and the two **dichotomies** `brun_count_dichotomy` /
`brun_reset_dichotomy` (the machine): reading a word of digit blocks, the head
either arrives at the far end with the left counter equal to `((v−c)/2^d)·2^e+f`
and the predicted pending digit, or — exactly when `v < c` — overflows to the
left end.  There is no third possibility and no getting stuck.

Two structural facts follow.

* **One pool of blocks.**  At the level of blocks a phase moves blocks from the
  right half to the left half one for one: `brun_cstackRun` gives
  `lt'.length = lt.length + w.length`.  The "two" counters are two halves of a
  single pool, which is exactly the picture of a two-sided counter whose total
  size only grows at the overflow.
* **Growth.**  `cmap_digit_count` / `rmap_digit_count`: `e − d` equals
  `#bits − #shifts` of the word.  So the phase multiplies the left counter by
  `2^(#bits−#shifts)`; that exponent is the quantity `D` measured empirically
  in §14.

`digit_counts_differ` exhibits the swap numerically: the word `21 21 22` has
1 bit and 2 shifts in the counter phase (`cmap = ⟨0,2,1,1⟩`) but 3 bits and no
shift in the reset phase (`rmap true = (true, ⟨0,0,3,1⟩)`) — the same tape, the
values `1` (over one digit) and `7` (over three digits).

### 16.2 The overflow, explicitly

When the left counter runs out the head walks off the bottom of the stack.  Two
explicit functions describe what that does.

* `cdec` — the decrement as an operation on the *stack*, i.e. the borrow:

  ```
      01 s  ↦  11 s                (borrow stops:   the value was odd)
      11 s  ↦  01 (cdec s)         (borrow travels: the value was even)
      03 s  ↦  03 (cdec (cdec s))  (a shift digit costs *two* decrements)
  ```

  `brun_cdec` proves the machine performs it, `cdec_cval` that it subtracts one,
  and `cdec_run_of_zeros` that the borrow crosses exactly the trailing zeros:
  `11^m 01 s ↦ 01^m 11 s`.

* `ofw` — the word the overflow deposits.  On the way out the head converts
  every block of the left stack into one block of the tape
  (`brun_overflow_word`, `ofw_length`, `ofw_CWord`):

  ```
      11 (bit 0) ↦ 22        03 (shift) ↦ 11   if the counter below is exhausted
                                        ↦ 21   otherwise (one decrement is spent)
  ```

  So the overflow **re-encodes the whole left counter into the right-hand
  digits**, block for block, and hands it to the reset phase, which parses it
  back with the *other* table.

Putting the two together, `brun_overflow_reset_cycle` gives one full turn of
the cycle in closed form: from a left counter that has just run out, the
machine reaches the far end of the deposited word with the pending digit
`(rmap true (ofw lt)).1` and the counter value `(rmap true (ofw lt)).2.f`,
provided the deposited word does not ask for a decrement the empty counter
cannot pay (`c = 0`; §16.4 reports that empirically it never does).
`reset_value_bound` bounds the rebuilt counter by `2^(number of blocks)`, and
`overflow_reset_of_zero_bits` shows the bound is attained: a counter of `n`
zero bits overflows to `n` copies of `22`, which the reset reads as `n` one
bits, so it comes back as the full counter `2^n − 1`.

### 16.3 Does the reset depend on the value of the counter?

This is the question that decides whether the family is a "reset depends on
`v mod k`" counter.  The verified answer is in two parts.

* **Inside a phase, no.**  The whole of a phase — counter or reset — is the
  single shift map above.  The only way `v` enters is through `⌊(v−c)/2^d⌋`
  and through the all-or-nothing threshold test `v ≥ c`.  A residue of `v`
  mod `2^d` is *discarded*, never branched on: no phase ever takes a different
  route according to `v mod k`.  `countRun_no_residue_dependence` and
  `resetRun_no_residue_dependence` state it directly — two counter values with
  the same quotient are indistinguishable to the phase, output value and
  pending digit alike — and it is why the phases can be predicted instead of
  simulated.

* **At the overflow, yes — but locally, digit by digit.**  The word that is
  handed to the next reset is not a function of the shape of the stack alone.
  At each shift block `03`, `ofw` writes `11` or `21` according to whether the
  counter standing *below that block* is exhausted, and how far the borrow of
  `cdec` travels is fixed by the trailing zeros below it.  When the sub-counter
  is `0` or `1` — which is what the two decrements a shift digit costs leave —
  the test is exactly its low bit (`ofw_W_low_bit`): the digit written is the
  **parity of the counter below**.  `overflow_word_value_dependent` makes this
  concrete: the two stacks `03 03 11 01 ^11` and `03 03 01 11 ^11` have the
  same length, the same multiset of blocks and the same value `0`, but they
  deposit `22 22 11 21` and `22 22 21 11` and the following reset rebuilds `1`
  in one case and `3` in the other.

So there *is* value dependence, and it is exactly where one would look for a
"reset mod `k`" law — but it is not a single global residue test.  It is a
digit-local one: each shift digit of the counter is re-encoded according to the
low bit of the sub-counter beneath it.  A reset rule of the form "if
`v ≡ r (mod k)` then …" would have to be a consequence of that whole family of
local tests, and nothing in the verified material produces one.

### 16.4 What the 13 members actually do

Two of the observations below are **machine-checked**, in
`RequestProject/BB25/Trace.lean`, by running the accelerated block simulator of
`Blocks.lean` inside the kernel from the blank tape and computing the shift map
of each reset word with `rmap`:

* `shared_overflow_prefix` — **the 13 members share their first five
  overflows**: for every member the first five reset phases re-parse words with
  the shift maps `⟨0,0,0,0⟩`, `⟨1,0,1,1⟩`, `⟨0,0,3,5⟩`, `⟨0,0,6,57⟩`,
  `⟨0,0,6,53⟩`, i.e. they rebuild the counters `0, 1, 5, 57, 53`.  This is the
  shared prefix of the family, in phase-level form.
* `reset_maps_clean` — **the resets neither borrow nor delete digits**: within
  4000 accelerated block steps every member reaches at least seven overflows,
  and every reset word except the second has `c = 0` and `d = 0`.  `c = 0` is
  exactly the hypothesis of `brun_overflow_reset_cycle`, so on this stretch the
  overflow–reset cycle really is the closed-form one; `d = 0` says the reset
  deletes no counter digit and simply reads the deposited word as a binary
  numeral.

The rest of this subsection is exploratory.  `tools/phases.py` logs, for each
member, the shift map `(c,d,e,f)` of the word
each reset phase re-parses and the counter value at each `<B1` event.  Over all
13 members, the first 14 overflows (≤ 400 000 accelerated block steps):

* **`c = 0` and `d = 0` at every logged reset except the second** — the two
  verified facts above continue to hold out to the fourteenth overflow of every
  member.  The members diverge from the sixth overflow on.
* **The rebuilt counter `f` is odd from the second overflow onwards**, and from
  roughly the sixth it satisfies `f ≡ 1 (mod 8)` for every member; every reset
  from the fourth onwards ends in the pending digit `1>`.
* `e` grows geometrically and member-dependently (for `2LB`:
  6, 8, 20, 28, 48, 82, 136, 216, 364, 608; for `0RB`:
  24, 46, 84, 170, 554, 1274, 2682, 5970, 14288), matching §14.
* At the `<B1` events the counter is even in every logged event of every member
  **except one**: `1LA` reaches a `<B1` sweep with `cval = 25`.  So "the
  counter is even at every `<B1`" is *false* for the family.  For five members
  (`2RB`, `1RB`, `0RB`, `2RA`, `0RA`) some `<B1` events occur with a left stack
  that is not a pure counter stack at all, so no `cval` is defined there.
* `1LA` is also the one member whose `<B1` counter values stay small and repeat
  (`56, 52, 50, 98, 194, 52, 25, 48`) while its reset words keep growing; the
  other members' `<B1` counters grow with `e`.

Apart from the two theorems named at the start, none of §16.4 is
machine-checked; the rest is the output of a simulator and should be
read as evidence about where to look, not as proof.  In particular the smallest
counter seen at any *logged* `<B1` event, over all members, is `25` (`1LA`) —
still not the `0` that §12 shows to be the only chance of halting.

## 17. The rebuilt counter `f`: what invariant of it can decide halting (verified)

`RequestProject/BB25/FValue.lean` and `RequestProject/BB25/FTrace.lean`.  Everything in
this section is machine-checked (axioms `propext`, `Classical.choice`,
`Quot.sound`; the two kernel computations use `propext` only) unless it is
marked as exploratory.

### 17.1 The danger is a lower bound on `f`, not a congruence

§16 reduced one turn of the cycle to the number `f` the reset hands back:
`brun_reset_cycle` survives the `<B1` event at the far end when `f ≥ 1` (reset
ending in phase `2>`) or `f ≥ 2` (phase `1>`).  `reset_cycle_of_f_ge_two`
packages this in terms of the shift map of the word: for a bouncing member
(`Bounces b4`), a reset word `w` of digit blocks with `c = 0` and `f ≥ 2` is
crossed, the `<B1` event survived, and the machine comes back to the left end
with a well-formed counter stack and no `141`/`241` block anywhere;
`danger_iff_f_le_one` is the converse reading.

The empirical `f ≡ 1 (mod 8)` of §16.4 is now explained *and disqualified*.  A
run of `21` blocks is read in phase `1>`, so each block first decrements and
then pushes: `f ↦ 2f − 1`, i.e. `f − 1` doubles (`rmapFrom_Vrun`).  A trailing
run of `n` such blocks therefore forces `f ≡ 1 (mod 2^n)` (`rmapFrom_Vrun_mod`)
— but it fixes the dangerous value: `f = 1` after the run exactly when `f = 1`
before it (`rmapFrom_Vrun_eq_one_iff`).  **No congruence on `f` can certify
non-halting**; a lower bound is needed.  (A run of `22` blocks is the other
exact law: `f + 1` doubles per block, `rmapFrom_Yrun`.)

### 17.2 The deficit and the normalised value

The right quantity is the deficit `δ = 2^e − (f+1)`, equivalently the normalised
value `t = (f+1)/2^e ∈ (0,1]`.  Its laws are exact:

| block | deficit | normalised value |
|---|---|---|
| bit (`push`) | `δ ↦ 2δ` (`deficit_push`) | unchanged (`tval_push`) |
| shift (`pop`) | `2δ' ≤ δ` (`deficit_pop`) | does not decrease (`tval_pop`) |
| decrement (`dec`) | `δ ↦ δ + 1` (`deficit_dec`) | drops by at most `2^-e` (`tval_dec`) |

So `t` is monotone: it only ever decreases, and only at decrements, by `2^-e`
each — the deeper the counter, the cheaper a decrement.  Summing the losses
along a word gives the *cost* `rcost w` (`rcostFrom`) and the bound
`tval_rmapFrom_ge`.

**The criterion (`rmap_f_lower`).**  If `rcost w ≤ 1/2` then
`2^(e−1) ≤ f + 1`: the top bit of the rebuilt counter is set.  With `e ≥ 3`
this gives `f ≥ 3` (`rmap_f_ge_two`) and hence survival of the whole cycle
(`reset_cycle_of_cost`).  This is a *non-modular* invariant, and it is the one
the data actually shows: the rebuilt counter has exactly `e` binary digits at
every overflow of every member.

Two decidable forms of the same criterion:

* integer, at a fixed scale: `2 * rncost K w ≤ 2^K` implies `rcost w ≤ 1/2`
  (`rcost_le_half_of_nat`, `reset_cycle_of_ncost`) — this is what the kernel
  checks below, since rational arithmetic does not reduce well in the kernel;
* counting: if every decrement happens at digit count ≥ `m` and the word has at
  most `2^(m−1)` decrements, the word is cheap (`rcost_le_half_of_deep`).  This
  form is only sufficient: of the reset words of `2LB` it certifies all but the
  fourth (12 blocks, 5 decrements, shallowest decrement at `e = 3`), which the
  exact cost still passes comfortably (`0.184 < 0.5`).

### 17.3 The criterion checked against the runs

`FTrace.lean` collects the configurations at which the accelerated simulator
finds the head at the left end with the counter exhausted (`ovCfgs`; every one
of them really occurs in the run, `ovCfgs_reachable`) and tests each of them
with `ovSafeCfg`: the tape ahead of the head is a word of digit blocks followed
by the end marker, the word needs no borrow (`c = 0`), it builds at least three
digits, and it is cheap in the integer form at scale `2^256`.

* `overflow_words_safe` — kernel-checked: within 4000 accelerated block steps
  **every one of the 13 members** reaches at least seven overflows (in fact 9
  to 12), and every overflow from the fourth on passes the test.
* `overflow_top_bit` — consequently the counter rebuilt at each of those
  overflows has its top bit set, `2^(e−1) ≤ f + 1`, and in particular `f ≥ 3`.
  This is *derived from the cost*, not read off the value.
* `bouncing_overflows_survived` — for the five members whose `A> 241` bounces
  (`2LB`, `1LB`, `3RA`, `2LA`, `0LA`) every one of those overflow events is
  provably survived: each ends with a well-formed counter stack and no
  `141`/`241` block on the tape.

The first three overflows are the degenerate ones (`f = 0`, `f = 1`, and a word
that ends in a pending `1>` block) and are excluded from the test.

### 17.4 What this does and does not settle

It settles the shape of the argument: for a bouncing member, **non-halting
follows from the single statement "every reset word is cheap"**, and cheapness
is a local, propagatable property of the deposited word — unlike a congruence,
which §17.1 shows can never suffice.  It does not settle any member: the check
above is a finite certificate covering an initial stretch of each run (nine to
twelve overflows), and proving that cheapness propagates from one overflow to
the next would require controlling the word `ofw` that the overflow deposits,
which is still open.  Exploratory (simulator only): the measured costs of the
`2LB` reset words fall off fast — `0.25, 0.094, 0.184, 0.064, 0.0073, 0.0041,
0.00098, …` — so the criterion is not tight on the runs, which is what one
would want of an inductive invariant.

## 18. Verification of the submitted `3RA`/`2LA` prefix-safety proof

The archive `bb25_3RA_2LA_prefix_safety.zip` (unpacked in
`submissions/bb25_prefix_safety/`) contains a prose proof (`PROOF.md`) that the
two members

```
  1RB2LA0RB1LB---_1LA3RA1RA4LB3RA        (B4 = 3RA)
  1RB2LA0RB1LB---_1LA3RA1RA4LB2LA        (B4 = 2LA)
```

never halt, together with Python checkers and an uncompiled Lean seed file.
The submission states that its argument was **not** machine-checked.  It has
now been formalized in full, against the block simulator of this project, in
`RequestProject/BB25/Prefix/`:

| file | content |
|---|---|
| `Word.lean` | the reset arithmetic `rstep`/`rrun`, the transducer `qout`/`trun`, Dyck prefixes, and Lemma 3 (`trun_ge_of_hasCl`, `trun_ge_two`) |
| `Stack.lean` | the decoder `pdec`/`bval`, the invariants `Adm`/`Good`, and the identification `ofw = pdec` of the word an overflow deposits with the decoded word of the stack |
| `Reset.lean` | the paid reset stack `tfold`, its arithmetic (Lemma 2, `tfold_props`) and the machine correspondence `brun_paid` |
| `Return.lean` | the return theorem `cp_returns`, its cases (Lemmas 4 and 5, the early overflows and the left-end spinout) and `not_halts_of_safeCP` |
| `Main.lean` | the seed (`seed_run`, `safeCP_seed`) and the conclusions `not_halts_3RA`, `not_halts_2LA` |

### 18.1 What is now machine-checked

* **Safe checkpoints.**  `SafeCP s` is the submission's invariant: the stack is
  a well-formed counter, it is *admissible* (every suffix has at least as many
  bit blocks as pops, so no pop underflows), it is *good* (on every suffix the
  counter value is at most the decoded reset value `bval`), and its counter is
  positive.
* **Lemma 2 (paid reset).**  `tfold_props`: re-parsing a clean word of digit
  blocks from a good admissible stack yields a good admissible stack whose
  counter is the reset value `rrun` of the word and whose decoded value is the
  transduced value `trun`.  `brun_paid` shows the machine really performs that
  re-parse, including the one-decrement debt carried by a pending `1>`.
* **Lemma 3 (matched groups).**  `trun_ge_of_hasCl`: a Dyck prefix containing a
  completed pair takes the second counter from `c` to at least `4c+2`; hence
  `trun_ge_two`, inequality (7) of `PROOF.md`.
* **Lemma 4 (protected drain)** `returns_strong` and **Lemma 5 (pending tail)**
  `returns_tail`.
* **The return theorem** `cp_returns`, for any member whose `A> 241` rule
  leaves a bit block and a pending `2>` behind (`GBit`), which covers `3RA`
  (`gBit_3RA`, cost 5) and `2LA` (`gBit_2LA`, cost 7).
* **The early overflows** `returns_overflow`, including the exceptional case
  `d = X` with decoded value `0` or `1`, whose sub-case with an empty stack is
  the left-end spinout: the nine-step identity (10) of `PROOF.md` is
  `xy_spinout_step`, and `not_halts_xy` iterates it.  As claimed, the identity
  holds for every value of the `B4` transition.
* **The seed.**  `seed_run`: after exactly 156 steps the blank tape reaches
  `L ZZZXXX <B1 22 1`, again for every value of `B4`; `safeCP_seed` checks the
  six prefix comparisons (counter 56, decoded value 63).
* **The conclusion.**  `not_halts_3RA` and `not_halts_2LA`, with no `sorry` and
  only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

### 18.2 Deviations from the prose proof

The formalization follows `PROOF.md` step by step, with two presentational
differences, both verified in Lean:

* `PROOF.md` re-parses the tape suffix `2> 22^r 1` as `22^r 21` and treats the
  whole early-overflow word as `u d Y^r V R` (an identity of raw tape symbols).
  The Lean proof instead keeps the pending digit as a block and lets the
  machine cross the `22` run, which is the same computation at block level and
  needs no re-parsing identity.
* In the exceptional case the Lean proof reaches the pending-tail form of
  Lemma 5 directly rather than the strong `A> R` form of Lemma 4; both end at a
  safe checkpoint.

No error was found in the submitted argument.

### 18.3 Independent numerical checks

`tools/prefix_check.py` re-runs the block simulation of both members from the
blank-tape start with an independent implementation of `cval`, `bval` and the
goodness test, and confirms that the invariant holds at every checkpoint the
run reaches (no failure within 20000 block steps of either member).  This is an
exploratory check only; the statements of §18.1 are the machine-checked ones.

## 19. Three further members: `1RA`, `0LA` and `2LB`

The second submission (`bb25_1RA_0LA_2LB_nonhalting.zip`, document
`PROOF_MORE.md`) extends the prefix-safety argument of §18 to

```
1RA: 1RB2LA0RB1LB---_1LA3RA1RA4LB1RA
0LA: 1RB2LA0RB1LB---_1LA3RA1RA4LB0LA
2LB: 1RB2LA0RB1LB---_1LA3RA1RA4LB2LB
```

It has now been verified in Lean.  The three conclusions are

```
BB25.Prefix.not_halts_1RA : ¬ Halts (M b4_1RA) init
BB25.Prefix.not_halts_0LA : ¬ Halts (M b4_0LA) init
BB25.Prefix.not_halts_2LB : ¬ Halts (M b4_2LB) init
```

in `RequestProject/BB25/Prefix/Main.lean`, with no `sorry` and only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`.

### 19.1 How the development was reorganised

| file | contents |
| --- | --- |
| `Drain.lean` | the milestones of a return: the three-fold drain invariant `Strong` (Lemma 1 of `PROOF_MORE.md`), the pending-`2>` tail `returns_tail` (Lemma 2), the early overflows and the left-end spinout, and the bit-block case `returns_dP2`; also the goodness-free variant `returns_dX_weak` |
| `Return.lean` | the member-independent `<B1` sweep.  The member-specific branch is abstracted as `WCase b4`: *from `L c <A 141 22…1` with `c` good, admissible and `cval c ≥ 2` the machine returns*.  Granting it, `cp_returns` and `not_halts_of_safeCP` hold for that member |
| `Expand.lean` | counting *expanding* closes (`qcnt`) in a decoded word, and the height-sensitive bounds `trun_ge_pow`, `trun_ge_pow_q1`, `trun_ge_pow_q2` (Lemma 3 and Corollary 3.1), together with `rrun_mod_four_ne` (the structural half of Corollary 3.2) |
| `Bit.lean` | `WCase` for `1RA` |
| `Except.lean` | the runs shared by `0LA` and `2LB`, the facts about the paid stack of an exhausted counter of value two (`paid_stack_facts`, `paid_stack_mod_four`), and the goodness-free tail `returns_P1_tail_weak` |
| `Zero.lean`, `Two.lean` | `WCase` for `0LA` and for `2LB` |

The drain invariant was weakened from the four-fold to the three-fold form
while doing this, exactly as Lemma 1 of `PROOF_MORE.md` asks.

### 19.2 What is machine-checked

* **`1RA`** (`wcase_1RA`).  Its rule `A> 241 → 11 A> 2>` pushes a zero bit on
  the left stack, which preserves goodness, so the ordinary tail lemma applies
  and no exceptional checkpoint arises.
* **The two barriers of Corollary 3.2.**  `paid_stack_facts` ends with the
  dichotomy *the counter of the paid stack is odd, or its decoded value is at
  least 11* — this is (13).  `paid_stack_mod_four` is (12): a decoded value
  divisible by four forces at least two expanding closes (`rrun_mod_four_ne`),
  hence `trun ≥ 11·2^h − 1 ≥ 43`.  Both are proved from the word-level theory
  of `Expand.lean`, with no finite search.
* **`0LA`** (`wcase_0LA`).  With a counter of at least three the three
  decrements are available and the stack stays good (`wcase_0LA_ord`).  With a
  counter of exactly two the machine reaches the exceptional checkpoint
  `W :: X :: t`, of counter `f = cval t` and decoded value `bval t − 1`
  (equation (22)).  If `bval t ≥ f+1` it is good and the sweep returns at once;
  otherwise `bval t = f` and the repair of §6 is carried out: `r = 1` falls back
  to the ordinary case with the counter `X :: t` of value `2f ≥ 8`, and `r ≥ 2`
  meets a bit block, where `returns_dX_weak` needs only the numerical bound
  (`3A ≤ 16C+11` for odd `A`, and `f ≥ 8` for even `A`, supplied by (13)).
* **`2LB`** (`wcase_2LB`).  Its rule leaves a residual `12` block, so the sweep
  needs *four* decrements.  Counter at least four: ordinary
  (`wcase_2LB_ord_weak`).  Counter three: the fourth decrement overflows and
  the residual `22` block of the turn pushes a one bit, so the checkpoint stack
  `W :: Z :: t` is good because the counter below the pop is odd
  (`wcase_2LB_a3`).  Counter two: the exceptional checkpoint `W :: W :: t`,
  repaired as in §7 of the document.  The tight sub-case is a counter divisible
  by eight, which is exactly where (12) applies and gives `bval t ≥ 43`, hence
  `f ≥ 40` and `A₀ = f/4 ≥ 10`.

### 19.3 Deviations from the prose proof

No error was found in the submitted argument.  The Lean development differs
from it in the following places, all of them simplifications that were
themselves verified.

* **The numerical content of the `2LB` exception is proved once.**
  `exc_2LB_arith` derives, from *"the checkpoint stack `W :: W :: t` is not
  good"* together with (12) and (13), everything the repair needs: `f ≥ 8`,
  `A₀ ≥ 2`, `C₀ ≥ A₀ − 2` and — when `A₀` is even — `3(A₀/2) ≤ 4(C₀/2)`.  The
  document instead splits into the residues (24) and (25) of `f` modulo four.
* **Two sub-cases of §7 do not occur.**  Because `f ≥ 8` in every non-good
  case, the case `a' = 3` (that is `f = 6`) of §7 `r = 1`, and the case `A = 1`
  of §7 `r ≥ 2`, are vacuous; the separate overflow arguments the document
  gives for them are not needed.
* **A goodness-free tail instead of a restored invariant.**  For the `r = 1`
  repair of `2LB` the document argues that the two decrements before the `241`
  block restore goodness of `t W`.  The Lean proof keeps the stack as it is and
  uses the numerical form of the tail lemma (`returns_P1_tail_weak`, which
  needs only `0 ≤ bval` and `3 cval ≤ 4 bval + 4`); this is why the ordinary
  `2LB` case is stated as `wcase_2LB_ord_weak`, with the hypothesis
  `3 cval c ≤ 4 bval c + 14` in place of goodness.
* **The sweep is factored through `WCase`.**  The document proves a return
  theorem for each member separately; here the sweep, the early overflows and
  the spinout are proved once for all members and only the `A> 241` branch is
  member-specific.

### 19.4 Scope

Eight of the thirteen open members remain.  The arguments above use the
`A> 241` rule of the member only through `WCase`, so any further member whose
rule can be pushed through the same three lemmas — an ordinary case that keeps
the invariant, and an exceptional case whose checkpoint returns to the
invariant one sweep later — can be added by proving `WCase` for it.

## 20. Four more members: `0RA`, `2RB`, `2RA` and `1LB`

These four were verified after §19 was written, and the notes were not updated
at the time; this section records them.  All four are proved non-halting from
the blank tape in `RequestProject/BB25/Prefix/Main.lean`
(`not_halts_0RA`, `not_halts_2RB`, `not_halts_2RA`, `not_halts_1LB`), through
the same route as the earlier members: the seed checkpoint of `Main.lean`, the
sweep of `Return.lean`, and a member-specific proof of `WCase`.

### 20.1 The one-use markers: `0RA` and `2RB` (`Prefix/Marker.lean`)

```
  0RA :  A> 241  ⟶  011 A>     (five steps)      K1 = 011
  2RB :  A> 241  ⟶  023 A>     (three steps)     J  = 023
```

The `241` block becomes a block on the *left* stack and the head carries on to
the right.  Both blocks obey the same rule at the next leftward visit,
`K1 <A ⟶ 11 A> 2>` and `J <A ⟶ 11 A> 2>`: the marker turns into a zero bit, the
head turns around and a pending `2>` appears — exactly what the left end of the
tape does, except that a bit is left behind.  So the marker is a *movable left
end*: the counter the sweep builds above it drains against it and overflows on
to it, and only then does the machine see the stack below again.

`marker_core` runs that local episode, in three cases according to the number
`n` of one bits the sweep left above the marker (`n = 0` and `n = 1` are finite
calculations, `n ≥ 2` is a real drain, `drain_rep`).  The factorisation
`wcase_of_core` isolates the part of the sweep that does not depend on the
marker rule, and is reused by `2RA` and `1RB`.  Because the checkpoint ends in
a zero bit, the sweep always strips at least one `11` block, which is what
makes `n` well defined.

### 20.2 A two-stage marker: `2RA` (`Prefix/K0.lean`)

`A> 241 ⟶ 001 A>` leaves `K0 = 001`, which is *not* a movable left end: at the
first leftward visit `K0 <A ⟶ 01 A>` it behaves like an ordinary one bit (and
becomes the marker `K1`), and only the second visit creates the pending `2>`.
So the episode has two halves: the counter above `K0` drains and overflows on
to it, the marker becomes `K1` and the head turns around **without** a pending
digit — it therefore re-reads the deposited word in the *counter* phase, which
has no general theory here (the stack it rebuilds need not be good).  It does
not need one: `drain_rep_word` gives the deposited word exactly,
`kword n = 22^n 21 22 22 21 11 21^(n-1)`, and `free_cycle` follows the counter
phase over that explicit word; the counter it rebuilds is exhausted and
deposits the same word again, one `21` block longer.

### 20.3 A one-unit deficit and its repair: `1LB` (`Prefix/One.lean`)

`A> 241 ⟶ <A 11 1>` leaves a residual zero bit and a **pending `1>`** — one
decrement owed — and the head sweeps left.  With a counter of at least four
below the pop the sweep is ordinary.  With a counter of three or two it runs
out during those decrements, the head overflows, and the checkpoint the machine
then reaches can fail the goodness invariant — but only by one unit.
`repair_return` shows that such a checkpoint still returns, because the
numerical bound the drain needs survives a deficit of one as soon as the
counter is at least three, and at least eight when it is even.  The small even
counters are excluded by the expansion barriers of `Expand.lean`: a decoded
word of height at least two whose value is even has an expanding close, hence
value at least `11`, and one whose value is `2 mod 8` and at least `4` has two
of them, hence value at least `43` (`paid_stack_mod_eight`).

No error was found in the submitted arguments for these four members.

## 21. The tenth member: `1RB` (`Prefix/JOne.lean`)

```
  A> 241  ⟶  013 A>      (three steps)      J1 = 013
  J1 <A   ⟶  <A 11 2>    (five steps)
```

`1RB` pushes a marker like `0RA`/`2RB`, so the local episode above the marker
is the same (`marker_drain`, via the shared `wcase_of_core`).  The difference
is what the marker does when the head comes back to it: it disappears **without
leaving a bit behind**, and the head keeps going *left*, with a `11` block and
a pending `2>` in front of it.  The configuration handed back is therefore
`c <A 11 2> w`, where `c` is the counter stack that was below the `141` block
and `w` is the word the local overflow deposited.  Two cases:

* `cval c ≥ 2` (`returns_j1_ord`): the head pays the two decrements the `11`
  block and the pending digit ask for, pops, and `w` is re-parsed in the
  ordinary **reset** phase over the good stack `03 D²(c)`.  For a long sweep
  `w = kword n`, which ends in a `21` block and has positive value, so the
  reset ends at a checkpoint (`returns_reset_end`).  For the two short sweeps
  `w` is `11` resp. `22 21`, followed by a second pending `2>` and the tail.
* `cval c ≤ 1` (`returns_j1_small`): the decrements are unavailable, the head
  runs off the left end, the decoded word of `c` is reset first — and the two
  pending digits then **cancel** (`returns_merge`: `2> 2>` re-parses to a `22`
  block), so that `w` is read in the **counter** phase over the rebuilt stack.

The new ingredients, all in `Prefix/JOne.lean`, are that cancellation; the
three deposited words read in the counter phase (`returns_ct0`, `returns_ct1`,
`returns_ctk`); and, for `returns_ctk`, the observation that `kword n` is a
*balanced* word: read in the counter phase it gives the counter back — after
the single decrement its `11` block costs — and multiplies the decoded value by
`2^(2n+2)`, which is far more than the drain at the right end needs
(`Wrun_facts` computes the tower of pops that ends the word).

Two margins of the checkpoint are used.  `WCase` was strengthened to carry the
general even margin, `cval c` even `→ cval c + 2 ≤ bval c`, which the goodness
of the checkpoint stack at the pop supplies; and `wcase_of_core` now also hands
the local episode the height bound `2 ≤ nbit c - nsh c`, which is what the
expansion barrier of `Except.lean` needs in the exceptional case
`cval c = 0`.  No error was found in the submitted argument for `1RB`.

With this member, ten of the thirteen are proved non-halting from the blank
tape: `3RA`, `2LA`, `1RA`, `0LA`, `2LB`, `0RA`, `2RB`, `1LB`, `2RA`, `1RB`.

## 22. `1LA`: what the submitted argument needs, and what is verified

`1LA` is genuinely different: its rule

```
  A> 241  ⟶  <B1 22        (nine steps)
```

does not end the `<B1` sweep.  After the two decrements the head is back in
state `<B1` on the stack `D²(c)`, with one more `22` block in front of it, so
the sweep **continues** and can consume several pops in a row, each costing two
decrements of the counter below it.  If some pop is met with a counter below
two, the head meets the `241` block out of phase and the machine halts in three
steps.  Goodness of the checkpoint is therefore not sufficient — and the
submitted document gives the explicit counterexample `L ZXZWWX <B1 22 1$`,
which is good, positive and `X`-ending, but whose scan strips a `11`, consumes
a `03` and then meets a second `03` with too small a counter.

The submitted argument adds the finite, decidable predicate *Ready* ("the whole
`<B1` scan of the current stack succeeds") to the checkpoint invariant, and
proves that every return regenerates it, via a reverse-debt interpreter
(Section 3), a dual-credit comparison lemma (Section 4) and the exact word of a
direct return (Section 5).

`RequestProject/BB25/Prefix/LA.lean` formalises the part of that argument that
does not need the new comparison lemma, and isolates the rest as one explicit
hypothesis:

* `Ready` is the scan predicate, as an inductive definition on the stack;
* `scan_1LA`: from a ready, good checkpoint the sweep is safe — every pop it
  meets has its two decrements — and it ends either at the left end in state
  `<B1`, which is the known spinout, or at a one bit, i.e. at the
  member-independent `01` branch, with at least two `22` blocks in front of it;
* `readyCP_seed`: the blank-tape seed checkpoint `L ZZZXXX <B1 22 1$` is ready
  (its scan strips three `11` blocks and stops at the first `01`);
* `not_halts_1LA_of_zready`: granting `ZReady`, `1LA` never halts from the
  blank tape.

`ZReady` is exactly the open statement: *the `01` branch of the sweep returns
to a checkpoint that is ready again*.  It is a hypothesis of the theorem, not
an axiom, and nothing in the project claims that `1LA` has been decided.  What
its proof needs, beyond what the project has, is the exact stack produced by
the `01` branch — the present return lemmas produce a checkpoint whose
goodness, positivity and final block are known, but not its identity as the
paid stack `T(P(c) d 22^r 21 11^(r-1) chi(m) 21)` of an explicit word — and
then the reverse-debt induction of the document on that word.  This is the
natural next step for `1LA`.

## 23. `1LA` is settled: the readiness of every return

Section 22 left `1LA` conditional on one statement, `ZReady`: that the
member-independent `01` branch of the `<B1` sweep returns to a checkpoint whose
own scan succeeds.  That statement is now proved
(`RequestProject/BB25/Prefix/LA/Final.lean`, `zready`), so

```
  not_halts_1LA : ¬ Halts (M b4_1LA) init
```

is unconditional and sorry-free, with the standard axioms only.  `1LA` is the
eleventh member of the thirteen to be verified; only `0RB` and `0LB` remain.

The development is four files under `RequestProject/BB25/Prefix/LA/`.

**`Debt.lean` — the reverse-debt interpreter (Section 3 of the submission).**
`dpow n s` is the stack after `n` decrements and `TW w = tfold [L] w` the paid
reset stack of a word.  Reading a word from the right, with a debt `n` of
decrements already charged:

```
  … Y :  n even  → the scan stops at a one bit;   n odd → debt (n-1)/2
  … V :  n odd   → the scan stops at a one bit;   n even → debt n/2
  … X :  a pop: the two decrements of the 1LA rule make the debt 2n+4,
         and the counter below must satisfy 2n+4 ≤ cval (TW u)
```

These are exact, and the three stack identities behind them —
`dpow n (W :: s) = W :: dpow (2n) s`, `dpow (2k) (X :: s) = X :: dpow k s`,
`dpow (2k+1) (X :: s) = Z :: dpow (k+1) s` — hold with no side condition, so
legality has to be checked at the pops only.

**`Debt.lean` — the dual-credit lemma (Section 4).**  `ready_dpow_of_cval`: for
a good `c`, the scan of `D^n(T(P(c)))` is safe once `2n + 2 ≤ cval c`.  The
submitted proof peels a maximal run of decoded `X`s and computes
`n_j = 2^j(n+4) - 4`, `b_j ≥ 2^j(b+2) - 2`.  The Lean proof instead carries the
disjunction

```
  Credit c n :  2n + 2 ≤ cval c   ∨   (n even ∧ n + 4 ≤ 2 cval c ∧ n + 2 ≤ bval c)
```

through a plain induction on the stack.  The second alternative is exactly the
state of the scan *inside* such a run: it is inductive on its own (a pop
doubles the debt, but doubles `cval` and more than doubles `bval + 2` too), the
first alternative feeds into it, and a one bit stops the scan whenever the debt
is even — which it always is after one pop.  No maximal-run bookkeeping is
needed.

**`Chi.lean` — the digits of the drain (Section 5) and the crossing bound
(Section 6).**  `chi m` lists the low binary digits of `m`, least significant
first, a zero digit as the pop `X` and a one digit as the pop `V`.
`ready_chi`: crossing `chi m` backwards from debt `0` is legal, and the debt
`n` it hands to the left of `chi m` always satisfies

```
  n + 4 ≤ 4m ,     and    n + 9 ≤ 2m  when n is odd,
```

the two inequalities (C) and (D) of the document.  `chi_two_pow`,
`chi (2^k m) = X^k chi m`, identifies the `X^(q-1)` buffer of the document as
the head of the drain digits, so the buffer needs no separate treatment in the
machine argument.

**`Exact.lean` — the checkpoint the machine really reaches.**  The return
theorem of `Drain.lean` only records *that* a safe checkpoint is reached; for
`1LA` its identity is needed.  `exact_zero`, `exact_drain` and `exact_tail`
redo the drain keeping the word: from `σ` with a pending `2>` and a run of `r`
blocks `22`, the checkpoint is the paid stack of

```
  P(σ) Y^r V chi(2^(r-1) (cval σ + 1)) V
```

— the word (A) of Section 5, with `m = cval σ + 1`.  These hold for every
member of the family.

**`Direct.lean` and `Final.lean` — the assembly.**  `ready_drain_word` shows
that word is ready for every good `σ` and every `r ≥ 2`: the last `V` costs
nothing, `chi` is crossed by `ready_chi`, the buffer doubles `n+4` once per
pop, the `V` in front of it halves the debt, and the run `Y^r` then stops the
scan unless `r = 2` and the debt is `1 (mod 4)`; in that one case the debt
reaching `P(σ)` is `(n-1)/4`, and `n + 9 ≤ 2m` gives exactly the
`2·(n-1)/4 + 2 ≤ cval σ` that the dual-credit lemma wants.  `Final.lean` then
splits the `01` branch as in Section 7: a counter of at least two drains as
above; an exhausted counter overflows early, and either the reset is clean — in
which case the checkpoint literally begins `X Z …` and is ready for free — or
it is the exceptional one, which spends a further overflow and lands in a drain
with a run of at least three `22` blocks, ready again by the same lemma.  The
empty-stack sub-case is the established left-end spinout.

Two simplifications relative to the submitted proof are worth recording.  The
document's parity split on the residual digit `d` (Section 6, the `a` even and
`a` odd cases at the end) disappears: applying the dual-credit lemma to the
stack `W D²(c)` *after* the pop, rather than to `c` with the extra letter `d`,
makes both cases the single inequality above.  And the buffer `X^(r-1)` is not
constructed separately, since `chi (2^(r-1) m)` already begins with it.  No
error was found in the submitted argument.

## 24. `0RB`: the sweep, the odd branch, and what the even branch needs

The twelfth member is `1RB2LA0RB1LB---_1LA3RA1RA4LB0RB`.  Its `A> 241` rule is

```
  A> 241  ⟶  <B1 0 22        (three base steps, leaving a marker)
```

so, like `1LA`, the `141` block does **not** end the `<B1` sweep; unlike `1LA`,
the pop deposits a *marker* and the head then runs a whole local counter phase
above it before coming back.  The word it leaves in front of the head grows at
every pop, and the return is governed by the reset of that word.

### 24.1 What is machine-checked

Everything in `RequestProject/BB25/Prefix/RB/`, plus the new
`RequestProject/BB25/Prefix/Strict.lean`.

* **Strict admissibility** (`Strict.lean`).  A stack is *strictly admissible*
  when every bottom prefix that contains a bit has strictly more bits than
  pops.  `Strict.tfold` shows a clean paid reset above a strictly admissible
  stack is again strictly admissible — a reset pop needs a counter of at least
  two and so at least two unmatched bits below it — and `strict_TW` specialises
  that to a reset from the left end.  This is the extra invariant `0RB` needs
  and `1LA` does not: the submitted document exhibits the good, positive,
  `X`-ending and ready stack `ZWZZXWX`, on which `0RB` runs into the undefined
  transition `A4`.  `Strict` is now a field of the checkpoint class `ReadyCP`
  used by the whole development, and `LA/Exact.lean` was strengthened to record
  that the checkpoint a drain reaches is strict.

* **The counter phase above a marker** (`RB/Count.lean`).  `cfold_props` runs
  the local counter over a foreign bottom, and `marker_return_word` and
  `rb_pop_episode` give the exact marker theorem of the submitted document:
  an excursion above the marker in front of `w R` returns with `Y w X^h V R`,
  where `h` is the Dyck height of `w`, two decrements lower.

* **The generated right words** (`RB/Gen.lean`).  `Gen w h` is the language of
  right words: it starts at `w0 r` after the first pop, a stripped zero bit
  prepends `Y`, and a further pop applies `w ↦ Y w X^h V`.

* **The sweep** (`RB/Sweep.lean`).  `first_episode`, `sweep_odd` and
  `sweep_even` reduce non-halting of `0RB` from a `0RB` checkpoint to the two
  `01` branches of the sweep, `ZOdd` and `ZEven`.

* **The odd branch is closed** (`RB/Final.lean`, `zodd`).  Before the first pop
  the right word is still a run of `22` blocks over the terminal `1$`, so the
  branch is the member-independent one already proved for the whole family
  (`zready`); the checkpoint it reaches is a paid reset from the left end and
  is therefore strict for free.  Hence

  ```
    not_halts_0RB_of : ZEven → ¬ Halts (M b4_0RB) init
  ```

  `0RB` now rests on the single remaining obligation `ZEven`.

* **The reverse scan of a reset word over an arbitrary base** (`RB/Debt.lean`).
  `Scan w n a Q` runs the two-decrement scan over `w` from the right, starting
  from the debt `n` over a base of counter `a`; it holds as soon as the scan
  stops inside `w`, and otherwise hands the exit debt to `Q`.  `ready_scan`
  turns it into readiness of the paid stack `tfold σ w`.  This is the `0RB`
  analogue of the `1LA` reverse-debt interpreter, which only reads resets built
  from the empty stack.

* **The credit estimate and the leading-run criterion** (`RB/Credit.lean`).  In
  the coordinate `C = value + 2` a pop halves the credit and a bit never
  decreases it, so a word with `j` pops keeps at least `C₀ / 2^j`
  (`rrun_credit`); read backwards the debt obeys `n + 4 ≤ 4·2^K` after `K`
  pops.  Together (`scan_tail`) every pop of a tail is supplied as soon as the
  part in front of it has credit `2^(J+2)`.  Crossing `L` one bits costs the
  scan a debt of at least `2^L − 1` (`scan_Yrun`), so

  ```
    scan_leading_run : w = Y^L s, Digs s, nxw s + 2 ≤ L, 0 ≤ a
                       ⟹ the scan of w from debt 0 stops inside w
  ```

  and `rrun_pos_leading_run` gives `2 ≤ rrun w a` for the same words.

### 24.2 A reformulation of the scan that simplifies the analysis

Write `v` for the forward reset value at a position of the word and `n` for the
debt the backward scan carries there, and put `H = v − n`.  Then the whole scan
is

```
  at a bit (Y or V):  stop if H is odd, otherwise H ↦ H/2;
  at a pop (X):       the supply condition is exactly H ≥ 1,
                      and H ↦ 2H − 2 + (v mod 2).
```

In particular the scan stops at the first bit where `H` is odd, and the number
of bits it crosses in a row is the 2-adic valuation of `H`.  This is a
convenient way to see both the leading-run criterion (crossing `L` bits needs
`2^L | H`) and the supply conditions (they are one inequality, `H ≥ 1`), and it
was checked against the block simulator for all generated words up to five
marker steps.

### 24.3 What `ZEven` still needs

`ZEven` is Section 8 of the submitted document: with `a` the counter under the
`01`, four cases — `a ≥ 2` clean, the exception `w = YXYYV` with an exhausted
reset, `a ≤ 1` clean, and `a = 0` dirty.  Its ingredients are Lemma A (every
generated word is a safe local reset), Lemma B (a dyadic-slack estimate), Lemma
C (the early-clean reset clock) and the small clock of Section 7.  None of
these is formalised yet.

For **Lemma A** the route is now completely mapped out.  Write `lead w` for the
length of the leading run of one bits and `nxw w` for the number of pops.  The
leading-run criterion applies exactly when `nxw w + 2 ≤ lead w`.  Setting
`D = lead w − nxw w − h − 2`, `D` is unchanged by a stripped zero bit and
increases by one at every marker step, and its value on the base words is
`−3, −2, −1, r−5` for `r = 2, 3, 4, r ≥ 5`.  The criterion is `D + h ≥ 0`, so
the words it misses are exactly those with `D + h ≤ −1`, and tracking `D`
through the two constructors shows these are the six explicit families

```
  F1  Y X Y Y V
  F2  Y Y X Y Y V
  F3  Y^(k+2) X Y Y V X^(k+1) V
  F4  Y^(k+3) X Y Y V X^(k+1) V
  F5  Y^(k+3) V Y Y V X^(k+2) V
  F6  Y^(j+k+3) X Y Y V X^(k+1) V X^j V
```

(the classification was checked against the generator for all words with at
most five marker steps and `r ≤ 7`).  On each of them the scan stops after a
short explicit computation: it crosses the trailing pops and zero bits, arrives
at the `Y` of the `Y Y V` of `w0` with an even debt, and stops there.  So Lemma
A is the leading-run criterion, the classification of the six families, and six
finite computations; the supply conditions in the families are again the credit
estimate.  Positivity of the reset value fails in exactly one place, the
unextended `w0 2 = Y X Y Y V` over an exhausted counter, which is precisely the
exception of case 8.2.

## 25. `0RB` is settled: the even branch, and non-halting from the blank tape

This section supersedes §24.3: the four ingredients listed there (Lemma A,
Lemma B, Lemma C and the small clock of Section 7) are now all machine-checked,
`ZEven` is proved, and therefore so is

```
  not_halts_0RB : ¬ Halts (M b4_0RB) init
```

in `RequestProject/BB25/Prefix/RB/Final.lean`.  It uses only `propext`,
`Classical.choice` and `Quot.sound`, and nothing in `RequestProject/` contains
a `sorry`.  With `0RB` closed, twelve of the thirteen members of the family are
proved non-halting in this development; only `0LB` remains open.

### 25.1 Lemma A: every generated word is a safe local reset

`RB/LemmaA.lean` and `RB/Families.lean`.  The route is the one mapped out in
§24.3 and it went through unchanged.

* `scan_of_criterion`: if the leading run of one bits of a word of digits is at
  least `nxw w + 2`, the reverse scan started at debt `0` stops inside the
  word.  This is `scan_leading_run` of `RB/Credit.lean` applied after splitting
  `w = Y^(lead w) ++ w.drop (lead w)`.
* `gen_lead_or_exc` (in `RB/Classify.lean`): every generated word either satisfies
  the criterion or belongs to one of the six explicit families `F1`–`F6` of
  §24.3.  The proof is the induction on `Gen` with the deficit
  `D = lead w − nxw w − h − 2` as the invariant.
* `scan_fam12`, `scan_fam34`, `scan_fam5`, `scan_fam6` (in `RB/Families.lean`):
  the six finite computations.  They are all assembled from `scan_Xrun` (a run
  of pops multiplies `n + 4` by a power of two), `rrun_YcX` / `rrun_YcV` (the
  value of a run of one bits followed by a pop or a zero bit) and
  `scan_stop_YV` (the scan stops at the `Y` of a `Y V` when the debt it arrives
  with is divisible by four).
* `gen_scan_stops` is the disjunction of the two cases, and `gen_rrun_pos`
  gives positivity of the reset value of a generated word over a non-negative
  base.

### 25.2 Lemma B: the dyadic slack of a clean reset (`Prefix/Slack.lean`)

Lemma B says that an early clean reset cannot leave a stack whose counter is
one less than a power of two *and* whose decoded value is exactly the counter:
there is always at least one unit of slack.  The word-level statement is

```
  trun_gt_of_pow : Digs w → DyckPre w → bal w = h → 1 ≤ h →
                   1 ≤ e → rrun w 0 = 2 ^ e → rrun w 0 + 2 ≤ trun w 0 0
```

— for a clean Dyck prefix of positive height whose value is a power of two, the
transduced value exceeds the value by at least two.  The proof is a general
expanding-close estimate:

* `qgain q c = 4 ^ q * (c + 1) − qloss q`, with `qgain (q+1) c = 4 qgain q c − 1`
  and `3 qloss q = 4 ^ q − 1`, is the value a close of the counter gains after
  `q` further closes;
* `trun_ge_qgain` bounds the transduced value from below by
  `2 ^ h * qgain q c` for *every* `q ≤ qcnt w a` (this generalises the three
  ad-hoc bounds `trun_ge_pow`, `trun_ge_pow_q1`, `trun_ge_pow_q2` of
  `Prefix/Expand.lean`), and `rrun_le_two_pow` bounds the value from above by
  `2 ^ (h + 2 qcnt w a) (a + 1)`;
* a value that is a power of two forces, through the `Shape` trichotomy, either
  no expanding close (value `2 ^ h − 1`, which is odd, contradicting `e ≥ 1`)
  or a shape in which the two bounds above are incompatible with equality.

`slack_early` in `RB/Clock.lean` is Lemma B at stack level: for a strictly
admissible stack with a non-negative value and a clean last digit `d ∈ {X, V}`,
the stack `TW (pdec σ ++ [d])` the reset builds satisfies
`cval + 1 = 2 ^ k → cval + 1 ≤ bval`.

### 25.3 Lemma C and the small clock (`RB/Clock.lean`)

`ready_chi_ref` is a refinement of `ready_chi`: the counter in front of the
drain digits is only required to satisfy `4 m ≤ cval + 4` — an early reset
cannot promise more — and, in exchange, the continuation is told that either
`m` is a power of two (all digits are zero) or the outgoing debt satisfies
`n + 12 ≤ 4 m`.  Lemma C is then

```
  lemmaC : Good t →
           (∀ k, cval t + 1 = 2 ^ k → cval t + 1 ≤ bval t) →   -- the slack
           Gen w h →
           1 ≤ rrun (wordCD t w h) 0 ∧ Ready (TW (wordCD t w h))
```

— the word `wordCD t w h = pdec t ++ Y ++ w ++ X^(h+1) ++ chi (cval t + 1) ++ V`
that the early clean reset rebuilds is positive and ready.  The power-of-two
branch of `ready_chi_ref` is exactly where the slack hypothesis is consumed;
the other branch is the debt gap of §25.4.  `lemma_seven` is the same statement
for the degenerate word `[Y, V]` of the exceptional case, and needs only
`1 ≤ cval t`.

### 25.4 The debt gap of a generated word (`RB/Gap.lean`)

The missing quantitative ingredient is that a scan entering a generated word
*from the right with a debt* — not from debt `0`, as in Lemma A — either stops
inside or comes out with a debt divided by sixteen:

```
  gen_scan_gap : Gen w h → (n : ℤ) + 4 ≤ 4 a − 1 →
                 (∀ m, 16 (m + 1) ≤ n + 4 → Q m) →
                 Scan (w ++ X ^ h) n a Q
```

The two base words `w0 2` and `w0 3` always stop (`rrun_w0_two`,
`rrun_w0_three`); for `w0 (k+4)` and for the two constructors the gap comes
from `scan_Yrun_gap` and `scan_Vrun_gap`, which say that crossing `j` of a run
of `L` bits already costs a factor `2 ^ j` of the debt.  The value estimates the
argument needs above the drain buffer are `gen_rrun_lb`
(`2 ^ (h+1) · 2 a ≤ rrun w a + 2`), `gen_rrun_buf` and `gen_rrun_buf'`.

### 25.5 The even branch (`RB/Even.lean`, `zeven`)

`zeven` is Section 8 of the submitted document, with the four cases in the
order: `cval c = 0` (dirty overflow, `ret0_overflow_gen`); the counter reaches
zero after one decrement (the same, with the extra fact that the decoded word
is non-empty); and otherwise, after the two decrements the pop needs, either
the exceptional word `w = w0 2` over an exhausted counter (`ret0_exc`, which
runs the small clock of §25.3) or an ordinary clean reset
(`ret0_gen_reset`, which runs Lemma C with the slack of §25.2).

## 26. `0LB` is settled: all thirteen members are proved non-halting

`BB25.Prefix.not_halts_0LB : ¬ Halts (M b4_0LB) init`
(`RequestProject/BB25/Prefix/LB0/Final.lean`) proves that
`1RB2LA0RB1LB---_1LA3RA1RA4LB0LB` never halts from the blank tape.  It uses
no `sorry` and only the axioms `propext`, `Classical.choice`, `Quot.sound`.
With it, all thirteen members of the family are formally proved non-halting
in this development.

### 26.1 Which submitted material was used

* The **new** package (`bb25_0LB_nonhalting_proof.zip`, `PROOF_0LB.md`) gives a
  *single-return closed invariant* at the Z checkpoints
  `L c Z <B1 22^r 1`.  This is the argument that was formalized.
* The **old** `0LB` material (`PROGRESS_0LB.md` in
  `bb25_0RB_nonhalting_and_0LB_supply.zip`) reduced `0LB` to an unproved
  "the `ZZZ`-rooted class is restored after one or two returns" statement.
  The new argument does not need that statement, and it was not used.  The
  only idea of the old file that survives is the four-decrement *energy*
  `E(sW) = ⌊E(s)/2⌋ - 2`, and even that is only needed here in its word form
  (see 26.2).
* From the old `1LA` package the formalization reuses the existing Lean
  interfaces it produced: the paid reset stack `TW`, iterated decrements
  `dpow`, the drain digits `chi`, and `exact_tail` (the exact checkpoint of a
  pending-`2>` tail and its drain).  From the `0RB` package it reuses
  `trun_ge_qgain` (the general expanding-close bound).

### 26.2 How the formal proof is organized

The Lean proof follows `PROOF_0LB.md` closely, with one simplification: the
stack energy `E` of Section 2 (and its matched-forest decomposition,
Lemma 2.1) is never needed.  Every core that occurs is presented as
`c = D^k (T w)` for an explicit reset word `w`, and all the supply arguments
are carried out on words with the energy evaluator
`estep : Y ↦ 2e+1, V ↦ 2e, X ↦ ⌊e/2⌋ - 3` (the `ρ₃` of the document):

* `LB0/Energy.lean`: `erun`, `etrun`, the transduced word `qw`, the height
  `ht`; `erun ≤ rrun`, with a margin of `2` after a pop
  (`erun_add_two_le_rrun`, replacing `K(c) ≥ 2` of Lemma 2.1);
  `etrun_ge_egain` (**Lemma 3.1**); `pdec (T w) = qw w 0` and the other facts
  of a partly paid-off reset stack (`dpow_TW_facts`).
* `LB0/Clock.lean`: `chi` consists of pops and has at most `h-2` letters,
  the buffer energy `ρ₃(Y^r V X^(r-1), e) = 4e - 2` for `r ≥ 4`, the
  `6(2^t - 1)` energy threshold of a pop word, and the two density bounds of
  **Corollary 3.2** (`density_bounds`).
* `LB0/Scan.lean`: the machine-level sweep.  `brun_pop_0LB` is the
  four-decrement pop `W <B1 → D⁴ <B1 22` (through `N1`, `N2`); the
  reverse-debt table of **Section 6** is `scan_V_even`, `scan_Y_odd`,
  `scan_Y_even`, `scan_V_odd`, `scan_X`, with the energy `n ≤ erun u 0`
  carried along; `scan_pops` sweeps a whole word of pops (stop, with at least
  two letters crossed after entering without debt — Case A — or crossing with
  `n + 6` at most doubled per letter — Case B), and `scan_Xrun` is the exact
  buffer computation.
* `LB0/Return.lean`: the invariant `ZInv w k r` and the main return theorem
  `zinv_return` (**Sections 4–8**, both stopping cases).
* `LB0/Final.lean`: the blank tape reaches `L ZXZZX Z <B1 22^7 1` at step
  `931` (`entry_run`), whose core is `D⁹(T(Y⁵))` and satisfies `ZInv`
  (`zinv_entry`, **Section 9**), and `not_halts_0LB`.

One harmless deviation from the document: the invariant carries the counter
density bound in the form `23·2^h ≤ 24(b+1)` with the *actual* height `h`
instead of the decoded height `H ≥ h`.  This is weaker as a hypothesis, it
is all that the Case B counter estimate (31)–(32) uses, and it is
re-established at the next checkpoint from the stronger bound `(33)`.

### 26.3 The `4RB/0LB` sibling

The second new package (`bb25_4RB_0LB_nonhalting_transfer.zip`) concerns
`1RB2LA0RB1LB---_1LA3RA1RA4RB0LB`, which is **not** a member of the family
(its `B3` is `4RB`, so it is not of the form `M b4`).  Its local candidate
file now compiles as `RequestProject/BB25/Sibling/Local.lean` (the new marker
rules `03 <B1 → 043 A>`, `043 <A → <A 101`, the ordinary rules for the new
table, the composition of one pop episode, the spinouts and the 156-step
seed).  The transfer of the `0RB` return theorem to that machine is not
formalized: every block-level execution lemma of the project is stated for
the block simulator of `M b4`, whose `W <B1` rule is false for the sibling,
so the transfer needs the common execution lemmas to be re-derived for a
machine with an unspecified `B3`.

## 27. The `4RB/0LB` sibling is settled

`BB25.Sibling.not_halts_sibling : ¬ Halts BB25.Sibling.machine init`
(`RequestProject/BB25/Sibling/Final.lean`) proves that
`1RB2LA0RB1LB---_1LA3RA1RA4RB0LB` never halts from the blank tape.  No
`sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only.  This
supersedes the "not formalized" remark of §26.3.  The proof follows the
transfer argument of `bb25_4RB_0LB_nonhalting_transfer.zip` (`PROOF.md`); no
error was found in it.  The `0RB` checkpoint class `CP0`, the seed and the
word language `Gen` are reused unchanged.

**How the transfer is done without re-deriving the block lemmas**
(`Sibling/Transfer.lean`).  Every member-independent block lemma of the project
is stated for an arbitrary `b4`, so it can be used at `b4 = none`.  For
`bstep none`:

* every rule except the pop rule `W <B1 → <A F` is a valid run of the sibling
  (`bstep_none_sound_sib`): the `G` rule is undefined at `none`, and no other
  rule reads `B3` or `B4`;
* the number of `F`/`G` blocks on the right never decreases, and the pop rule
  adds one (`bstep_none_fgc`).

So a `bstep none` run whose two ends carry no `F`/`G` block never pops and is a
run of the sibling (`BRun.sib`).  It stays one with arbitrary cells added below
the left tape, as long as the bottom block `^11` is never read
(`BRun.sib_frame`); this is what lets the local computation above the new
marker `043` be taken from the `0RB` lemmas, run over the empty bottom.

**The `01` branches** (`Sibling/Ret.lean`).  The proofs of `zready` and `zeven`
(and their sub-lemmas in `LA/Final.lean`, `RB/Phase.lean`, `RB/Early.lean`,
`RB/Even.lean`) are re-run literally at `b4 = none`, with a return predicate
`SRet` that records the block run to the checkpoint *or to the left-end
spinout* instead of `¬ Halts (M b4)` (which would not transfer).  The results
are `zreadyS` and `zevenS`.

**The pop** (`Sibling/Pop.lean`).  `sib_pop` composes `03 <B1 → 043 A>` (2
steps), the local computation over the marker, `043 <A → <A 101` (3 steps),
the first decrement, `A> 101 → <A 201`, the second decrement and
`A> 201 → <B1 22` (9 steps).  `sib_pop_word` (later pops, via
`marker_return_word`) and `sib_first_pop` (the first pop, via the local part of
`first_episode`) give exactly the configurations of `rb_pop_episode` and
`first_episode` of `0RB`.

**The sweep and the conclusion** (`Sibling/Final.lean`): `sweep_odd_sib`,
`sweep_even_sib`, `cp0_returns_sib` (each return takes at least six steps),
the two spinouts for the sibling, and the halting-time descent from the
`156`-step seed.


## 28. Consolidation

All fourteen machines (the thirteen members and the `4RB/0LB` sibling) are
restated in `RequestProject/BB25/Check.lean` for the machine given by its
bbchallenge string, each depending only on `propext`, `Classical.choice`,
`Quot.sound`.  Everything not on the dependency path of those theorems was then
removed, by a declaration-level dependency analysis: the exploratory files
(`Deep`, `FTrace`, `FValue`, `Invariant`, `Pairing`, `Simulation`, `Trace`,
`Twins`, `Phase`, `Stride`, `Family`, `Halting`, `Rules`), unused declarations
inside the remaining files, and the Python exploration scripts in `tools/`.
The `01`-branch returns of `1LA`/`0RB` and of the sibling, which had been
duplicated, are now proved once for every `b4` (`zreadyS`, `zevenS`, with the
return predicate `SRet` recording the spinout run explicitly); `zready` and
`zeven` are derived from them.  The shared execution layer is one file,
`Runs.lean`.  Size: 21 600 lines in 71 files before, 15 200 lines in
55 files after (including the new `Check.lean`); the long kernel computations of the simulation
certificates are gone, the only remaining ones being the `156`- and
`931`-step runs from the blank tape.
