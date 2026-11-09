# Plan: fgh runtime machines, 2 symbols, blank tape

Target: one runtime machine per level of the fast-growing hierarchy

    ε₁, ζ₀, ζ₁, η₀, η₁

each **2 symbols**, each **under 67 states**, each **starting from a blank tape**,
each **formally verified in Rocq** -- then each compacted into 3, 4, 5, ..., 9
symbol versions, then published to the bbchallenge Discord.

This file is the plan of record.  It records what is built, what the binding
constraints actually are, and where the numbers come from, so that nothing below
gets asserted without a measurement behind it.

## Status

| level | states (2 sym) | tape level | value level (Rocq) |
|---|---|---|---|
| ε₀ | 31 minimal (32 reachable) | simulated, no proof | proved (earlier work) |
| ε₁ | **57**, 100 rows | rung branch proved (`rocq/Eps1Tape.v`); copy sweep proved (`rocq/Eps1Copy.v`); block-spent decision proved and composed into the copy (`Eps1Tape.v`); eps₀ round interior still simulated | `rocq/Eps1Ladder.v` + `Eps1Tape.v` + `Eps1Copy.v`, 156 closed theorems total |
| ζ₀, ζ₁, η₀, η₁ | not started | — | — |

ε₁ is `tools/eps1_machine.py`: eps₀'s rounds with the stage count read off the
value, `lvl 0 v = v`, `lvl (S k) v = run (lvl k v) v`.  Checked: a = 0 halts with
v in 7 steps; (1,1) → 3 in 105; (1,2) → 255 in 68 384.  a ≥ 2 is beyond
simulation, not merely slow (`lvl 2 1 = 65535` already forces a round over 65 535
marks, ~4·10⁹ steps).

## Constraint 1: bbchallenge counts blank-tape starts

This is not a detail of presentation, it changes the machine:

1. **The frame has to be written by the machine.**  The current machine starts on
   a written tape (`1^{a+1}` budget, wall, `1^v` value, seed, head on the wall).
   On a blank tape there is no mark to the left of anything, so every
   "walk left until a mark" pattern in the construction -- the budget walk, the
   block's left end, the copy's leftward scans -- is undefined until the machine
   writes the scaffold itself.
2. **A blank tape carries no input.**  `f_α(n)` needs n present.  On an all-blank
   tape the run is a single fixed number, so either n is hard-wired into the
   table (the machine computes one value) or another machine generates it.  For
   bbchallenge it is hard-wired, and the `f_α(n)` phrasing becomes "this machine
   computes `f_α(n₀)`" for the specific n₀ in its table.
3. **The budget's halt test leans on a written tape.**  The construction dropped
   its sentinel because the budget run's own last mark is the "no rungs left"
   signal.  That holds once the budget exists; the prologue must create it.

## Constraint 2: the state budget

Measured by partition refinement (Mealy minimisation: merge states whose rows
agree in written symbol, direction and *class* of the target), not by eye:

* ε₁ as assembled: 61 states used, **60 reachable**, **57 after exact merges**.
  The four merge pairs were `R0/AA`, `R6/K1` (redundancy inherited from eps₀'s
  table) and `S4/ZE`, `B2/BL` (from the splice).  Applied in
  `tools/eps1_machine.py`; the run lengths are unchanged (105 and 68 384 steps),
  which is the evidence that the merge preserved behaviour exactly.
* ε₀: 32 reachable, 31 minimal.  So ε₀'s own table is the floor here, and the
  ladder adds 26 states.

Blank-tape arithmetic for ε₁:

    57  ladder (minimised)
     6  the generator machine below (its halt routed into the ladder)
    ~2  reposition / carve the frame's gaps out of the generated run
    --
    65  under 67, with two states of slack

The `~2` is an estimate, not a measurement: carving `1^{a+1}[gap][block]1(wall)
[gap]1^v[gap]1` out of one contiguous run is the part that can exceed it.

**For ζ₀ and above, < 67 is not established and must not be claimed.**  The
ladder as built re-reads the count field as a *value*; ζ₀ needs it re-read as an
ordinal notation, with the notation's fundamental sequence driven by the tape.
That is a new mechanism per level, not a re-use, and its state cost is unknown.
The honest statement at this point: ε₁ fits under 67 with room to spare; ζ₀, ζ₁,
η₀, η₁ are unbuilt and unbudgeted.

## Constraint 3: material for a blank tape -- the 6-state generator

A 6-state machine that starts blank and halts with a single ungapped run of
`10 ↑↑ 15` ones -- the maximum-consecutive-ones champion for 6 states.  Blank is
0, halt is a state with no rows:

    A _ 1 R B      A 1 _ L D
    B _ 1 R C      B 1 _ R F
    C _ 1 L C      C 1 1 L A
    D _ _ L E      D 1 1 R halt
    E _ 1 L F      E 1 _ R B
    F _ _ R C      F 1 _ R E

(uppercase R/L -- `tools/tm.py` reads anything other than `R` as a left move, so
lowercase directions silently go the wrong way; that cost one debugging pass)

Its role: it supplies the enormous run of ones that becomes the ladder's value
and budget material, from a blank tape, in six states.  The head finishes beside
the run, so reaching its first mark costs about one transition ("move left a
little"), and the frame's gaps have to be carved out of the run afterwards.

**Caveat that must travel with it:** its halting tape is `10 ↑↑ 15` steps away.
No simulation can reach it and no amount of running distinguishes it from a
machine that never halts -- the early tape is sparse and holey, which says
nothing about the halting tape.  So the final-run claim is only usable once it is
*proved* symbolically, and the composite's behaviour on that run is likewise
beyond simulation.  Any claim resting on this machine is a Rocq obligation, not a
simulation result.

## Constraint 4: compaction into 3..9 symbols

Once the 2-symbol versions exist, each is re-expressed over k = 3..9 symbols.
The point is not translation but re-encoding: with more symbols the frame's roles
stop needing their positions to carry meaning.

* the wall and the seed are permanent marks distinguished from data only by
  *where* they sit; with 3+ symbols they become their own symbols, so the
  searches for them collapse;
* the budget needs no sentinel and no positional test at 2 symbols; with an
  extra symbol the "one rung left" cell can simply be written differently;
* the copy's two destinations (block mark, value mark) are distinguished at 2
  symbols only by geography; extra symbols distinguish them by value.

Expected effect: states fall as k rises, but each k-symbol machine is a distinct
table that has to be re-verified -- never obtained by truncating the previous
one.  The 2-symbol case is the binding constraint; if 2 works, k > 2 is
compaction, not new mathematics.

## Verification requirements (Rocq)

Per level, per symbol count.  The rules already in force in this repo apply:

* symbolic/parametric proofs only -- `vm_compute` runs and simulations are not
  proofs;
* `./verify.sh` is the gate: it greps for `admit | Admitted | Axiom | Parameter`
  and counts closed theorems (currently 156, all closed).  Never write those
  tokens in a `.v` file, not even in a comment;
* what is verified at a level is the *value* semantics (`stage`, `run`, `lvl`
  and their monotonicity/separation lemmas, as in `rocq/Eps1Ladder.v`) plus, once
  it exists, the tape-level invariant;
* **the tape-level invariant exists for ε₁'s rung branch, not yet for its copy.**
  `rocq/Eps1Tape.v` proves, for every gap m, budget length and value length v,
  that `ENTRY` reaches the copy's entry in 2m + 7 steps with one budget mark
  spent, the block region blank and flush, and the value region untouched
  (`rung_reaches_copy`), and that with one mark left it halts with the value
  intact (`rung_halts`, `rung_halt_conf`, `rung_halts_run`).  What is not proved
  is the copy's own sweep over the value.  For the blank-tape machines it gets
  harder again: the prologue's output must be characterised before the ladder's
  invariants can even be stated.

Nothing in the repo currently depends on a simulation, and that must stay true.

## Constraint 5: where the levels actually are (`championsreal.txt`)

loader3229's file (712 lines) records the level per (states, symbols) for the
bbchallenge finds.  Selected rows, 2 symbols:

| states | level | row |
|---|---|---|
| 8 | (f_w)^3(12) | BB(8) |
| 10 | f_{w+1}(2{36}3) | BB(10) |
| 11 | f_{w+1}(f_w(f_w(5))) | BB(11) |
| 12 | f_{w+2}(f_{w+1}(f_{w+1}(3))) | BB(12) |
| 13, 14 | (f_{w+2})^6((f_{w+1})^2(3)), ^9 | BB(13)/(14): "12-state w+2 machine with the halt step redirected into a parity-check gadget" |
| 18 | f_{w+3}(114) | BB(18) = the BB(16) machine with two states (Q,R) spliced in |
| 20 | f_{w+6}(f_{w+6}(4)) | BB(20) |
| 21 | > (f_w^2)^2(4^^341) | BB(21) |
| 40 | f_(w^w)(75500) | BB(40), table inline |
| 51 | **f_(e0+1)(8)** | BB(51), table inline, "start from state 30" |
| 67 | q^81(q(5)-2) (laver) | BB(67) |

Across symbols, for eps_0: 36 states / 3 symbols (BB(36,3), f_e0(7)), 19 / 5
(BB(19,5), f_e0(1.7e352)), 18 / 7 (BB(18,7)).  Above that,
`BB(56,7): (f_e0)^F(k0)` -- "the (18,7) f_e0 engine applied F TIMES, F = the
round-0 extent read off the tape (the fuel is measured, not a constant)", glue
kernel-checked in Lean (`LadderGlue.lean`, native_decide) -- and psi_0(OMEGA_2)
at BB(46,7)/BB(61,6).

### What it changes

1. **The lift recipe is explicit and cheap: redirect the halt.**  Costs in the
   file: +1 state buys the whole w+1 level over w (BB(3,5) f_w(2{15}5) ->
   BB(4,5) f_{w+1}(27041), the same base machine); +2 spliced states buy a level
   (BB(16) -> BB(18) f_{w+3}); a halt-redirect gadget buys an iterate count
   instead (BB(12) -> BB(13)/(14)).  At a fixed base, each extra *symbol* adds
   one f_w rung with the argument unchanged (BB(3,5) -> BB(3,6) -> BB(3,7) ->
   BB(3,9) = (f_w)^1..6(15)).
2. **The 2-symbol base for eps_1 under 67 is BB(51)**: f_(e0+1)(8) in 51 states
   leaves 16 for the glue, which is tighter than our own 26-state rung+copy --
   so at that base the glue must be a halt redirect, not a copy.  BB(40) (w^w)
   leaves 27, which is exactly the size of our current glue.
3. **The eps_0-engine + F-times glue already exists, in 7 symbols.**  BB(56,7)
   is that construction at 56 states / 7 symbols.  Our 57-state / 2-symbol
   machine is the same construction with the alphabet paid for in states
   instead.  That is the honest answer to "61 seems high": against BB(10)'s
   f_{w+1} in 10 states it is high (but BB(10) is optimised for halt time from
   blank tape, not for a value being computable); against the 7-symbol version
   of the *same* construction it is at par, and two symbols cheaper.

### The risk that must travel with it

Every level in that file is the reporter's own estimate -- the file says so
repeatedly ("predicted, not formal", "claimed analysis by Claude never
verified"), and none of it has a Rocq proof.  Building on BB(51) turns the
base's level into a *proof obligation*, not a citation: proving an opaque
51-state machine's halt ordinal in Rocq is plausibly harder than proving our own
construction, which is designed to be provable.  So: use the champions for state
efficiency and as the target, keep our ladder as the provable path, and never let
a champion's estimate enter a theorem.  The one row that matters here is the
BB(8,5) note -- f_{w*2}(32) in 8 states / 5 symbols, where loader3229's own
comment is "You can prove this in Coq now."

### Added 2026-11-01 12:03: the BB(11,4) w*2 variants

Two more rows, both 11 states / 4 symbols, both w*2, both "(informal)":

    machine 1  f_{w*2}(2{11}6)   "potential ... probably can reach"
    machine 2  f_{w*2}(98)

Both are the 07:06 BB(11,4) row with the grid untouched (eleven states A..K,
alphabet {0,1,2,3}, a single halt entry `1RZ` in state A).  Every difference is
in the lift states: B, D, E, H, J of the 07:06 row, and in each case a
*defined* entry replaces an undefined one.  Blank entries fall from 8 in the
07:06 row to 5 and 3.  No state is added.

1. **The level is bought by defining transitions, not by adding states.**  That
   is the trade step 8 (3..9 symbols) runs on: the same mechanism needs fewer
   states at larger k because more of the frame can live in written symbols.
   These two rows are the file's cleanest demonstration, since they hold the
   state count at 11 and the alphabet at 4 and move only the ambiguity.
2. **In four symbols w*2 costs 11 states, and that number did not move.**  The
   07:06 row already reached w*2 in 11 states / 4 symbols; what these two change
   is the argument, not the state count.  The 4-symbol ladder's own top is
   BB(9,4) f_{w+3}(16), so the step from w+3 to w*2 costs 2 states here -- while
   the 5-symbol row reaches f_{w*2}(32) in 8, three fewer.  That is the exchange
   rate our compaction has to beat, not a narrative.
3. **Do not rank rows by argument.**  Machine 1's 2{11}6 is an arrow tower,
   machine 2's is 98, BBi(28)'s is 17, the 8-state 5-symbol row's is 32.  Only
   the level is comparable across rows; arguments are not, and both of these
   are estimates anyway.
4. **A cheaper formal target than eps_1.**  If we want a level proof on record
   before the eps_1 one, the candidates in order of tractability are BB(8,5)
   f_{w*2}(32) (8 states, his own "You can prove this in Coq now") and then
   these two: 11 states, 4 symbols, 3 blank entries, one halt.  Proving either
   would be a real result; neither is needed for eps_1 and neither enters it.

What this repository checked: the strings parse as eleven rows of four
3-character entries, deterministic, one halt, targets inside A..K, and neither
halts in 50 000 steps from a blank tape.  Nothing about the levels.

## Order of work

1. [x] ε₁ ladder machine, 2 symbols, simulated for a = 0, 1 (57 states)
2. [x] exact state merges applied and measured (61 → 57)
3a. [x] ε₁ tape-level invariant, rung branch: for every gap m, budget length and
       value length v, `ENTRY` reaches the copy's entry in 2m + 7 steps with one
       budget mark spent, the block region blank and flush, and the value region
       untouched; with one mark left it halts with the value intact.  Proved in
       `rocq/Eps1Tape.v` (16 theorems, all closed), its table generated from
       `tools/eps1_machine.py`, and the statements cross-checked against the
       simulator by `tools/check_eps1_tape.py`
3b. [x] ε₁ tape-level invariant, copy sweep: the copy rebuilds 1^v in the block
       from the value while the value survives, for every v -- the rest of step 3
       and the gate on everything after it
       done: `sweep` in `rocq/Eps1Copy.v`.  From the first trip's frame -- head on
       the source's first mark, w marks behind it, gap D, budget k -- it returns
       `trip_frame (j + S w) D k` with the head on the blank after the source's
       last mark: the block and the copy both 1^(j + S w) (j marks already there,
       S w more copied), the budget pushed S w cells further left, and everything
       beyond the source -- the value's tail, `skipn (j + S w) A` -- untouched.
       So the copy is "the block grows by exactly the source it eats, and the
       value it eats is preserved": no mark invented, none lost.
       It is an induction on w.  One round is `trip_step`, a trip at *any* frame
       index j <= N, which is `trip` for j = S m and `trip0` for j = 0; `trip` is
       4m + 2D + 2(S n) + 21 steps from `trip_frame (S m)` to `trip_frame (S (S m))`,
       chained from `trip_out` (2m + D + 11) and the return half `trip_back`
       (2(S n) + 2m + D + 12) = the eight runs P2, P3, P4, P5, BQ, BW, R1, R2;
       `trip0` is the first trip, from an empty block and empty copy, 2D + 2(S n)
       + 17 steps, where the phase chain genuinely degenerates (P5 lands on a
       blank instead of a prefix mark, R2 walks no marks, the block's single mark
       is written by B2's own blank row), so it needed its own statement and got
       one.  The count is a Fixpoint over the frame index, `sweep_steps`, with the
       closed form v * (4j + 2(S d) + 2(S n) + 15) + 2vv: v trips from frame j
       cost v*(4j + 2D + 2k + 15) + 2v^2, the 2v^2 being the 2j of each trip
       growing as j does.
       Checked against the running machine, not only in Rocq: `python tools/check_eps1_copy.py` builds each statement's start frame as a
       tape, runs the machine on `tools/eps1_machine.py` (whose rows
       `rocq/Eps1Copy.v` embeds, emitted by `tools/emit_eps1_copy.py`) for the
       statement's own step count, and compares the whole result frame -- 994
       frames, all matching, 898 of them the phases and the two trip statements,
       96 of them the composed sweep: up to four trips from frames j = 0, 1, 2,
       with the count taken from `sweep_steps` itself.  Raising that count by one
       makes all 96 fail, so the composed cases test the count and not just the
       frame.  `./verify.sh` closes all 156 theorems with no axioms and no
       parameters.
       open: this is the copy in the frame the rung hands over -- step 4's
       prologue builds that frame, and step 3's ladder side (`a` count of halves,
       the eps_0 stage branch) is not proved here either; so what is proved is
       "the copy copies for every v", not yet "the machine runs the ladder".
       Nothing in the repo claims the latter.
3c. [x] ε₁ tape-level invariant, the stage branch's decision: when the block is
       spent the machine hands over to `ENTRY` and spends a rung.  `S1` erases a
       block mark and `S2` asks whether another is left; on a blank both hand
       over, on a mark `S2` goes back into the round.  `block_spent_reaches_copy`
       (and its `_S1` twin) in `rocq/Eps1Tape.v` compose that handover with the
       rung branch: from `S2` (or `S1`) on a blank with the block region `zeros (S M)`,
       2M + 10 steps later the machine is in `WALK`, the copy's entry, in exactly
       the frame `rung_reaches_copy` produces -- the gap one cell wider, because
       the blank the decision stopped on joins the gap on the way out.  The rows
       are one-step facts (the decision is local); the composition is the
       theorem.  Checked: `block_spent` in `tools/check_eps1_tape.py`, 16 cases
       from both states over M, a, b, v, all matching the running machine.
3d. [ ] ε₁ tape-level invariant, the eps₀ stage branch's *interior*: the rounds
       themselves.  Nothing is proved past one round at a value of one mark
       (`round_v0` in `rocq/Eps0Drive.v`, for every gap m).  The statement the
       rounds owe, measured by cutting an eps₀ trace at `R1`-to-`R1` (the frame
       conversion below is what `round_v0` proves at v = 1; the cost formula is
       what `tools/round_cost.py` checks against 40 measured rounds, 0
       mismatches):

           run (2*m + 7*v + 14 + k_pre v 0 0)
             (mkConf R1 (on :: L) on
                     (on :: zeros m ++ ones v ++ bl :: on :: [])) =
           Some (mkConf R1 L on
                     (on :: zeros (m + v + 2) ++ ones (2 * v + 1) ++ bl :: on :: []))

       one counter mark spent (the left context loses one mark), the value
       doubled plus one, the gap grown by v + 2, at module K's cost plus the
       walks.  No theorem in the repo states or owes this yet, and nothing above
       depends on it -- but the stage branch cannot be called proved until it is,
       because it is the branch's whole interior.  This is what "the eps₀ branch
       is still this simulation" means, precisely.

       An attempt at it exists and is written down in this file only because it
       failed in a way worth recording: the twelve-phase shadow of `round_v0`
       (same frames, `v` in place of the numeral) replays H1..H9 unchanged --
       the R1/R2 steps, `walk_R4_phase m A (S v)`, `walk_on_R5 v`,
       `k_block_drive_exit (S v) 0 0 m`, `walk_A5_phase (S v)`,
       `walk_A6_phase (S v)`, the two A7/A8 steps -- and then stops at the A8
       step, on nothing mathematical: `ones (2 * S v + 2)` and
       `ones (S (2 * S v + 1))` are the same list but not convertible, because
       Coq only computes `ones`/`zeros` on a constructor-headed index, and a
       run of marks split across a `tl` boundary changes its spine.  The same
       wall blocks the A9 phase (`ones (2 * S v + 1) ++ on :: ...` has to become
       `ones (2 * S v + 2) ++ ...`, which is `ones_succ`, which lands on `S (...)`,
       not on `+ 2`) and the AA walk, where the left gap has to become
       `zeros (S v + S m)` via `zeros a ++ zeros b = zeros (a + b)` -- that one
       is fine, the mark runs are the problem.  Two fixes are worth trying, in
       this order: (a) restate the frames with the doubled length as its own
       variable (`set (d := 2 * S v)`) and prove the phases as small lemmas at
       `d`, so no `2 * S v + k` index ever faces a `tl`; or (b) keep the frames
       and write every run in the canonical spine `on :: ones k` / `bl :: zeros k`
       from the start, with `S (2 * S v + k)`-shaped indices throughout.  Neither
       is a proof; this note is here so the next attempt starts from H10 instead
       of from H1.
       Option (a) was then tried: a variable for the doubled length, and every
       seam stepped through a lemma ([tl_ones_succ], [merge_marks], [zeros_add]
       with [zeros_succ]) instead of through [cbn].  H1..H9 stand, the A9 phase
       and the AA walk are now small lemmas that compile on their own, and the
       attempt again stops at H10 -- with the mismatch now named exactly: the
       step leaves [on :: ones (2 * S v)] where the frame says
       [ones (2 * S v + 1)].  Same list and same count, different spine: since
       [2 * S v] is [S (v + S v)], which of the two [cbn] unfolds depends on
       which side of the equation the term sits on.  So the last barrier is not
       mathematical either: write every run in the frames in the unfolded spine
       ([on :: ones k], never [ones (S k)]), or normalise both sides with one
       lemma [ones a ++ ones b ++ Z = ones (a + b) ++ Z] before comparing.
4. [x] blank-tape prologue: the frame is written by the machine itself, and the
       machine now starts from nothing -- state 0, empty tape, head at 0
       (`tools/eps1_blank.py`).  The prologue writes the frame right to left from
       cell 0 (seed, the blank, the value, the value gap, the wall, the block
       region, the budget) so the wall is not written until near the end, then
       one return pass skips the budget marks and the block region and spends
       ENTRY's own first step off the wall.  Measured from a blank tape:
       (a=0, v=1) halts with 1 in 13 steps, (a=1, v=1) with 3 in 101,
       (a=1, v=2) with 255 in 68 375 -- values equal to `lvl`, checked for five
       instances.  Geometry is tight: the block gap must be at least 1 (0 never
       halts) and the value gap exactly 2 (1 never halts).  State cost is the
       open item: 67 states for the (0, 1) instance -- exactly bbchallenge's
       limit -- 68 for (1, 1) and 69 for (1, 2), so a rung-bearing instance is
       1-2 states over.  Nothing here is a proof.
       target ≤ 65 states, and state the halting-run claim as a proof obligation
6. [ ] decide the base for each level: own ladder (provable by construction,
       57 states for the eps_0-engine-iterated design) vs a champion base such
       as BB(51)'s f_(e0+1) (51 states, 16 left for a halt-redirect glue) --
       and state which claim each choice hands to the proof
7. [ ] ζ₀, ζ₁, η₀, η₁: the notation descent, one mechanism per level; budget
       states honestly rather than assuming 67 is reachable
8. [ ] k-symbol versions, k = 3..9, each re-verified, compared by level and
       never by argument, against the file's benchmarks: 4-symbol w*2 in 11
       states (2026-11-01 12:03), 5-symbol w*2 in 8 states, w*2+1 in 8 states
       (BBi(36))
9. [ ] publish to bbchallenge Discord: 5-tuple tables, blank-tape starts, and
       every halting claim proved rather than simulated

Step 3b gates everything after it: a machine whose tape behaviour is only
simulated is not something to publish to bbchallenge, and a 10↑↑15-step run can
never be simulated at all.

## The eps_1 tower machine: design of record (2026-11-02)

### Why nesting cannot get there

The ladder machines (`eps0_machine.py`, `eps1_machine.py`) put the loop structure
in the **states**: one stage loop inside one rung loop inside one loader.  That is
a fixed tower height, i.e. a fixed ordinal below eps_0, and no counter size
changes it -- `stage(x) = 2^(x+1)-1`, so `lvl k v` is `f_3` iterated k times,
whatever the budget.  Measured, not assumed: the ladder reproduces `lvl(1,1)=3`,
`lvl(1,2)=255`, and its level is `f_3`.

eps_0 and above need the tower **on the tape**: the depth must be data, so the
machine's four local moves walk a tower of any depth.  This is also what the
BB(150) machine in `limbms.txt` does -- its matrix is the ordinal notation, and
its "requires at least 3 BMS rows" is the same statement that a fixed number of
rows below the notation's own depth cannot represent the descent.

### The tape and the moves

    [1^c0] 0 0 [1^c1] 0 0 [1^c2] ... 0 0 [1^ch]

folded from the bottom is `w^(w^(...^(c0)...)*c1)*c2 ...`, so with depth h
unbounded the sup of these towers is **eps_0**, not eps_1: eps_0 = sup_h of the
h-level towers over 1.  eps_1 is one epsilon number up:
`eps_1 = sup(eps_0+1, w^(eps_0+1), w^(w^(eps_0+1)), ...)`, the same climbing
restarted on a base of eps_0+1.  With n the index (read off the
bottom run):

| move | when | rewrite | ordinal rule |
|---|---|---|---|
| A | top coefficient > 1 | decrement it | predecessor |
| B | top 1, exponent a successor | decrement the exponent, top := n+1 | `w^(b+1)[n] = w^b*(n+1)` |
| C | top 1, exponent a limit | step the exponent instead | `w^b[n] = w^(b[n])` |
| D | depth 0 | decrement the bottom coefficient | predecessor |

### What is checked

`tools/tower_rules.py` compares all four moves against the ordinal model in
`tools/eps1_descent.py` (CNF below eps_1, eps_0 as an atom with
`eps_0[n] = w-tower over 1`, standard fundamental sequences): **477 chain/index
cases up to depth 3, every move equal to `fs` or `pred` exactly**.  Since each
move strictly decreases the ordinal, halting follows from well-foundedness, and
the depth being data is what makes the level **eps_0** rather than a fixed `f_k`.
Getting to eps_1 from here needs one more thing: eps_0 must be available as a
*value* -- an atom in the notation whose fundamental sequence is an unbounded
tower, unfolded at runtime -- so that `w^(eps_0+1)` can be written and stepped.

Descent lengths (n bumped at each move, the convention a tape machine has):

| chain | ordinal | moves |
|---|---|---|
| `[1]` | 1 | 1 |
| `[2,1]` | w^w | 10 |
| `[3,1]` | w^(w*3) | 29 |
| `[1,1,1]` | w^w^w | 23 |
| `[1,2]` | w^w*2 | 5 |
| `[1,1,2]` | w^w^w*2 | 63 |
| `[2,1,1]` | w^(w^(w*2)) | > 200 000 |
| `[1,1,1,1]` | w^w^w^w | > 200 000 |

`H_{w^(eps_0+1)}(n) = H_{w^eps_0}^{n+1}(n)`: one wrap above eps_0 iterates an
eps_0-level function n+1 times.  That is the structure the tower machine has and
the ladder machines do not.

### State budget

| piece | states |
|---|---|
| cursor + the four moves' decisions | ~12 |
| move B: copy the bottom run to the top (reuses `eps1_copy`'s sweep) | 16 |
| eps_0 drive at the bottom (move D hands over) | 33 |
| glue / handover | ~5 |
| total | ~66, before exact merges |

Open: the bottom of the tower has to *be* an eps_0-level descent, and the drive in
this repo measures `f_3`, so either the drive is replaced by the tower machinery
itself (depth-1 chains, which `tower_rules` already validates) or the two are
spliced.  Next: build the tower machine with the bottom as a stub, verify the
descent against the table above by simulation, then splice the bottom.

### The 150-state machine is the super-eps_1 machine, and it is now exercised

`limbms.txt` is the BB(150) champion in the repo, `f_lim(BMS)`: 151 rows over 150
counted states (state 0 is uncounted), blank tape, its own 6-state loader.  Its
level is lim(BMS), which is far above eps_1 -- this is the "super eps_1" machine,
and the only one in the repo that is actually above eps_1.

`tools/limbms.py` now runs it as an acceptance test (`python tools/limbms.py`,
`ALL OK`):

| run | result |
|---|---|
| documented RFPMS example `11_11__111_...`, from A1 | halts in 59 640 steps, 23 cycles; cycle 0 decodes to `S(2,2,3,3,3,3,3,3,3,3)` = their `(0,0,0)(1,1,1)(2)` |
| backend from d0 with S(2,2): doubling -> e1..e6 -> S1..S13 -> T1..T3 -> A1 core | **halts in 30 841 steps, 144 of 151 states used**; the 7 untouched are exactly `0, A..F` (the loader) |
| production input `1 0 1^n 0 (0 1^n)^m` | n=2: m=5 -> 2 176 steps, m=6 -> 198 785, m=7 -> 200 028, all halt with 119 core states; m=8 does not halt in 2e6 (growing) |
| same shape, n=3 | m=5 -> 9 162, m=7 -> 9 444, halt; m=8/10/11 grow past 2e6 |

Two things this settles.  First, the module accounting is measured, not read off
the comments: setup is 32 states (loader 6 + doubling 9 + S 13 + T 3 + state 0),
core is 119, and the core needs its whole generality even on the easy production
inputs -- restricting the input to towers does *not* shrink it, so there is no
cheap 119 -> 60 reduction by input restriction.

Second, why a small hand-built eps_1 machine keeps failing: a unary run cannot
grow in place between its neighbours (move B must set the top coefficient to
n+1, which overruns the gap and would require shifting the suffix on two
symbols), and that is exactly the obstruction `limbms.txt` answers by flattening
the matrix into one row and encoding nesting in the *distances* between entries.
So the small machine needs the distance encoding, not the run-per-level tape that
`tools/tower_rules.py` validates.

### The eps_1 machine, 2026-11-02: the step is now a tape step

The obstruction recorded above was "a unary run cannot grow in place".  It is
gone, and it did not need the flat/pointer encoding: it needed two changes to the
*representation*, both of which follow from the rules rather than adding to them.

**1. The park.**  Write a chain top-first as run lengths T = [t0..tk] and resolve
`tower_rules.step`'s C recursion by hand.  The decision is local in the first two
runs (a chain is a successor iff its top coefficient is >= 2), and C only walks
down to the first run of size >= 2, where B fires.  So the position that grows is
`j-1`, just under the leading block of 1s.  That block is what cannot sit at the
free end, so store it as a *count*: state = (park m, working part W), chain =
`[1]*m ++ W`, and

    m == 0            A:  W[0] -= 1
    m >= 1, W != []   B:  park m-1, W := [n+1, W[0]-1] ++ W[1:]
    m >= 1, W == []   W := [n+1], park m-2      (m == 1: the chain is 1, so 0)

`tools/tower_free.py` checks this against the four moves: 360 chains up to depth
4 at n = 1,2,3, all matching.  Every growth is now at W[0], and measured over
those runs the park and the chain's depth never exceed the starting depth, which
is what lets a fixed layout budget for them.

**2. Where the tape can grow.**  Frame, left to right:

    [free] 1^m (park) 0 0 1^n (index) 0 0 1^{W_bottom} 0 ... 0 1^{W_top} [free]

W bottom-first, so its top run is rightmost and grows into free space; the park
is a count run whose only growth is a write into the free space on its left.  The
copy that implements B's `n+1` drains the index from its left end and writes each
mark back one cell left (`eps1_copy`'s one-sweep trick, mirrored), so the index
shifts left one cell per copy; move B spends one park level from the park's
*right* end, so the park's right end also moves left one cell per move.  Equal
rates: the park-to-index separator is the same width after every move and only
the index-to-W separator grows, which costs nothing.

The writer is built and tested: 25 states, `python tools/eps1_tower.py` gives 19
frames, all PASS -- a new top run of exactly n+1 marks, one blank from the old
top, the index still n marks one cell left, the park untouched, including frames
with a park in front.  Cost is 30 steps at (W=[1], n=1) and 722 at (W=[6,6,6],
n=9): quadratic in n per copy, which does not move the level.

Still to splice on: the park's two operations (spend one from its right end, grow
one into the free space on its left), the A move (remove W's top run's rightmost
mark), the dispatch that reads the park and picks A or B, the normalisation that
folds W's top run into the park when it reaches 1, and the build phase (seed 1^n
-> park of n levels and an index of n marks, by draining the seed into both
regions one mark each per trip).

### The tower machine works on tape, 2026-11-02

`tools/eps1_full.py` is the descent as a 2-symbol table: the park and the working
part of the design three sections up, actually running.  What made it possible
was dropping the index: n is a *constant* of the machine, so move B writes n+1
marks with a fixed chain of states, and with the index go the copy, the drift and
the park-to-index gap arithmetic.

Frame, left to right, W bottom-first so its top run is rightmost:

    [free]  1^m (park)  0 0  1^{W_0} 0 1^{W_1} 0 ... 0 1^{W_k}  [free]

Three things had to be right, and each was wrong first:

  * **B's order.**  `tower_free` gives W' = [n+1, W[0]-1] ++ W[1:].  Decrementing
    the run *below* the new top leaves two blanks where its last mark was, and
    two blanks is the separator, so the frame dies.  Decrementing while that run
    is still the top the cell it frees is at the free end and costs nothing:
    spend a park level, take one mark off the top, write n+1.
  * **Which end of the park moves.**  Spending erases the park's *leftmost* mark
    and folding writes at its *leftmost minus one*, so its right end is a fixed
    landmark: "is there a park" is a three-cell look, and a fold that creates one
    writes three cells left of W's leftmost mark.
  * **Eager normalisation.**  `tower_free` re-splits at every step, and the split
    is what turns a leading 1 into a park level; on tape that level is a physical
    mark.  So after every A the machine folds while W's top run is one mark, and a
    fold that leaves such a run continues in the same move.

## Checks

`python tools/eps1_full.py` runs three:

  * 16 frames `(park, W)` move by move against `tower_free.step`, decoding the
    tape after each move: the machine must reach the same (park, W) *and* halt
    exactly when the model does.  All pass, from 1 to 247 moves.
  * blank tape with a park of h levels, for h = 1..7: the number of moves must
    equal `tower_free.descent`'s.  1, 4, 11, 26, 57, 120, 247 all match.
  * the blank tape run itself halts with the tape cleared.

The base is a real parameter -- n = 1, 2, 3 all work -- and the run grows as
2^h moves: steps 85, 310, 911, 2388, 5861, 13810, 31675, 71296, 158273, 347646,
757175 for h = 2..12, ratio settling at about 2.1 per level (2^h moves, each move
a walk).

Size: 71 states and 112 rows at (n=2, h=3), where the build costs one state per
park level; Moore refinement (`eps1_minimise.rebuild`) gives 68 states / 108 rows
and preserves the run exactly, checked against all of the above.

## What this is and is not

Given a park of h levels it performs that tower's descent, 2^h moves, and
halts.  Read against the ordinals: it realises `eps_0[h]` -- the fundamental
sequence of eps_0 at height h, two per level: the descent of a height-h tower is
2^h.  So the machine computes eps_0's fundamental sequences, but only for the
heights the build can write, and the build is fixed at one state per level.  That
bounds the level: a fixed machine realises finitely many eps_0[n]'s, which is a
fixed f_k, not eps_0 and certainly not eps_1.

The two missing rungs, in order:

  * **eps_0** needs h to come off the tape instead of out of the state table -- a
    counter-driven park builder, so the same table realises eps_0[n] for every n
    it is given.  That is the first real level claim, and it is one loop away.
  * **eps_1** needs more than deeper towers, because deeper towers only climb to
    eps_0.  eps_1 = sup(eps_0+1, w^(eps_0+1), w^(w^(eps_0+1)), ...): the base of
    the outermost tower has to be eps_0+1, so eps_0 must be carried as a value
    whose fundamental sequence is itself an unbounded tower, unfolded at runtime.
    On tape that means the data structure stops being a flat list of runs and
    becomes a tree whose nodes are towers -- the hydra-shaped part -- and the
    descent recurses instead of walking.

What is here is the piece both rungs call: a descent that runs, matches the model
move for move, halts when the model halts, and can be invoked from a phase above
it.

## Rules of record for the eps_1 machine (2026-11-02, from the user)

These override anything earlier in this file that conflicts.  They are the
acceptance criteria; a machine that misses one is not the machine.

1. **Two symbols.**  Alphabet `{0, 1}`, blank `0`.  Nothing else, no marking
   states, no auxiliary alphabet.
2. **At most 67 states**, and as few as the design allows.  State count is to be
   minimised as far as possible below that ceiling, not merely brought under it.
3. **eps_0 machines already exist.**  A machine that only reaches eps_0 is not a
   contribution, so the descent must contain a step eps_0 machines do not have:
   a step that builds a tower whose *height is read from the tape*.
4. **The step count must be f_{eps_1}(n)** for some n > 2.
5. **Blank tape start.**  No input, no prologue loaded from outside: the machine
   starts on all blanks and writes its own ordinal notation.
6. **The sequence.**  eps_1 = sup(eps_0+1, w^(eps_0+1), w^(w^(eps_0+1)), ...),
   i.e. the members are the towers of omegas over eps_0+1, and
   eps_1[n] = the tower of height n over eps_0+1.  Then
   f_{eps_1}(n) = f_{eps_1[n]}(n) by the definition of f at a limit, so the
   machine's obligation is: descend eps_1[n] to 0 for an n > 2.
7. **Exactness is not required.**  It is enough to prove it halts with a step
   count *around* f_{eps_1}(n) -- bounded factors from conventions and from the
   per-move walk are allowed, the level is what is being claimed.

### What "around f_{eps_1}(n)" has to mean, precisely

The machine's moves are ordinal decreases with the index bumped at every
successor step -- Hardy's H.  So the obligation splits in two, and only the
second is about ordinals:

  * **halting**: every move strictly decreases the ordinal, so the run reaches 0
    and the machine halts; this is a well-foundedness argument, not a simulation;
  * **length**: the number of moves from eps_1[n] is H_{eps_1[n]}(n), and the
    ladder of H values has to be compared with f on a computable ladder and then
    propagated by the recursion f_{eps_1}(n) = f_{eps_1[n]}(n).

Nothing in that needs the machine to be *run* to completion, which is just as
well: H_{eps_1[3]}(3) is not a number anyone can reach.

### The eps_1 machine: design of record and state budget (2026-11-02)

The ordinal the machine descends is a **chain with an atom at the bottom**:

    a = w^(w^(...^(b0)*b1)...)*bh        b0 in {number, eps_0, eps_0+1}, bi >= 1

This is closed under the descent from eps_1[n] -- starting from a single term, fs
and pred only ever give single terms, and the one sum that ever appears, eps_0+1,
is the atom with a +1 that pred removes -- and it is *not* closed under anything
wider, which is what keeps the tape flat.  In the flat engine's notation this is
`W` = a list of run lengths; the atom is the new entry that makes the level
eps_1, because eps_0's fundamental sequence is a tower of height n *read off the
tape* and the chain has to be extended by n entries at the moment it is reached.

Tape, one track, two symbols:

    [chain: b0 0 b1 0 ... 0 bh] 0 0 [index: 1^n]

bottom at the left, top at the right, coefficients unary, one blank between
entries, the atom as a zero-length bottom with a flag.  Every rule acts on the
smallest term, which is the top of the chain, and looks one entry down, so the
whole rule set is local:

| move | test (local) | tape action |
|---|---|---|
| M1 pred top | top entry >= 2 | erase one mark of the top entry; index += 1 |
| M2 walk down | top entry == 1 | step left over the entry (its length is one because the cell left of its rightmost mark is blank) |
| M3 fs | entry k >= 2, entries above are 1 | decrement entry k; entry k+1 := n+1 |
| M4 atom | bottom is the atom, all entries above are 1 | replace the atom by n unit entries: eps_0[n] = tower of height n |
| M5 eps_0+1 | bottom is the atom with the +1 flag | clear the flag (pred) |
| M6 halt | chain is a single entry equal to 1 | halt |

M2 is why the walk is free: in a unary bottom-first chain, "this entry is 1" is
the single cell to the left of the entry's rightmost mark, so no counting and no
depth comparison is needed anywhere in the walk.  The same is true of M1 and
M3: coefficients are unary and separated by one blank, so "decrement" is one
erase at the free end.

### State budget (ceiling 67)

| phase | states |
|---|---|
| build eps_1[3] on a blank tape: index, wall, atom flag, three unit entries | 7 |
| main loop: read the top entry, branch to M1/M2 | 4 |
| walk down the chain (M2), including the "entries above are 1" invariant | 5 |
| M1 and M3's decrement, then the walk back up to the level above | 5 |
| M3's write: copy the index into the level above (one-sweep copy, the
  `eps1_copy` gadget, drained and rebuilt in place) | 12 |
| M4: expand the atom into a tower of height n (same copy, writing `1 0` per
  index mark) | 10 |
| M5 and M6 | 3 |
| index increment and the walks that reach it | 4 |
| **total** | **50** |

50 leaves 17 in hand for the control mistakes a build of this kind always
uncovers, under the ceiling of 67.

### The one open point

M3 and M4 both need a copy of the index, and they need it at **opposite ends** of
the chain: M3 at the top, M4 at the bottom.  The one-sweep copy of `eps1_copy`
needs the source and destination adjacent, separated by a wall, because it writes
two marks for every mark it drains -- so one index cannot serve both ends.  Three
resolutions, in order of preference:

  * **(A) the index travels.**  Copy it to the end that needs it, erase the
    original, and back when needed.  Costs a factor of O(n) per move, which does
    not change the level (rule 7 allows bounded factors), and reuses the copy
    gadget unchanged; needs a wall at each end.
  * **(B) two indices, updated in step.**  Every increment writes to both; no
    duplication is ever needed but every walk is twice as long and the two
    copies must not drift.
  * **(C) the index is the top coefficient.**  Bump the index at every move
    rather than only at successor moves, then the fs write is free (the marks are
    already there).  Cheapest, but the atom then has to reach a value that lives
    at the far end, which is the same distance problem.

(A) is the one that cannot fail on correctness; (C) is the one that saves the
most states.  Nothing in the rule table above changes with the choice -- only the
gadget that supplies n to M3 and M4 -- so the machine can be built against (A)
and trimmed to (C) later.

### What is checked already, and what is not

`python tools/eps1_level.py` (new): records the sequence members
(eps_0+1, w^(eps_0+1), w^w^(eps_0+1), w^w^w^(eps_0+1), ...), checks that every
move `fs`/`pred` strictly decreases the ordinal on a 400-notation sample (the
atom included, 30 of the 125 limit moves being atom expansions) -- which is the
halting half of rule 7 -- and measures the two ladders.  It does **not**
establish the level separation: at n >= 2 both ladders pass the 2e6 cap at the
third rung, and at n = 1 both are capped by height 3 / member 0, so the run is
too violent to separate the ladders by measurement, and the f-versus-H table is
printed side by side rather than asserted, because those two hierarchies agree
only after their conventions are matched.

So: rules recorded, design fixed, budget 50 of 67, halting measured, level not
yet proved, **and the table itself is not built**.  The next step is (A): extend
`eps1_full.py`'s verified flat machine with the atom entry and the travelling
index, and test it against `eps1_descent` on small chains the way the flat engine
was tested against `tower_free`.

### The geometry, settled (2026-11-02)

The open point above is now closed by making the copy *shift its own source*.
`eps1_copy`'s one-sweep copy drains a run from one end, writes a mark into the
block behind the wall, and rebuilds the drained mark in the value region -- so the
value survives with one cell of drift.  Turn that drift into the layout:

    [free]  [chain: top ... atom]  gap  [index 1^n]  [free]

The chain's free end is at the left and the index's free end is at the right, both
walls of free space, so neither can ever collide with the other: every fs write
extends the chain leftwards, and the index drifts rightwards by the number of
marks it just rebuilt.  Every operation is then local:

  * decrement a coefficient: erase one mark at the end of the run (its free end);
  * fs-successor (top is 1, entry below >= 2): decrement the entry below, and let
    the copy write n marks into the top entry, which had exactly 1 -- n+1 total;
  * fs-limit: **not** a pop.  Measured against the model, `w^p(X)` never loses a
    wrap: fs(w^p(X)) = w^(p-1)(X) holds only when X is a limit, and when X is a
    successor the fs is w^(p-1)(w^(X-1)*(n+1)) -- the wrap is *spent on a
    coefficient*, not discarded.  The first version of this table had the pop and
    `tools/eps1_chain.py` refuted it in two moves;
  * atom with no wraps: p := n-1 by a copy between the index and the wrap
    counter, which sit across one wall from each other;
  * eps_0+1: clear the offset flag; halt when the chain is a single 1 and p = 0.

The key simplification this buys: the entries above the acting level are always
1, so they are a pure tower and are stored as a **wrap counter p**, not as tape
entries.  That removes the middle of the chain entirely -- the acting level is
always the chain's top -- and with it the middle-insertion that was the real
obstacle.  The budget above still holds (the pop is cheaper than the write it
replaces), and no move now needs a copy except the two the index is adjacent to.

What is left is table plumbing, not design: the drain-and-shift copy, the pop,
the wrap-counter copy, and the build.  Nothing about the level is in doubt any
more; what was in doubt was whether the geometry existed, and it does.

### The rule set, checked against the model (2026-11-02)

`tools/eps1_chain.py` is the moves of the design written at the level of the
representation, so they can be compared with `eps1_descent` exactly.  State:
`(p, chain)` with the invariant that the chain's top entry is the acting one, so
every unit entry above it lives in the wrap count `p` instead of on the tape.

| move | condition | rewrite |
|---|---|---|
| pred | p = 0, val(chain) a successor | chain := chain - 1; index += 1; then absorb a top 1 into p |
| fs-successor | p >= 1, val(chain) a successor | chain := (chain-1) ++ [n+1]; p -= 1 |
| fs-limit | val(chain) a limit | chain := chain[n]; p unchanged |
| fs-atom | chain = [eps_0] | chain := [1] ++ [1]*n  (eps_0[n] = tower of height n) |
| halt | p = 0, chain empty | -- |

Normalisation (erase a top 1, p += 1) is value-preserving: w(w^p(X)) = w^(p+1)(X).
It is also what keeps the tape local -- with it the acting entry is always the
chain's top, so every write is at the chain's end and no insertion ever happens
in the middle.

Checked, `python tools/eps1_chain.py`, ALL OK:

  * **every move against the model**, 400 random chains x 4 moves, decoding the
    ordinal after each move: the successor must equal the model's fs or pred, and
    the index must bump exactly on predecessor moves.  The first versions failed
    here in three distinct ways -- a "pred" that was really an fs, wraps that
    vanished instead of being spent, and a chain whose bottom was a bare integer
    -- which is why this check exists before any table is written.
  * **lengths**: from eps_1[n], the number of moves equals `hardy()` where both
    run (member 0, n=1: 21 = 21) and both exceed the cap afterwards, in step.
  * **the obligation traced**: eps_1[3] as a chain is p=3, chain=[eps_0+1], and
    the first six moves decode to w^w^w^(eps_0+1)*4, then *3 with a new
    coefficient, then two preds as the index climbs, then a wrap absorbed.

What this does and does not settle: the *semantics* of the machine are now fixed
and machine-checked, including the epsilon_0 expansion that makes the level
epsilon_1.  What is still missing is the 2-symbol transcription: the tape
geometry for the index (it must sit beside the chain's top for the n+1 writes,
and the wraps counter must sit beyond it without being pushed), the pop/absorb
walk, and the build.  No table is claimed.
## The 2-symbol transcription, stage 1: geometry and the index copy

`tools/eps1_table.py` is the table.  Two pieces of it are now written and
machine-checked; the moves that drive them are not yet attached.

### The tape, as built

    [free] 1^p (park)  0 0  1^{c0} 0 1^{c1} 0 ... 0 1^{cm}  0 0  1^n (index)  [free]
            Lp..Rp         C0                                X..

Entry code: run length 1 = eps_0, 2 = eps_0+1, L >= 3 = the number L-2.  The
single blank is the chain's separator, two or more blanks are free space, so the
chain's top run is "the last mark before two blanks" and the index is "the first
mark after two blanks".  Homes: `HT`, the head on the top run's last mark E.

Two invariants carry the geometry:

  * I1 -- the park's right end sits at C0-3 forever.  Spending erases the park's
    *leftmost* mark and growing writes one cell left of it, so the right end never
    moves and "p = 0" is a fixed look three cells left of C0.  Anchoring the other
    end would put the p = 0 test behind a walk of p cells, which is why the park
    is right-anchored and *spent from the left* even though that costs O(p);
  * I2 -- X = E+3 at rest, two blanks between the top run and the index.  pred
    erases E and writes one index mark at E+2, so both ends move left together
    and pred costs six moves whatever p and n are.  Only the fs writes move X
    right, and that is the copy.

### What the copy had to be, and what the first attempt got wrong

The fs-successor's new top run has n+3 marks and the index keeps n, while the
band between the chain and free space held n.  Two facts fixed the design:

  * the new run's own cells are almost exactly the old index's cells, so the run
    cannot be built by *moving* the index's marks: they are the run.  The copy
    therefore *erases the source and rewrites it two cells to the left* as the
    run, one trip per mark, which keeps the cursor local (the erased cell's right
    neighbour is the next source mark);
  * the index's copy goes into free space three blanks past the source's right
    end, so its write position is a fixed offset from a position the head can
    find, and the "three reserved blanks" are what make that offset checkable.

The first attempt preserved the source and tried to track a read cursor on an
unmarked block; that is not possible with two symbols, and it is why the plan's
earlier phrase "erase a top 1, p += 1" style shortcuts do not extend to the copy.
The second attempt was off by one in three places at once: the new run starts two
cells past the decremented run (separator plus the old gap), the run needs two
marks at the finish rather than three because the entry already wrote one, and
the return trip crosses three reserved blanks plus the old cursor's cell, not
three plus two.  Each was caught by decoding the tape at the home, not by reading
the rows.

### Checked

    the copy, in isolation, n = 1,2,3,4,5,8,13,21:  PASS
    the copy on 60 random shapes (p 0..3, chain depth 1..3, top entry 2..4,
      n 1..7):                                     OK
    states used by the copy:                       21

Cost, measured: 24 moves at n = 1, 41 at 2, 62 at 3, 87 at 4, 116 at 5, 227 at 8,
492 at 13, 1124 at 21 -- quadratic in the index, about 2.5 n^2, as predicted for a
unary copy with one head.  That factor matters for the halting time and is
recorded below rather than papered over.

### The state budget was too optimistic, and the reason is structural

The plan budgeted 12 states for the copy; it takes 21.  Worse, the dispatch needs
*p* at the moment it decides pred against fs-successor, and p lives at C0-3, a
walk of the whole chain away from the acting entry.  The flag has to be carried
back over that walk, which duplicates the walk-back and the entry-length count:
about 18-21 states.  Adding it up with pred, the fs-limit, the build and the halt
gives roughly 73 states raw against the 67 cap, so before the table can be called
a 67-state machine the dispatch needs a cheaper design (or Moore refinement has
to recover six states, as it did from 79 to 68 in the eps_0 engine).

### What the overhead does to the level claim

Every routine here costs a fixed polynomial in the current index: pred is 6
moves, the fs-successor is about 2.5 n^2 plus two walks over the chain, the
fs-limit's p += n is about n(P + chain) because the park's left end is reached
from the middle.  Summed over a descent the halting time is f_eps_1(n) up to a
fixed polynomial factor, not f_eps_1(n) exactly.  For these hierarchies that
keeps it inside level eps_1 (any fixed power of f_eps_1(n) lies below
f_eps_1(n+1)), but it is an overhead, and the machine's step count is not the
Hardy value.

### Not yet written

  * the dispatch (entry length 1/2/3/4+, is the run the bottom, is there a park);
  * pred, including the absorb case (a top run of value 1 is deleted and the
    wrap counter grows) and the halt;
  * the fs-successor's wiring around the copy, including the case where the chain
    is exactly [NUM(1)] and the new run starts at C0;
  * the fs-limit: [eps_0] -> [1] with p += n, which needs the same double write as
    the copy but with the park as the near destination and the index as the far
    one;
  * the blank-tape build of p = 3, chain = [eps_0+1], index = 3.

No halting-time claim is made for the table, and `rocq/` is untouched.
## Cheaper designs: what the wrap counter is actually for

The 21-state copy is not the problem; the dispatch was, because it had to walk to
the park to read p.  Two observations remove most of that cost.

### 1. p is only ever asked whether it is zero

Reading the model of record, `p` appears in exactly four ways:

    p == 0                the pred / fs-successor branch
    p - 1                 the fs-successor's spend
    p + 1                 a pred that absorbs a top run of value 1
    p + n                 the fs-limit's [eps_0] expansion, through normalise

Its *magnitude* is never compared with anything and never used in an arithmetic
comparison.  So the machine does not need p at the point of decision; it needs
one bit, and it needs the counter itself only because the count must survive
being spent one at a time.

That kills the argument that made the dispatch expensive.  The bit does not have
to be read afresh at every move: the machine can *track* it, because every place
that changes p is a place the machine already is.

    after an fs-successor's spend    at the park, where "is the park empty now"
                                     is the cell just right of the erased mark
    after a pred's absorb            the pred that erases a 4-mark run is
                                     recognisable by that run's length, so the
                                     machine knows p went 0 -> 1
    everything else                  p is unchanged, and the pred loop keeps it 0

So the bit is only read where p can fall to zero, which is once per fs-successor,
and it is carried back over the walk by two exit states -- not by duplicating the
whole entry-length count.  What that costs:

    the count for p == 0   4 states   (2 = shorten, 3 = halt, 4 = erase and p+1,
                                       >=5 = shorten)
    the count for p >= 1   2 states   (3 = the chain is exactly [1], else shorten)
    the spend              2 states   (erase the leftmost park mark, then test)
    the walk back          4 states   (two shared, two by the flag)
    the pred               3, the halt 1
    ------------------------------------------------------------------
                          16 states  against the 20-21 estimated before

### 2. The fs-limit can share the copy's loop instead of having its own

The fs-limit is the same shape as the copy: drain the index, write one mark into
a near destination and one into a far one, with the index's new position fixed by
three reserved blanks past its old right end.  Only the near destination differs
(the park's left end instead of the new top run).  Written as one routine with two
near-destination arms, it costs the second arm (3-4 states) plus the copy's loop
instead of a second 10-12 state routine.

### 3. The copy's own blank counting is where its 21 states go

Six of them are the entry's three-cell offset (CW0..CW3, CWB, CBA) and eight are
the two "count three blanks" walks (CX1..CX4, CY1..CY4).  Moore refinement
(`tools/eps1_minimise.py`, which took the eps_0 engine from 79 to 68) should merge
the counting walks with the marking walks; expect 21 -> 17 or so.  That is a
measured 14% cut on the earlier engine, so it is a reasonable expectation, not a
promise.

### 4. Why the bit cannot just sit next to the acting entry

The obvious cheaper design is to keep p's emptiness in a mark a couple of cells
from the acting entry, so the branch is a two-cell look.  It does not work, and
the reason is the same drift `tools/eps1_copy.py` documents: the index's left end
marches left by one cell on *every* pred, unboundedly, and the acting entry
marches with it.  Anything parked at a fixed offset from the acting entry is
therefore eventually reached and eaten by the index -- a marker 3 cells out is
gone after three preds.  For the bit to survive it would have to recede as the
index advances, which is another counter to maintain, and the net saving is gone.
A separate flag cell is therefore not available; the flag has to travel with a
walk, which is what item 1 makes cheap.

The other structural option -- fold the wraps into the chain as trailing unit
runs so there is no park at all, making "p == 0" the length of the chain's
rightmost run -- does make the branch local, but it reintroduces the middle
insertion: the new run [n+1] has to go *below* the remaining unit runs, so the
fs-successor would shift p-1 runs right by n+3 cells, a second conveyor of 6-8
states, on top of the copy.  It also throws away the copy that is already
verified, because the run's geometry changes.  Not worth it.

### The arithmetic

    copy (verified today, before refinement)      21
    dispatch under item 1                         16
    the fs-limit as a second arm of the copy       4
    the blank-tape build                           7
    the halt                                       1
    ------------------------------------------------
                                                  49

with the copy's refinement as margin.  That is the design to build: keep the
geometry and the verified copy, track the wrap bit instead of re-reading it, and
share the copy's loop with the fs-limit.  Nothing here is implemented yet beyond
the copy and the decoder.

## The ε₁ table as built (2 November 2026)

The design above was written, run, and checked against the chain spec.  It does
not meet the 67-state cap.  The numbers are recorded here so the next session
does not re-derive them.

### What the table is, and what it agrees with

`tools/eps1_table.py` implements the whole move set at the homes: the blank-tape
build, the dispatch, pred (shorten and halt), the index copy, the spend, the
absorb, a 3-run normalisation pass, a trailing-unit fold, the head-empty arm and
the fs-limit.

  * blank tape, state 0 -> (p = 3, chain = [ATOM1], n = 3) in 16 steps, home H1;
  * the index copy in isolation: n = 1,2,3,4,5,8,13,21 pass in 23, 40, 61, 86,
    115, 226, 491, 1123 steps (quadratic, about 2.5 n^2), plus 60 random shapes;
  * 414 starts x 4 moves ALL OK against `eps1_chain.step`, compared by ordinal
    value with `full` and by n exactly, each move run from the machine's own tape;
  * halting counts on 10 terminating starts: advancing homes + the halt equals
    `eps1_chain.run`'s move count.  Value-neutral intermediate homes (the absorb's
    3-run fold, the trailing-unit fold) are counted as extra; e.g.
    p = 0, chain = [w^0, 1, 2], n = 3 gives 131 advancing + 1 extra + halt =
    132 model moves.

### The state count

Raw: 150 states, 207 rows.  Moore refinement (`tools/eps1_minimise.py` through
`tools/_test_minimise.py`) merges five nontrivial classes (BW2/W31/QIH,
P4/W30, R3/SW/HSW, B/SR, QIP/QIW) to **143 states, 198 rows**, checked
behaviour-preserving on the blank-tape build and six frames.

Cost drivers, own states before shared-state double counting (the sum is 151
because one name is defined in two functions): the fs-limit 27 (its
index-preserving pass 2 is the expensive half), the absorb 25, the copy 20,
dispatch + pred 19, the build 14, the spend 14, the head-empty arm 12, the 3-run
normalisation 9, the unit fold 5, the erase 1, pred-shorten 5.

### The verdict on the 67-state cap

**Not met: 143 states is the measured floor of this architecture.**  The
arithmetic above (49) assumed a pred of 3 and counted the fs-limit as 4; in the
built table the fs-limit needed index-preserving staging the budget never
assigned, and the absorb's index move (n + 1 marks landed five cells left, over
an overlap) took 25.  Reaching 67 therefore needs a different architecture, not
more merging of this one.  Whether one exists in the style of
`EPS1_35_STATES.md` — whose 61-state stage/rung machine sits one level
*below* ε₁ — is open; what ε₁ additionally demands is the descent on an
ordinal notation, whose tape encoding is exactly what this table costs most.

### Status of record

Seven-module gate green (2 November 2026).  `./verify.sh` re-run the same day:
16 Rocq modules compile, 156 theorems closed under the global context, no
forbidden vernacular — but the development formalises the tower/chain rules and
the ε₀ machine, **not** this 150-state table.  The machine's ε₁ halting time
rests on the checked `eps1_chain` descent, not on a measured run; an
ε₁-sized halt is astronomically long and was not simulated.
