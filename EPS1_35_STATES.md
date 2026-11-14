# Can 35 states reach f_{ε₁}(71)?

Short answer: not with anything this repo can currently build or check.  This
note records the state budget honestly instead of producing a table nobody can
verify.

## What is actually built

| piece | states | status |
|---|---|---|
| module K (append-2 copy, source consumed) | 7 | simulated x = 1..6; three walks proved in `rocq/ModuleK.v` |
| drive (count rounds off the tape) | 26 | 33-state table, simulated; round and stage proved for every value/counter length (`Eps0Round.v`, `Eps0Stage.v`) |
| second feedback: value -> stage count | 28 | **built and simulated**: 20 for the copy (`tools/eps1_copy.py`), 8 for the rung branch; `tools/eps1_machine.py` runs `lvl` for a = 0, 1 |
| ε₁ descent on the ordinal notation | ? | not designed |

eps_0's drive with module K inside it is 33 states, and the second feedback is 28
more: 61 states, 106 rows, not 35 (57 states once the four
exact duplicates are merged).  That machine would still sit below ε₁.
The gap between a value-driven stage count and ε₁ is not a few more states: it
is a *descent on an ordinal notation*, where the count field is re-read as a
notation and the notation's fundamental sequence is itself the computation
(`tools/eps1.py` is that rule, checked, but nothing turns it into tape
operations).

## The second feedback, as built

eps_0's machine already lets the value decide its own stage's *round* count: the
fuel phase moves the value into the counter, and the round engine runs once per
counter mark.  The *stage* count is the one thing handed in, as a block of marks
on the left.  Handing it in no longer is the whole of the change, and it needs
one operation eps_0 never performs: a block of marks has to be laid down with the
value's length **while the value survives**, because the fuel phase then consumes
that same value into the counter.  Every block operation the machine already has
consumes its source -- module K appends two marks per source mark and eats the
source, the fuel phase empties the value's region -- so a preserving duplicate is
new.

Frame (head on the wall at the start):

    1^{a+1}(budget) 0^k [block] 1(wall) 0^k 1^v 0 1(seed)
      stage branch       -> rung branch      -> copy      -> into a round
      (eps_0's table)       (spend a budget)   (rebuild block)

which is `lvl 0 v = v`, `lvl (S k) v = run (lvl k v) v`.

### The copy is one sweep, not two

The design recorded here before this was built said two passes were needed.  That
was wrong, and the reason is worth keeping: the two destinations are in
*different regions* -- the block left of the wall, the value right of it -- so a
single trip can write two marks for every one it reads, and one sweep is enough.
What is true is that the drain has to be from the value's **left** end: then the
"does the source continue?" test is the cell immediately right of the cell just
erased, which is local, and local is all two symbols give.  Each trip:

    x = the source's leftmost mark
    1. erase x, step right
    2. go left two cells, write the value's mark at x-1 (x-1 was erased a trip
       earlier, so it is blank)
    3. continue left over the copy, the gap and the wall to the first blank left
       of the block, and write the block's mark there
    4. keep going left and carry the budget's rightmost mark to its left end
    5. come back right: over the budget, the gap, the block, the wall, the gap,
       the copy, one blank -- and look: mark means the source continues, blank
       means it is empty and the copy is done

`tools/eps1_copy.py` tests that sweep on the geometry a real run reaches.  It is
16 states, 2v^2 + 35v + 9 steps at budget 1, and it is checked for v = 1..20 and
255 with budgets 1..9: block = 1^v flush at wall-2, value = 1^v shifted one cell
left, seed untouched, budget pushed exactly v cells and never eaten, and the gap
between the block and the budget constant at 3 cells for every v.

Two dead ends, both measured rather than argued:

* the copy's first attempt assumed the head arrives one cell right of the wall.
  It arrives **on** the wall (`head == wall` at COPY in every case), so the first
  erase hit the wrong mark.  Rows written from the trace instead of from the
  sketch work;
* the budget cannot live right of the seed.  The rounds rewrite the value one
  cell right per round, so the seed drifts right by about v per stage -- a=1 n=2
  v=2 starts with the value at 8 and the seed at 11 and reaches COPY with the
  value at 275 and the seed at 531.  A budget parked past a 3-blank buffer breaks
  eps_0 outright: the run stops at A7 after 41 steps instead of 140.

So the budget lives left of the block and the copy pushes it one cell per block
mark, the rate the block grows, which keeps their gap fixed.  The budget is one
run of a+1 marks, spent one per rung: after spending, a mark to the left means
another rung, a blank means halt.  No sentinel is needed -- the run's own last
mark is the signal, and it is why the spend is testable at all.

### What is checked

`tools/eps1_machine.py` assembles the machine: eps_0's 33 rows with the two
halting rows redirected, the copy's states after them, the rung branch, and a
handover that puts the head back where a round starts: 61 states, 106 rows.
Partition refinement (merge states with identical write/direction/target-class
rows) finds four exact duplicates -- R0/AA and R6/K1 inherited from eps_0's own
table, S4/ZE and B2/BL from the splice -- so the table is merged to **57 states,
100 rows**, and the checked runs take exactly the same 105 and 68 384 steps, which
is what shows the merge was behaviour-preserving.  For the state budget against
bbchallenge's 67, see `FGH_MACHINES_PLAN.md`.

| input | result | steps |
|---|---|---|
| a = 0, v = 1, 2, 5 | v unchanged | 7 |
| a = 1, v = 1 | 3 = lvl 1 1 | 105 |
| a = 1, v = 2 | 255 = lvl 1 2 | 68 384 |

a >= 2 is beyond simulation rather than merely slow: `lvl 2 1 = 65535` already
forces a round over 65 535 marks, about 4e9 steps.  Nothing above is a proof, and
this is still not eps_1: the count field is re-read as a value, not as an ordinal
notation, so the class is one level above eps_0's.

### The value level, in Rocq

`rocq/Eps1Ladder.v` is the specification the table meets.  `stage v = 2^(v+1)-1`
(`stage_is_rounds`: the proven round rule at the count the value gives), n stages
are `run n`, and the rung is

    lvl 0 v     = v
    lvl (S k) v = run (lvl k v) v

The file also records the mistake that keeps looking tempting: the rung is **not**
"nest `stage` k times" -- that is still one exponentiation of height k, the eps_0
rung in a different hat.  Proved there: `stage` monotone, strictly increasing and
non-lowering; `run` additive, monotone in both arguments, non-lowering; `lvl`
monotone and strictly growing at the previous rung's own output
(`lvl_strict_rung`); and the rung separation `run c v <= lvl (S k) (v + c)` for
every fixed c (`lvl_beats_fixed`), the same gap `Eps1.v` proves one rung down.
`verify.sh` is at 156 closed theorems.

The tape-level counterpart is proved for the rung branch and the block-spent
decision, and **not** for the eps_0 stage branch's rounds (`rocq/Eps1Tape.v`,
`rocq/Eps1Copy.v`).  Proved there, for every gap m, budget length and value
length v: `ENTRY` reaches the copy's entry in 2m + 7 steps with one budget mark
spent, the block region blank and flush, and the value region untouched
(`rung_reaches_copy`); with one mark left it halts with the value intact
(`rung_halts`, `rung_halt_conf`, `rung_halts_run`).  The table in that file is
generated from `tools/eps1_machine.py` by `tools/emit_eps1_tape.py`, so the
machine that is proved about is the machine that runs, and
`tools/check_eps1_tape.py` runs the same frames through the simulator and
compares step counts and tapes.

The stage branch's *decision* is proved too, and composed with the rung branch:
`S1` erases a block mark, `S2` asks whether another is left, and on a blank both
hand over to `ENTRY`.  `block_spent_reaches_copy` (with its `_S1` twin) takes
that handover through the rung branch to the copy's entry: from `S2` on a blank,
2M + 10 steps to `WALK` in the frame `rung_reaches_copy` produces, the gap one
cell wider because the blank the decision stopped on joins the gap.  Sixteen
cases (`block_spent` in `tools/check_eps1_tape.py`, both states, several M, a, b,
v) match the running machine.  The branch's interior is now proved:
`round_v` covers every value length and `stage_run` composes it over every
counter length (`rocq/Eps0Round.v`, `rocq/Eps0Stage.v`).  The copy is started too: `rocq/Eps1Copy.v` has the copy's rows, one step lemma
per row, and the walks its phases are made of (`walk_WALK`, `steps_C1`,
`walk_CL_marks`, `walk_CL_blank`, `walk_CG`, `step_B1`, `walk_B2`, `walk_P1`),
each for an arbitrary run length with an exact step count, its table generated
by `tools/emit_eps1_copy.py`, and every frame checked against the running
machine by `tools/check_eps1_copy.py` (994 frames, all matching).
`trip_out` composes those phases into one run: from the trip's start frame,
2m + D + 11 steps reach the point where the budget carry begins, with the block
one mark longer and the corridor written flush; that statement, not only its
phase lemmas, is checked against the machine on 432 parameter sets.
The return half is proved too: `trip_back` carries the budget's mark to its left
end, walks back over the budget, the gap, the block and the wall, and comes back
along the copy to the next source cell, in 2n + 2m + D + 12 steps, out of eight
phase lemmas (P2, P3, P4, P5, BQ, BW, R1, R2), each with an exact count.  Chained
with `trip_out` that gives **`trip`**: one trip, from `trip_frame (S m) D (S n) A`
to `trip_frame (S (S m)) D (S n) A` in 4m + 2D + 2(S n) + 21 steps -- both runs
one mark longer, the budget one cell further left, the head on the source's next
cell.  Every one of those statements, composed ones included, is checked against
the running machine (`tools/check_eps1_copy.py`, 994 frames, all matching).
The sweep is proved too.  `sweep`: from the trip's frame with the head on the
source's first mark and w marks behind it, `sweep_steps (S w) j d n` steps return
`trip_frame (j + S w) D k` with the head on the blank after the source's last mark
-- the block and the copy both `1^(j + S w)`, the budget S w cells further left,
and the value's tail `skipn (j + S w) A` untouched, i.e. every mark the copy eats
is preserved in the block.  It is an induction on w; one round is `trip_step`, a
trip at *any* frame index j <= N, which is `trip` for j = S m and `trip0` for
j = 0.  `trip0` is the first trip, from an empty block and empty copy, in
2D + 2(S n) + 17 steps; at j = 0 the phase chain does degenerate (P5 lands on a
blank, R2 walks no marks, and the block's single mark comes from B2's own blank
row), so it has its own chain.  The count is a Fixpoint over the frame index,
`sweep_steps`, with the closed form v * (4j + 2(S d) + 2(S n) + 15) + 2vv; so v
trips from frame j cost v*(4j + 2D + 2k + 15) + 2v^2.

Every statement, composed ones included, is checked against the running machine,
each frame built from the statement's start and run for the statement's own step
count (`tools/check_eps1_copy.py`, 994 frames, all matching).  Of those, 96 are
the composed sweep -- up to four trips from frames j = 0, 1, 2, with the count
taken from `sweep_steps` -- and raising that count by one makes all 96 fail, so
the composed cases test the count and not only the frame.

What is **not** proved here: the frame is the one step 4's prologue builds, and
the ladder side (`a` count of halves, the eps_0 stage branch) is not part of this
file.  So what is proved is "the copy copies for every v", not "the machine runs
the ladder".  The whole copy's measured total, 2v^2 + 2vD + 2vk + 12v + 2G + 6,
is the sweep's count plus the entrance and exit outside it; no theorem depends on
that number.

## Why a 35-state claim cannot be checked here

`f_{ε₁}(71)` is beyond any simulation — the first descent step alone unfolds
ε₁ to a tower of 71 omegas, and one more unfolding is a tower of that height.
No run of any table can confirm a step count at that scale, so the claim would
have to rest on a symbolic proof of the machine's descent, which is exactly
what does not exist yet (module K's round is still a numeric check, not a
theorem).

A machine file that *looks* like 35 states and halts somewhere is easy to
write; it would not be at ε₁, and saying otherwise would be false.

## What 35 states could plausibly buy

Two allocations that fit the budget:

1. 7 K + 12 boot/drive + 8 feedback + 8 second-feedback header = 35, with the
   ordinal descent implemented by *reusing* the same module in a different
   tape frame (the only way the count fits).
2. 7 K + 10 boot/drive + 18 for a Goodstein-style descent, dropping the tower
   feedback entirely (this is the shape of the census's high-level machines).

Both are designs on paper.  The honest order of work is: close module K's round
in Rocq, build the tower machine and check it at small heights, then add the
second feedback — and only then is a state count at ε₁ a statement rather than
a wish.
