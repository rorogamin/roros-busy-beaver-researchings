# SUPER — the ≤40-state ε₁ machine, design record.

The verdict table (EPS1_67_PLAN §9) showed re-cutting the design's
fs phase below ~120 cannot reach 40: the pass-2 kernel costs
~27 states on any three-field re-cut, and the walk floor of the drain-frame
design is the reason.  The community record (EPS1_67_PLAN §10) shows what
machine above that exists: the champion is an ε₀ device, and its shape has
exactly ONE growing object — the self-describing descent list, which
carries the fs/pred/decrement information in the deformed copies of
itself, with no external index.

SUPER is that shape generalized to ε₁.  The descent below eps_1 is a
single tower w^p·val(chain) throughout the run (eps1_chain.py justifies
the single-term invariant), so the machine state compresses to one evolving
object: the tape IS the term.  The index n — the third field of the design
of record — is not a machine field here: it is paid for in the blank-tape
STARTUP (the setup unrolls eps_1[n] onto the tape; that unroll is where the
f_{eps_1}(n) step factor is spent — see the measure request in the
ledger).  This filters the third growing field out by representation, not
by re-cutting.

## The encoding, final (matches tools/eps1_super.py exactly)

One 0/1 string, left to right:

    [1-mark]*p  0  [frame]  0  E0 E1 ... Em-1  [0] [0...0 padding]

  * p marks: the counter field, then a separator 0.
  * the FRAME marks the bottom's kind, then an UNCONDITIONAL separator 0:
        plain numeral bottom: no frame (just the separator after p's zero)
        the atom (eps_0+1 in this project): frame `10`
        the atom + 1 (eps_0+2):             frame `110`
    Frames are prefix-free against each other and against the entries, so
    one unconditional separator is enough (the collision that killed v1:
    [atom, 1, x...] shared its cell pattern with [atom+1, x...] — frames
    removed it).
  * entry(c ≥ 1) = 1*(bitlen(c)+1) + 0 + bin(c) MSB-first: the run of 1s
    before the 0 gives the bit length, then exactly that many bits follow;
    entries sit head-to-tail with NO separators.
  * the chain ends at the first 0 not consumed by an entry's bit field.

Invariant kept by the codec: top-1 entries are normalised into p (the
same normalise() rule as eps1_chain), so a trailing 1 never sits on tape.

## What IS earned (this turn, model level)

`tools/eps1_super.py` — ALL OK:

  * codec round-trip: 300 cases; decode(encode(p, chain)) equals the
    independently rebuilt canonical form, covering atom and numeral
    bottoms, mid-chain 1s after the atom, and the normalisation;
  * move faithfulness: 200 random starts × up to 4 moves; every tape
    step computes eps1_chain's step at the fixed-seed parameter exactly
    (result and kind), and the parameter-free branch (successor at
    p == 0) matches eps1_descent's model value exactly;
  * layer agreement: full runs from eps_1[n] (n = 1, 2, 3) with the seed
    (1, 2) on the tape take exactly the chain-level move counts
    (9/30, 14/65, 20/136);
  * measured record (no claim): the fixed-parameter descent from
    eps_1[3] at seed 2 halts in 136 moves, while the Hardy
    bumping-index variant overruns a 200k cap at once — the step factor
    will have to be earned in the STARTUP, not the descent.  The
    f_{eps_1}(n) bound argument is open ledger work below.

## The state budget ledger (hypotheses to earn)

| phase                     | budget (hypothesis) |
|---------------------------|---------------------|
| reader/park: frame+reader | ≤ 10                |
| pred move on tape         | ≤ 12                |
| fs limit expansion        | ≤ 12                |
| setup (unroll eps_1[n]) + halt | ≤ 6           |

Each budget is earned only after: (1) a verified local-rewrite
realization of the corresponding move (head-stepping, no whole-tape
re-encode), (2) a 2-symbol table transcribed from the moves (the
`machines/` format), (3) machine-level checks like the drain device's,
and (4) for the final claim, Rocq verification under f_{eps_1}(n) with
the ruleseper AGENTS.md gate decision.  None of that is done yet at this writing.

## The open ledger items, honestly

  * NO 2-symbol table exists yet; no state count is claimed; 40 is a
    TARGET and nothing here proves it is attainable.
  * The moves currently re-encode the whole string per step (the model-cost
    stand-in; a TM cannot afford it); the local rewrites that a TM can afford are the
    next construction item and carry the true state budget.
  * The fs parameter semantics: the descent runs with the seed FIXED.
    Whether the "halt under f_{eps_1}(n) with the rules" gate accepts
    the fixed-seed variant, or requires the bumping index of the
    design of record, is an OPEN question — if the bumping semantics
    are required, the third field returns and the representation
    problem is open again.
  * The setup's unroll cost is unmeasured (the unroll writes eps_1[n]
    from blanks; its moves must fit the step budget with the factor).

## The unified ODOMETER rewrite (eps1_odi.py), design of record

Motivation (the BB(159) state-count concern): the per-case arm design
(`tools/eps1_super_local.py`, ~159/161 states) cannot be patched to 40 —
the census below shows the exec contract is a single mixed-radix
top-entry decrement with position-anchored edits, implementable by one
core of ~30-40 raw states.

### The census (fixed-seed `C.step` over full tier 1..3 x seed s ∈ {1,2})

148 distinct pre-step states crossed across the six runs; 12 classes:

  * 12 classes: plain bottoms with p 0/1 and tops 1,2,3; atom-bottom
    with 1-3 entries; the pure [ATOM1] (eps_0+2) singleton; the pure
    [ATOM](eps_0+1) singleton = the ONLY limit;
  * no `(·,[1])` plain singleton is ever visited (the `chain_fs`
    assert corner is unreachable in real runs — recorded, checked);
  * entries range over {1,2,3} only in tier ≤ 3 (the pushed n+1 run
    is compile-time constant = the pushed entry), but the core MUST
    implement the function for any chain, not tier-≤3 paths.

### The move contract (from `eps1_chain.step` at fixed seed sn)

Standard NORMALISE-then-apply on the chain of 'runs' (bottom-first,
ej entries after canonical fold into p):

  * fs (p ≥ 1, successor-kind): decrement_top + append [sn+1] entry
    at the top + ONE park mark erased;
  * pred (p == 0, successor-kind): decrement_top only;
  * fold: top-1 entries peel into p as park marks (until the top is
    ≥ 2 or the chain collapses; transiently non-canonical states
    exist mid-op; the fold pass runs BEFORE each exec decision);
  * singleton-atom limit (pure eps_0+1, p any): chain becomes the
    single entry [1] = NUM(1), p += sn;
  * pure [ATOM1] (eps_0+2) with p ≥ 1: (p−1, the single entry [sn+1])
    with the bottom now eps_0+1 (the frame flip);
  * halt: (·, []) — the chain emptied; no row = stop (the handoff
    convention), counted as the final move.

### The odi tape (eps1_table layout minus the index field)

    [1^p park]  0 0  [runs: 1^L 0 ...]  0 (extra chain end)  [blank *]

  * park right-anchored at C0-3 forever (handoff I1): p == 0 is a
    fixed look at the park separator's cell; spend = erase the
    park's LEFTMOST mark (walk), grow = write one cell left;
  * entry code: run length 1 = the atom (bottom), 2 = atom+1 (bottom),
    L ≥ 3 = the plain c = L−2; the bottom kind rides in the first run's
    length (no frame flags anywhere); seps are single 0s, so the terminator
    = first 00 pair walking right, and the home HT = the top run's last
    mark (two left of the pair's start, i.e. the last 1).
  * Holes are forbidden (no interior 00): pops RE-WRITE the entry zone's
    close cell so the single-0 separation invariant holds.

### State budget (hypothesis, honest)

    dispatch (fixed-look p + walk-left)        ~ 4
    pred shorten (top c ≥ 3)                   ~ 4-5
    fold cascade + absorb (top 1)              ~ 5-6
    fs push (append sn+1) + spend walk-back    ~ 8-10
    bottom-kind fork (walk to run 1 + test)    ~ 3-4
    atom-limit + atom1-flip                    ~ 5-6
    halt                                       0-1
    -------------------------------------------------
    raw total                                  ≈ 30-40 (40 only if it fits;
                                               refinement via eps1_minimise after)

### Verification (TBD this build, planned order)

  1. the 148 visited pre-step states: for each, the machine's
     one-move `decode(tape)`-after-step equals `C.step` exactly;
  2. random one-step battery: 400 chains x 4 moves byte-exact;
  3. fixed tier runs 1..3 x seeds 1..2: halting trip counts equal
     `C.run`'s (9/30, 14/65, 20/136);
  4. state count printed honestly, Moore refinement via
     `eps1_minimise` after green.

---------------------------------------------------------------------------
2026-11-03  odi status (the unified odometer rewrite, tools/eps1_odi.py)
---------------------------------------------------------------------------
Gate 1 green (274 exact landings, tiers 1..3, both seeds); Gate 3 green
(the six recorded tier counts, machine = frozen-index model walk; note that
C.run with the index forwarded cycles instead of halting).  State count
102/106 honestly above the 40-state target.  Gate 2 partial: the p0 pop
cascade (succ-top + the unit stack below, one park mark per pop,
length-variable run erasure, stop at the first non-unit) is the one
remaining failure class; the ABS/RP redesign of record is in HANDOFF.md.

### The dangerous layer and the verification boundary (recorded 3 Nov)

The champions page (carried in championsReal.txt line 319) records
BB(67) > q^81(q(5)-2) with q(n) from the Laver tables, alongside the
caveat that q(n)'s growth is unknown -- q(5)'s value is unknown, and even
its existence has no ZFC proof in hand.  So the layer at ~67 states is a
documented fact, not folklore.  odi's standing posture: ABOVE that layer
(96/98, every campaign count 9..136 simulable, all three gates run on
recorded paths).  Any drive at or under ~67 states changes the posture:
finite simulation stops being admissible evidence on its own, and the
standing rule applies -- halt at the specified ordinal, f_ordinal(n)
steps, verified in Rocq (the gates alone would not carry it).

-----------------------------------------------------------------------
2026-11-03  DESIGN DELTA after round 3 (the full follow-up turn)
-----------------------------------------------------------------------
The fs campaign no longer spends after the append.  The fs look arm
now owns the spend: FSL walks left over the park, FSP erases the park's
leftmost mark and the walk back enters from right of the erased cell;
the old SWT1/SWC/SWZ/SWX/SWP/SE cluster is gone and the append's close
write (SWT1) rests the machine on the new last mark in one hop.  The
route A park extension and route C growth write chains are parameterised
by sn (no more sn<=2 cap; build 3 runs the full battery clean:
86 states/152 rows, census 2418 landings 0 bad, tiers 184/557/1677).

The count of record: 82/84 (builds 1/2), 86 (build 3).  The walk-back
fusion wall is documented with a full case analysis in
EPS1_WALKWALL.md (the fork problem; the flag-cell scheme's failure on
positions; the reordering beats fusion lesson).  New tool: the merge
hunt (tools/eps1_mergehunt.py: floor proof, dead-row trace audit,
fork-problem pair report) and the adversarial battery
(tools/eps1_adversarial.py: deep cascade stacks and mixed chains,
ALL OK 19k starts across builds 1-3).

-----------------------------------------------------------------------
2026-11-03  DESIGN DELTA after round 4
-----------------------------------------------------------------------
An observed-context reduction pass now sits after the bisim minimise
in build_table.  Its merges (recorded in CONTEXT_MERGES in
tools/eps1_odi.py) fuse states that agree on every symbol they were
ever observed reading: the walk-home network (BR/BRZ/BRQ, the ROI
terminals), EA2, M2, and (builds 1-2) the RAW widen steps all fold
into the walk-back/cascade/append machinery.  The pass is sound on
reachable configurations given the corpus and is re-validated by the
full battery, the adversarial battery (5000 deep starts per build,
ALL OK) and extra gate-2 seeds.  The counts of record are 74/75/79
(builds sn=1/2/3); the remaining state count sits at the
observed-context fixpoint (a refreshed corpus found no further
merges).  The residual wall is unchanged in kind: the walk-back
families' landing tails and the append chain, documented in
EPS1_WALKWALL.md.

-----------------------------------------------------------------------
2026-11-11  r5 UNDER-50 GATE: measured NO (71/72/76)
-----------------------------------------------------------------------
The next one-object revision was measured with
`tools/eps1_odi_under50.py` (exit 0; every gate green):

    sn=1: 71 states / 128 rows, exact bisimulation floor 71
    sn=2: 72 states / 131 rows, exact bisimulation floor 72
    sn=3: 76 states / 138 rows, exact bisimulation floor 76

Gate 1 census landings are 43 / 231 / 2418, all model-equal; gate 2
is 400 starts per build, ALL OK; gate 3 tiers 1..7 are exact for all
three builds.  The separate observed-context pass found 0 further
merges on sn=1 and sn=2.  The floor is therefore 71 on the shipped
one-object layout, not 49.

The r5 route-A reordering was tested and rejected before shipping:
widening the singleton at dispatch and reusing the shared return walk
saves the WR_A family on paper, but the shared pred/home tail erases
the top mark at its terminal.  A corrected return needs a three-state
landing (and the park-extension writer), which gives the states back;
the experimental table was not gate-green and was not committed.  The
67-state U3 draft is not an alternative either: it dies at N3 and
fails move faithfulness.

Why the 21-state gap remains: the four p>=1/p0 walk-back families
(WB_P, WR_FS, WB_ABS, WR_A) plus their terminals, the append counter,
and the cascade measure.  This is the fork problem, not dead-row
slack: the trace corpus leaves dead rows but every candidate merge on
a live symbol changes a landing.  No under-50 table is claimed.  The
next architecture must free a case bit at the walk terminal (a
multi-track or self-delimiting code) or move the park to the active
end with an explicit park-shift rule; both remain open ledger items.

-----------------------------------------------------------------------
2026-11-11  r5 TIER-1 SPECIALIZATION: 61 states
-----------------------------------------------------------------------
The odometer pivot produced a smaller table for the exact tier-1 run,
`tools/eps1_odi_t1.py`.  It starts from the 71-state build, retains only
the rows fired by `chain_of(D.tower(1))`, prunes to reachable states,
and applies the two surviving observed-context merges:

    reached: 63 states / 89 rows
    merged:  61 states / 87 rows

the exact bisimulation pass on the restricted table has no further
merge.  The script checks all 9 tier-1 campaigns move-for-move against
`eps1_chain.step` and exits 0.  This is a run-specialized table, not the
general odometer: absent rows, tier-2+ inputs and FGH bounds are out of
scope, and no such claim is made.  The finite trace certificate below is
not an FGH proof.

-----------------------------------------------------------------------
2026-11-11  r5 TIER-1 ROCQ FINITE TRACE
-----------------------------------------------------------------------
`tools/emit_eps1_odi_t1_rocq.py` emits `rocq/Eps1OdiT1.v`, a generated,
self-contained finite-trace certificate for that same 61-state table:

    states 61 / rows 87
    rest1_at  ...  rest9_at   step_tm 24/55/77/98/126/167/186/203/214
    dead_at_215                step_tm 215 init = None
    exact_run                  step_tm 214 = Some rest9 /\ 215 = None

`coqc -Q . Top Eps1OdiT1.v` against Rocq 9.1.0 exits 0.  Every
`Print Assumptions` reports `Closed under the global context`; there is
no Axiom, Parameter, Hypothesis or Admitted step.  The first eight rest
configurations are the `eps1_chain` model's expected landings, so the
certificate checks model equality at eight boundaries and an empty tape
at the ninth; the ninth head is not part of an empty-tape configuration.

This is a finite trace certificate for the exact tier-1 run, not a proof
of a general odometer or of an FGH bound, and it does not change the
71/72/76 general counts.  The 61-state table still has deliberately
absent rows outside that run.
