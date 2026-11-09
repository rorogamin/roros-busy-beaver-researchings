# EPS1_WALKWALL.md — the walk-back fusion wall: a full case analysis

Date: 2026-11-03.  Written during the "super duper push" after the
state count reached 82/84 (sn=1/sn=2) and 86 (sn=3).

## 1. The wall, stated precisely

The machine rest-to-rest campaign has two long opponents:

  * the DISPATCH WALK: from the rest mark (the top run's last mark E)
    leftward over the whole chain to the park's look cell C0-3
    (D2..D5 + WAD/WAZ/WAS, WAE/WAZB/WASB).  It must reach the park
    because `p` (the parked count) is only decidable there, and `p`
    selects the route arm (plain dec / absorb / fs append / fs-limit).
  * the WALK BACK: from the look region rightward over the park, the
    sep and the whole chain to the top run's right end, plus the climb
    (X4/X5) and the landing action (WB_P* → IN, WR_FS* → DECF,
    WB_ABS* → ABS_E, WR_A* → RAW, RW1..3 → RW4, BR → IN).

The walk back is duplicated once per landing case (six families, ~28
states across builds 1-3 before the spend fold).  Fusing them into one
shared rightward walker would save the bulk of that.

The blocker: **the fork-problem.**  Every state in a shared walker has
at most two rows (one per read symbol).  The case identity (which model
action must follow the walk) is nowhere on the tape: the cases differ
only in an earlier decision taken at the stay/look, and the walk's
terminal geometry — (0,0) at the chain end, resolved by the third read
— is *identical* for every case.  A shared walker's 0-row can therefore
route only one case's tail.  Concretely (from tools/eps1_mergehunt.py,
the pair report): ~323 state pairs across the builds differ ONLY in
successor names, and each pair is exactly one such fork away from a
merge.  The bisimulation checker of record confirms the shipped table
is at its equivalent-state floor (all classes singletons).

## 2. A flag-cell proposal, and why it fails

The natural scheme: reserve a "flag cell" past the chain end (the first
blank after the terminator pair; every campaign's walk stops exactly
there during the 3-deep test).  Each case writes its bit into the flag
cell before or during the walk; the shared walker branches on the flag
at the walk's end instead of on nothing.

It fails on positions, not ideas:

  * **Write-at-campaign-start**: the flag cell lies ~L+2k+3 cells right
    of every launch position; launch states cannot reach it without a
    walk of their own (the very thing being deleted).
  * **Write-during-the-walk**: the walker is shared; it cannot decide
    *what* to write there — that is the missing information.
  * **Write-behind-the-head**: any bit the launch cluster can write (at
    the park or the chain head) sits left of a rightward walk; the walk
    leaves it behind and never reads it.
  * **Chain-internal encoding**: the runs are the count; holes or
    extra marks break decode_tape (an interior short run is an atom
    form, not a free bit).

## 3. What did work this round: reordering beats fusion

The fs spend (erase the park's leftmost mark) used to run *after* the
append, forcing the SWT1/SWC/SWZ/SWX/SWP/SE cluster: a full leftward
crossing of the freshly grown chain plus the sep plus the park.  The
round-3 insight: the campaign contract only fixes the *net landing*,
not the order of actions.  The spend folds into the fs look arm —
FSL walks left over the park, FSP erases the leftmost and enters the
walk back directly (the walk back's 3-deep test resolves the post-erase
park edge correctly for p=1 and p>=2 alike).  The append's close write
(SWT1) now rests the machine on the new last mark in one hop.  Net:
-4 states per build, zero new tape geometry.  Lesson for future
rounds: hunt for *ordering* freedom first; it converts whole
state clusters into nothing.

## 4. What remains blocked, and its honest price

  * The four p>=1 walk-back X-families (WR_FS, WB_ABS, WR_A, RW) plus
    the p0 plain (WBX/WB_P) and BR: each family = shared-shape X1..X5
    with a forked tail.  Without a positionally-placed case bit they
    cannot share.  Price of the wall: ~3 x 5 = 15 states (build 1).
  * The append A-chain (A{sn+3}..A1 + APW1/2) is a true counter; two
    symbols cannot count without states.  It is already minimal for
    its shape (its dead .1 defensive rows — the appended zone is blank
    when written — are the only slack, and removing rows there barely
    helps the count).
  * The cascade measure (MSE/CM1..4/SB2/SH1) counts marks with states
    for the same reason; the CM3~SH1 pair is a wall case.

## 5. What a next-generation encoding would need

The clean dream is a machine where the case bit lives *at the walk's
terminal position*: e.g. the terminator pair replaced by a single
sentinel scheme whose second cell carries the running case, written by
the previous dispatch's early moves at a cell the walk will pass.  On
this one-track two-symbol tape with contiguous runs every such cell is
load-bearing (counts, closes, sep or sentinel).  A multi-track format,
or moving the count into a self-delimiting code, could free it — at
the cost of re-proving the whole decode and the f_ordinal Rocq
obligation against the new encoding.  That is a false economy at sn
<= 3 scale; park it until the Rocq layer is green again and the state
target is missed badly enough to matter.
