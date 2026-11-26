# CET(4) formal skeleton

This directory is a **falsification harness, not two proofs.**

It exists because the question was "make one Lean proof that they all halt, and
one that they all can't halt, and see which one gets disproven". Those two
statements are mutually exclusive, so at most one can be true — meaning at least
one of the two files would be a proof of a false statement. Neither claim is
currently known to be true or false, no machine has a halt witness, no machine
has a non-halting invariant, and no Lean toolchain was available when this was
written. So what is here instead is: exact semantics, the ladder generated
mechanically from `ladder.json`, three conjectures stated as obligations, and the
results that can honestly be proved — that they contradict each other, and that
together they exhaust the possibilities.

## Contents

| file | status |
|---|---|
| `CET4/Basic.lean` | semantics; **proved**: `trichotomy`, `allHalt_and_noneHalt_contradict`, plus the exclusion lemmas |
| `CET4/Ladder.lean` | generated from `../ladder.json`; 11 pairs, no hand transcription |
| `CET4/AllHalt.lean` | `all_halt : AllHalt Ladder` — **`sorry`**, unproved |
| `CET4/NoneHalt.lean` | `none_halt : NoneHalt Ladder` — **`sorry`**, unproved |
| `CET4/Mixed.lean` | `mixed_ladder : Mixed Ladder` — **`sorry`**, unproved |
| `emit_ladder.js` | regenerates `CET4/Ladder.lean` |

The three conjectures are:

| | statement | def | dies to |
|---|---|---|---|
| A | all eleven halt | `AllHalt` | one non-halting proof |
| B | all eleven never halt | `NoneHalt` | one halt witness |
| C | at least one halts, at least one does not | `Mixed` | a full settlement of all eleven |

`AllHalt`, `NoneHalt` and `Mixed` are defined in `Basic.lean` as
`∀ M ∈ Ladder, Halts M`, `∀ M ∈ Ladder, NonHalts M`, and
`(∃ M ∈ Ladder, Halts M) ∧ (∃ M ∈ Ladder, NonHalts M)` respectively.

## The proved part

Facts about the *logic* of the conjectures, none about any machine:

- `halts_or_nonhalts : Halts M ∨ NonHalts M` — every pair does one or the other.
  This says nothing about which.
- `halts_not_nonHalts` — a halting pair is not a non-halting pair.
- `mixed_not_allHalt`, `mixed_not_noneHalt` — C excludes both A and B.
- `allHalt_and_noneHalt_contradict : L ≠ [] → ¬ (AllHalt L ∧ NoneHalt L)` —
  A and B cannot both hold. This is the reason the requested pair of proofs cannot
  both exist.
- `trichotomy : AllHalt L ∨ NoneHalt L ∨ Mixed L` — the three exhaust the space.
  Combined with the exclusions, exactly one of the three holds for a non-empty
  ladder, so A, B and C are a genuine three-way split rather than a list.

Also `halts_implies_haltsBy` and `noneHalt_no_haltsBy`, which connect `Halts`
to the finite, decidable `HaltsBy M N`. `HaltsBy` is the only halting predicate a
computer can ever establish.

## Checking it

```sh
cd proof
lake build            # then look for the "declaration uses 'sorry'" warnings
```

`AllHalt.lean`, `NoneHalt.lean` and `Mixed.lean` each end with `#print axioms`.
All three will print `sorryAx`, which is the honest signal that the conjecture is
open. A completed proof would print only the usual axioms (`propext`,
`Classical.choice`, `Quot.sound`) or nothing at all if it is computational.

**The toolchain is pinned to `leanprover/lean4:v4.9.0`. Bump `lean-toolchain` if
it is not available. None of these files was ever compiled — no Lean, Lake, Coq
or Rocq is installed on the machine that wrote them — so expect the first
`lake build` to need small syntax fixes. That is a known limitation, not an
oversight.**

## Semantics, and why they matter

The definitions in `Basic.lean` follow the pipeline in the parent directory:

- Both agents read the old tape, then both write, then both move — every step.
- If both heads write the same cell, **agent 1's write wins**.
- The pair halts when the heads share a cell **after** a step. Time 0 is not a
  collision: the heads start at 0 and 2, both in state A.
- The tape is `Int → Bool`, blank everywhere. Touched cells are the only
  `true`s. No seeded tape, no bound on the tape.

If any of these disagree with `cet_pair_sim.js`, the Lean ladder is describing
different machines than the simulator, and every result here is about the wrong
object. That check has not been made.

One decision deliberately *not* taken: `Ladder` is a concrete 11-element list, so
`AllHalt Ladder` is not vacuous. If it were a parameter or an empty list, the
statement would be trivially true and the exercise pointless.

## What each direction would actually need

**`all_halt`** — an explicit `t` per machine with the heads colliding. Easy in
principle for a machine that halts young; impossible to state for Comet as a
`Nat`, since the claimed halt time is a power tower. Would need bignum arithmetic
or a restatement as a growth relation on digit counts.

**`none_halt`** — an inductive invariant per machine. Currently the only plausible
route: each pair appears to decouple into one agent bounded in a box of width
`L2` and one agent executing a repeating cycle with net drift, so a periodic-orbit
certificate may be within reach for some of the eleven. None has been built.

**`mixed_ladder`** — one of each. A halt witness (finite, checkable) plus a
non-halting invariant (never checkable by simulation). Most plausible of the
three, hardest to prove, and least falsifiable: it survives every partial result
that A and B would each die to.

None is supported today. In particular, "no halt within 4·10⁶ steps" is not
evidence in any direction: the 5-state busy-beaver champion needs 47,176,870
steps, so a bound below that is vacuous against a claimed `10↑↑24`.

## Regenerating the ladder

```sh
cd proof
node emit_ladder.js
```

`ladder.json.order` is authoritative. Its `entries` array is **not** in ladder
order, so enumerating `entries` directly misnumbers machines 2–11.
