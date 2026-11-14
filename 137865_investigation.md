# Holdout 137865 — investigation note

> **STATUS: NOT PROVED. NOTHING HERE IS KERNEL-CHECKED.**
> (The Python port behind the empirical numbers has since been cross-checked against the
> compiled Lean `next` — see Caveats. A cross-check is not a proof.)
> No Lean theorem was added for this machine. This note records a reduction and a
> set of negative results, so that the next attempt does not redo them.
> Do not cite this as evidence that `137865` is non-halting.

## Machine

- Busy Beaver holdout id **137865** (of the 608 BB(6) holdouts, `BB6_holdouts_608.txt`).
- RLE: `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`
- Module: `cryptids_a6/BusyBeaver/BB6/M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean`
  - RLE appears at line 59; `def start : State := .D 1 0 0` at line 1432;
    `def next` (21 clauses) at line 1442; `is_valid_acceleration` at line 1662;
    `isHalt_iff_acceleration` at line 1792.
- The module already contains a complete, checked *reduction*
  (`IsHalt target ↔ CollatzHalts next start`). It contains no non-halting result.
- Raw machine: no halt in 200,000 steps from the blank tape. This is consistent with
  holdout status and proves nothing.

## Why this machine was worth attacking

An automated screen of all 86 in-list holdouts that have a repo module classified each
`next` by its arithmetic: 30 use `%`, 37 use `*` (doubling / exponential cascade),
3 use `/ 3`. Exactly **20** have a purely linear `next` (no `%`, no `/ 3`, no `*`),
which is the only class in which an A6-style closed family could plausibly be closed.
`137865` is one of those 20, and its `next` has a single halt clause.

**Caveat on that classification.** The screen read `def next` only. This module's
high-level acceleration `highLevelNext` does contain doubling (`2 * a + 3`), so the machine
is *not* purely linear one level up. The linearity that motivated the attack is a property
of `next`, not of the whole reduction, and a proof at the high level would face the same
doubling as the other 37 cascade machines.

## The reduction (by rule inspection of the 21 clauses)

**Only halt clause.** Line 1456: `| .E _ 0 3 => none`; every other clause of `def next`
returns `some`, so halting is exactly reaching `E a 0 3`. The high-level acceleration
`highLevelNext` independently has the same unique halt clause (line 1816), so the halt
condition is unchanged at that level (`isHalt_iff_highLevel_acceleration`, line 2089).

**Sole entrance to the halt state.** In state `E a b c` with `b = 0`:

- `c = 1, 2` → `D`; `c = 4, 5, 6` → `D`; `c >= 7` → `E 1 (a+3) (c-6)`.
- The only clause that produces `E _ 0 3` is the `b >= 1` rule
  `| .E a (b + 1) (c + 3) => some (.E (a + 2) b (c + 1))`
  specialised to `b = 0, c = 2`, i.e. from `E a 1 5`.

Hence

> **non-halting for `137865` ⟺ no reachable state is `E a 1 5`.**

This is a strictly sharper target than "`next` is total on reachable states", and it is
where an attempt should start.

## Descent invariants

For `b >= 1` and `c >= 3` the rule is `(a,b,c) -> (a+2, b-1, c-2)`. Therefore both

- `a + 2b`, and
- `c - 2b`

are exactly invariant along a descent. A descent from a state with `c - 2b = d` reaches
`b = 0` at `c = d`, and reaches `(1,5)` precisely when `d = 3`. So the halt condition is
exactly **`c - 2b = 3`**.

Empirically (`c - 2b`) never equals 3: over 400,000 abstract steps the quantity ranges
across 874 distinct values in `[-2510, 2436]` and never hits 3.

## Why that invariant cannot be used as-is

The `b = 0` rule rewrites it. For `c >= 7`,
`E a 0 c -> E 1 (a+3) (c-6)`, which has `c - 2b = c - 2a - 12`, not `c`. So `d = 3`
can be *created*: a `b = 0` state with `c = 2a + 15` jumps to `d = 3`. This is not
hypothetical — by the rules:

```
E 1 0 17 -> E 1 4 11 -> E 3 3 9 -> E 5 2 7 -> E 7 1 5 -> E 9 0 3   (halt, 5 steps)
```

So any proof must exclude **both** `c = 3` and `c = 2a + 15` at `b = 0`. Iterating the
`b = 0` map `(a, c) -> (2a+7, c-2a-12)` pushes the danger set to `c = 6a + 41`, then
`c = 14a + ...`, an infinite family of forbidden arithmetic conditions.

## Negative results (do not redo these)

All figures from a hand-transcribed Python port of the 21 clauses, run from
`start = .D 1 0 0` for 400,000 abstract steps (no halt).

1. **Linear / modular invariants: none.** Exhaustive over `alpha*a + beta*b + gamma*c ≡ const (mod m)`
   for `m <= 14` and `alpha, beta, gamma` in `[-4,4]`, sampled on 120,000 reachable states.
   176 hits, every one trivial (coefficients collapsing to zero, or the `m = 2` parity
   collapse). Invariants that exclude the halt state and hold on `E` states: **0**.
2. **Bound invariants: none.** `c <= 2a + 13` at `b = 0` (which would kill both `c = 3`
   and `c = 2a + 15`) is false: observed `max (c - 2a) = 2422`, still increasing.
3. **Residue / parity at `b = 0`: none.** All six residues occur for `c mod 6`, including
   3, the halt residue. Odd `c` occurs at exactly six `b = 0` states:
   `(1,7)`, `(1,463)`, `(9,449)`, `(25,419)`, `(57,357)`, `(121,231)`.
   The last two have `c ≡ 3 (mod 6)` and still do not halt, because the `b = 0` rule sets
   `b := a + 3 > 0` and leaves the corridor immediately. **No argument about `c` alone can
   work**; `b` must be tracked exactly.
4. **No cycle to quotient by.** 625 visits to `b = 0` gave 625 *distinct* `(a,c)` pairs.
5. **The only surviving invariant is too weak.** `a` is odd at every `E` state
   (199,351 `E` states, assertion never fired). The halt state `E a 0 3` also has `a` odd,
   so this does not separate the dangerous set.

Conclusion: the reachable set at `b = 0` is unbounded, aperiodic, all-residue, and has no
finite description of the kinds searched. It behaves like a genuine two-counter
Collatz-class system, so a reachability characterization would essentially *be* the proof.

## Caveats

- Everything above except the rule-level reduction is **empirical**, obtained from a port
  transcribed by hand.
- That port has been **cross-checked against the compiled Lean `next`** (the real built
  module, evaluated with `#eval`, not a hand copy), in two rounds:
  1. **616/616 lines identical** — a 400-step orbit from `start`, plus a single-step grid
     over `a ∈ 0..3`, `b ∈ 0..2`, `c ∈ 0..8` for both `D` and `E` (216 cases, whose
     results exercise all 21 clauses). The only four `HALT` results were `E a 0 3` for
     `a = 0..3`, exactly the halt condition claimed above.
  2. **17,439/17,439 lines identical** — a seeded random sample (seed `20261109`):
     5,000 single-step states (mixed `D`/`E`, 55% of values in `0..20` to hit the small-case
     clauses, the rest up to 3,000) and 500 random seeds each followed for 25 steps.
- Both checks are **samples, not a proof of equivalence**: they cover those inputs, not the
  unbounded state space, and the runs quoted in this note (400,000 abstract steps) extend
  past any verified prefix. Treat simulated orbit facts as well-supported leads, not facts.
- An earlier port of a *different* machine in this repo produced a spurious 2-cycle before
  the error was found, which is why this port was cross-checked at all.
- The reduction (`non-halting ⟺ E a 1 5 unreachable`) is by inspection of the 21 clauses
  and is independently checkable by reading lines 1442-1463 of the module.
- Nothing has been added to `championsReal.txt`. That ledger remains proofs-only.

## What a proof would need

An argument that `E a 1 5` is unreachable, tracking `b` exactly through the `b = 0`
rewrite `b := a + 3`. The `D` side is already closed: the sweep `D (a+1) b c -> D a b (c+2)`
preserves `c + 2a` and `b`, exiting at `D 0 b R` with `R = c0 + 2*a0` to `E 1 0 R`,
`E 1 2 (R-2)`, or `E 1 (b-2) (R+2)`. The missing piece is a reachability statement about
the `(a,c)` counter values, which the searches above did not yield.
