# Target: sharpened shield and the cascade bridge

Target machine: `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`.

## What is now proved in Lean

`bbwork/lean/TM25.lean` compiles cleanly with the installed Lean 4.35 core
library.  There is no `sorry` in the file.

The new chain is:

- `ShieldBeforeOneDeep l`: scanning left from the head, there is a `4` before
  any `1`, and that `4` has at least one cell to its left.  Compared with the
  older `ShieldBeforeOne`, this removes the left-edge case where a `4` has no
  room for `cascade_dies_before_four`.
- `A3ShieldDeep`: every reachable `A`-on-`3` configuration has a deep shield.
- `cascade_from_A3_deep`: from any `A`-on-`3` with a deep shield, the next step
  is a left-moving cascade, and there are `N`, `d` with
  - no `none` in the first `N` steps,
  - `iter N = some d`,
  - `CascadeOver d`.
- `a3_deep_cascade`: the same statement with the endpoint reachable.
- `A3Shield_of_deep`: the deep invariant implies the older one.
- `not_halts_of_A3ShieldDeep_B1Safe`: if `A3ShieldDeep` and `B1Safe` were
  global, the machine would not halt.
- `A3MarginOne`: the observed `4 1` boundary shape, `l = u ++ 4 :: 1 :: zs`
  with no `1` in `u`.
- `a3MarginOne_deep`: every margin-1 boundary is a deep shield.
- `shieldDeep_cons`: prepending any non-`1` cell preserves the deep shield.
- `a3_margin_one_cascade`: an `A`-on-`3` with the `4 1` boundary reaches a
  `CascadeOver` state without halting first.

`#print axioms` reports only `propext` and `Quot.sound` for the new cascade and
nonhalting theorems.  The ordinary finite certificate
`invariants_checked_to_hundred_million` additionally uses its generated
`native_decide` axiom, which is expected for a compiled evaluation certificate.
The deep finite certificate is deliberately limited to `10^6`
(`invariantsDeep_checked_to_million`) so the main artifact stays quick to check;
the much larger deep evidence is the external checker below.  Both compiled
certificates use their generated `native_decide` axioms; this is expected and
is distinct from a `sorry`.

## Finite checks

- Lean: `checkInvariants 100000001 (some init) = true`, covering all states
  through step `10^8` for the ordinary `A3` shield and `B1Safe`.
- Lean: `checkInvariantsDeep 1000001 (some init) = true`, a fast compiled check
  of the sharpened shield through step `10^6`.
- External `leftshield.exe 100000000000`:
  `A3_left=657 violA3=0  B_left=49999999342  B1=377 B1_left1=0`.
  This is a finite run, not a proof.
- External `leftshield_deep2.exe 10000000000`:
  `A3_left=540 violA3=0 deepViol=0  B_left=4999999466  B1=315 B1_left1=0`.
- External `leftshield_deep2.exe 100000000000`:
  `A3_left=657 violA3=0 deepViol=0  B_left=49999999342  B1=377 B1_left1=0`.
  The checker requires a genuinely nonempty used-tape context to the left of
  the stopping `4`, not merely a nonzero array index.  These are finite runs,
  not proofs.
- `longacc` target run, effort 200, 10M iterations per row, 600 s:
  78 rows, width 278, `halted:false`, `timeout:true`.
- Context dump at `10^10`: 540 A3, 315 B1, `deep_fail=0`, maximum `d4=76`;
  at `10^11`: 657 A3, 377 B1, still `deep_fail=0`, maximum `d4=76`.
  Details in `a3_context_findings.md`.
- `fours` at `10^11`: 358 cascade births, minimum **1** cell holding a `4`
  between frontier and head; distribution `1:30, 2:16, 3:17, 4:55, 5:107,
  6:18, 7+:115`.
- `cantor` at `10^11`: 84 cascades, **0** Cantor-compatible; all 84 were
  blocked by a digit `1` (none only by `22`).
- `a3margin` at `10^10`: 68 margin-1 A3 events; the next A3 is deep in all
  **68/68** cases, and 52 of those successors are again margin-1.  This is a
  finite successor check, not a preservation theorem for all time.

## Context analysis

`a3context.c` dumps the actual nearest-first left prefixes at every A3 and B1.
At `10^10` steps there are 540 A3 births and 315 B1 visits:

- all 540 A3 births have a `4` before any `1` and a genuine left context
  (`deep_fail=0`);
- the nearest-4 distance reaches 76, so this is not a small-radius property;
- all 68 margin-1 A3 events have the boundary pattern `4 1`, and the cell
  immediately beyond the nearest `4` is always `0` or `1`;
- B1 has zero leading-`1` cases, but 34/315 B1 prefixes have no `4` in the
  80-cell window.  The uniform 4-shield therefore does not extend to B1; the
  separate `B1Safe` condition is necessary.

See `a3_context_findings.md` for the distributions and reproduction commands.

## Context analysis at 10^11

Repeating the A3/B1 dump at `10^11` gives 657 A3 births and 377 B1 visits.
There are still `no4=0`, `no1=0`, and `deep_fail=0`; the nearest-4 distance
still maxes at 76, and `d1-d4` still has minimum 1.  The B1 side still has
zero leading-1 cases, with 36/377 prefixes lacking a `4` in the 80-cell
window, so the B1 separation remains necessary.

## What remains open

`A3ShieldDeep` and `B1Safe` are hypotheses, not proved global invariants.  The
public halting question for this machine remains open.  In particular, the
finite checks are lower bounds/evidence and do not imply nonhalting.  The
remaining mathematical gap is the global shape invariant described in the
archived analysis: one must prove that every cascade birth has a deep `4`
shield, or prove the counter shield at every cascade, not merely observe it for
a finite prefix.
