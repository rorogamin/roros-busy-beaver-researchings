# Gemini 2 CET/FGH submission — verification audit

Date: 2026-11-12

Status: **NOT VERIFIED**

The submitted files are preserved in `gemini2_incoming/`. They are not part of
`CET_ARTIFACT_BUNDLE`, and no champion record was changed.

## 1. CET(4) `CET4_7e43.v`

Claimed machine:

    1LB1RA_1RC0LD_1LA0LB_0RB0RA|1RB0LC_1LA0RC_1LD0RA_1RC1RA

Claimed result: exact halt at

    78159823316003962837401627984426228547406259

via `cet4_7e43_halts`.

### Rocq result

The file **does not compile** with Rocq 9.1. The first failure is:

    File "CET4_7e43.v", line 196, characters 2-9:
    Error: No product even after head-reduction.

I corrected the local bullet/tactic issue in a scratch copy. The next failure
was at the `assert (Hr1 : ...)` proof:

    Error: Found no subterm matching
    "pos1 (run_N a1 a2 n c2)"
    in the current goal.

I did not keep rewriting the proof. The submitted file does not establish
`cet4_7e43_halts` as delivered, and the later proof obligations are not merely
a missing bracket.

### Python result

`verify_all_submissions.py` does pass its own checks:

- raw prefix to step 3720;
- the formula `T(L,z) = 9*2^(L+z-1) - 5*z - 3` for small `L,z`;
- arithmetic for the quoted 7.816e43 number.

Those are **not** a replay of the claimed 7.816e43-step run and do not prove
`halts_at_exact`. The script never checks the final theorem or a collision at
that step.

Verdict: **UNVERIFIED**. The numeric candidate may be interesting, but it has
no compiled Rocq proof and no exact machine replay.

## 2. CET(2,3) `CET23_R8.v`

Claimed machine:

    1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA

The file claims the round-2 prefix at `t = 844`: `pos1 = 86`, `pos2 = 96`.

### Rocq result

The file **does not compile**:

    File "CET23_R8.v", line 323, characters 10-13:
    Error: Unable to unify "86" with "76".

The failing assertion is exactly the claimed position:

    assert (Hst : fc_844.(fpos1) = 86 /\ ...)
      by (repeat split; vm_compute; reflexivity).

Rocq's own fast engine computes `fc_844.(fpos1) = 76`, while the theorem asks
for `86`.

An independent direct replay with the CET semantics gives `pos1 = 86` at
`t = 844`. So there is a genuine inconsistency between the submitted fast
engine and the claimed theorem, not a cosmetic syntax error. The proof cannot
be accepted until the engine, the position, or the proof is corrected and the
result is re-derived.

Even if the prefix were fixed, the submitted text itself says the remaining
8-round base-3 odometer tower is not formalized. A prefix theorem is not a
champion proof.

Verdict: **UNVERIFIED**.

## 3. `Eps1Complete.v`

The file claims:

- `eps1_a1_halts`: blank tape halts at step 107 with score 5;
- `eps1_a2_enters_copy`: a=2 prologue reaches a copy configuration;
- a parametric `Eps1Ladder.lvl` induction for arbitrary `a >= 2` remains open.

### Rocq result

The file **does not compile as delivered**:

    File "Eps1Complete.v", line 65, characters 6-18:
    Error: The term "btbl_eps1_a1" has type "table"
    while it is expected to have type "nat".

This is because `Eps1Ladder.run` shadows `TM.run` after the imports. Qualifying
the calls as `TM.run` gets past the name resolution error, but then the claimed
halt configuration fails:

    Error: Unable to unify
      "Some {| cst := 69; clft := [bl; on]; ccur := bl;
               crgt := [bl; bl; bl; bl; bl; on; bl; bl; on; bl; on] |}"
    with
      "Some {| cst := 69; clft := []; ccur := bl;
               crgt := [bl; ...; on; on; on; bl; on] |}".

So `eps1_a1_halts` does not prove the stated `cf_a1`; the config or the run is
wrong. This is a proof-structure/result mismatch, not a namespace typo.

The file also does not contain the parametric theorem described in its header.
It has concrete a=1 and a=2 prologue results, not a closed theorem that the
machine computes `f_ε1` for general budget or satisfies the FGH step rule.

Verdict: **NOT AN FGH MACHINE** and not a verified ε1 result.

## 4. What the Python verifier actually verifies

`verify_all_submissions.py` checks:

- the CET(4) prefix at 3720 steps;
- small-`L,z` samples of the counter formula;
- the arithmetic value of the claimed 7.816e43 constant;
- the CET(2,3) prefix at 844 steps;
- the a=1 ε1 table halting at 107 with score 5.

It does **not**:

- compile or inspect any `.v` file;
- run the CET(4) machine to the claimed final step;
- prove `halts_at_exact`;
- check the CET(2,3) tower;
- prove the parametric ε1/FGH result.

Its final `ALL STANDALONE VERIFICATIONS PASSED!` is therefore not a Rocq
verification, and does not support the submission's stated proof status.

## 5. Disposition

- Keep `CET4_7e43.v`, `CET23_R8.v`, `Eps1Complete.v`, and
  `verify_all_submissions.py` in `gemini2_incoming/` as unverified submissions.
- Do not merge them into `rocq/` or the artifact bundle.
- Do not update CET records.
- For CET(4), require a compiling `halts_at_exact` theorem plus an independent
  exact replay or a checked derivation of the final step.
- For CET(2,3), resolve the 86-versus-76 engine mismatch and formalize the
  entire tower, not only the prefix.
- For ε1, prove the exact blank-tape run and a parametric theorem tying
  `btbl_eps1_a2` (or its general form) to `Eps1Ladder.lvl`/`f_ε1`, with no
  axioms, parameters, or admits.

The verified bundle and its existing records remain unchanged.
