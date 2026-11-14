# Gemini 3 CET/FGH submission — verification audit

Date: 2026-11-12

Status: **NOT VERIFIED**

The files are preserved in `gemini3_incoming/`. They are not part of
`CET_ARTIFACT_BUNDLE`, and no records were changed.

The files contain no textual `admit`, `Admitted`, `Axiom`, or `Parameter`
declarations. That is not enough: they must compile and prove the stated
theorems.

## 1. `CET4_R8.v`

Claimed machine:

    1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC

Claim: complete proof of `cet4_r8_halts`, an 8-round tower halt.

### Rocq result

The file **does not compile** with Rocq 9.1. The first error is:

    File "CET4_R8.v", line 140, characters 31-59:
    Error: No such goal.

This occurs in `cfg_eq_trans`:

    constructor; try congruence. eapply tape_eq_trans; eauto.

The `try congruence` has already closed the relevant goals, so the following
`eapply` has no goal. Removing that extra tactic gets past this point, but a
later proof is still incomplete:

    File "CET4_R8_test.v", line 212, characters 0-4:
    Error: (in proof step_agree_range): Attempt to save an incomplete proof
    (there are remaining open goals).

I stopped there. The submitted file does not establish `cet4_r8_halts` under
Rocq 9.1, and this is not merely a missing closing bracket. The claimed
`> 2↑↑7(200)` result is not verified.

## 2. `CET23_R8.v`

Claimed result: `prefix_844_ok`, with `pos1 = 86`, `pos2 = 96`.

### Rocq result

The file **does not compile**. The first error is the same extra-tactic issue:

    File "CET23_R8.v", line 129, characters 31-59:
    Error: No such goal.

After removing the extra `eapply`, the prefix checker itself fails:

    File "CET23_R8_test.v", line 331, characters 19-30:
    Error: Unable to unify "true" with "false".

That line is:

    Lemma fc_844_ok :
      check_fc_844 (N.iter 844 (fast_step_chk_range (-3) 98) (fc0, true)) = true.
    Proof. vm_compute. reflexivity. Qed.

So Rocq computes `false`, not `true`, for the submitted fast-engine prefix
check. The claimed prefix is not proved.

Even if the checker were fixed, the submission itself says the 8-round base-3
tower after `prefix_844_ok` is still missing. A prefix lemma is not a champion
proof.

## 3. `Eps1Complete.v`

The file claims a parametric blank-tape epsilon_1 construction, but its own
summary says the K-loop, stage loop, and general composition still need work.

### Rocq result

The file **does not compile**. The first error is:

    File "Eps1Complete.v", line 61, characters 4-14:
    Error: Found no subterm matching "hd bl V" in the current goal.

This is in `rung_halts_gen`, before the a=1/a=2 checks. The generalized rung
lemma is not proved as written.

The file contains concrete `btbl_eps1_a1` material and claims
`eps1_a1_halts_at_107`, but:

- the file does not compile;
- the generalized rung lemma fails;
- the K-loop and stage-loop are explicitly listed as remaining work;
- there is no closed theorem tying a general `btbl_eps1 a` to
  `Eps1Ladder.lvl a 1` or to `f_ε1`.

Therefore this is not an FGH-level machine under the project rule.

## 4. What is and is not established

Established only by inspection:

- no `admit`, `Admitted`, `Axiom`, or `Parameter` tokens were found;
- the files contain candidate theorem statements and substantial proof text.

Not established:

- compilation under Rocq 9.1;
- `cet4_r8_halts`;
- `prefix_844_ok`;
- `eps1_a1_halts_at_107`;
- any parametric `f_ε1` or FGH step bound.

The absence of forbidden vernacular is not a proof. These files must compile
with all goals closed and the printed assumptions closed.

## 5. Disposition

- Keep the three files in `gemini3_incoming/` as unverified submissions.
- Do not add them to `rocq/` or the artifact bundle.
- Do not update CET records.
- For CET(4), fix the incomplete proofs and compile `cet4_r8_halts` to a
  closed theorem before any record claim.
- For CET(2,3), first make `fc_844_ok` compute `true`, then formalize the entire
  tower, not just the prefix.
- For ε1, complete the generalized rung/K-loop/parametric composition and prove
  the exact FGH step relation in a closed theorem.
