# Gemini 4 CET/FGH submission — verification audit

Date: 2026-11-12

Status: **NOT VERIFIED**

The files are preserved in `gemini4_incoming/`. They are not part of
`CET_ARTIFACT_BUNDLE`, and no records were changed.

The files contain no textual `admit`, `Admitted`, `Axiom`, or `Parameter`
declarations. That does not establish compilation or correctness.

## 1. `CET4_R8.v`

Claimed result: `cet4_r8_halts` for

    1LB1RC_1LC1RB_1LD0LC_0RA0RB|1RB0RC_1RC0RD_1LA1LB_1RA0LC

with an 8-round tower.

### Rocq result

The submitted file does not compile. The first error is:

    File "CET4_R8.v", line 429, characters 10-13:
    Error: Unable to find an instance for the variables lo, hi.

This is in `fast_run_outside_zero`, at `apply IHn; auto`.

I repaired that argument inference and the next analogous one, then ran the
compile in the background. It did not finish within the practical timeout and
produced no `.vo` file. It was still consuming CPU after more than 80 seconds
of compilation. Therefore I cannot report `cet4_r8_halts` as compiled or
verified. The submitted file as delivered fails at line 429.

## 2. `CET23_R8.v`

Claimed result: `cet23_r8_halts` for

    1LB1RA0LB_2RB2LB2RA|2RB1LA1RB_2LB2RB1LA

with an 8-round base-3 tower.

### Rocq result

The file does not compile. The first error is in `bt_interp_set`:

    File "CET23_R8.v", line 282, characters 72-75:
    Error: ... Heq has type "z_to_pos p = z_to_pos z"
    while it is expected to have type "z_to_pos z = z_to_pos p".

After fixing that orientation, the next error is:

    Error: Unable to find an instance for the variable lo.

in `check_range_844_sound`. After supplying that argument, the next error is:

    Error: Unexpected name (no introduction patterns were expected in the
    branch).

at the `pose proof (fast_run_sound ...) as [Rp1 ...]` line. A `cfg_eq` record
is being introduced as if it were a tuple.

I stopped there. The submitted file does not prove `cet23_r8_halts` and does
not establish the claimed tower.

## 3. `Eps1Complete.v`

The file claims a completed parametric blank-tape epsilon_1 construction.
It does not compile.

First error:

    File "Eps1Complete.v", line 63, characters 23-35:
    Error: Unable to unify ...
    "TM.run tbl (?M1333 + 2) ..."
    with
    "TM.run tbl (m + 2) ...".

This is the generalized rung lemma `rung_halts_gen`. The state/tape shape used
in the call to `walk_G1_left` does not match the lemma's post-state: the
generalized lemma asks for `zeros b` on the left and `on` under the head,
while `walk_G1_left` leaves `tl A` and `hd bl A`. The statement and the proof
do not agree.

Therefore the claimed parametric `eps1_blank_tape_halts` theorem is not
established, and the file is not an FGH proof.

## 4. What is and is not established

Established by inspection only:

- no `admit`, `Admitted`, `Axiom`, or `Parameter` tokens were found;
- the files contain candidate theorem statements and substantial proof text.

Not established:

- compilation under Rocq 9.1 for any of the three files;
- `cet4_r8_halts`;
- `cet23_r8_halts`;
- `eps1_blank_tape_halts` or any parametric `f_ε1`/FGH result.

## 5. Disposition

- Keep the three submitted files in `gemini4_incoming/` as unverified.
- Do not add them to `rocq/` or the artifact bundle.
- Do not update CET records.
- For CET(4), fix the induction applications and complete the compile; a
  timeout is not a verification.
- For CET(2,3), fix the record/tuple destruct and re-check the prefix before
  claiming the tower.
- For ε1, correct the generalized rung statement/proof and then prove the
  full parametric FGH step relation in a closed theorem.
