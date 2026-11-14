# Gemini CET/FGH submission — verification audit

Date: 2026-11-12

Status: **REJECTED AS A VERIFIED RESULT**

The submitted files are preserved in `gemini_incoming/` for inspection. They are
not part of `CET_ARTIFACT_BUNDLE`.

## 1. CET(4) “31-round champion”

Claimed machine:

    1LB1RA_1RC0LD_1LA0LB_0RB0RA|1RB0LC_1LA0RC_1LD0RA_1RC1RA

Claim: halts after 31 tower rounds and beats `4,622,083,548`.

### Rocq result

`CET4_R31.v` **does not compile** with Rocq 9.1:

    File "CET4_R31.v", line 116, characters 56-58:
    Error: Syntax error: '|' or ']' expected (in [or_and_intropattern]).

Even if that syntax is repaired, the file contains only:

    Lemma no_collision_first_10 :
      forall t : N, (t < 10)%N -> ~ collides_at ag1 ag2 c0 t.

It contains no theorem of the form `halts_at_exact ... T`, no tower-round
theorem, and no computation of the actual halt step. “No collision in the first
10 steps” is not a 31-round halting proof.

### Independent replay

A direct two-agent simulator with the documented CET semantics was run for
20,000,000 raw steps from the blank tape. It did **not** collide. That is only a
cutoff observation, not a non-halting proof and not confirmation of the claimed
tower halt.

The Python helper `eval_exact_seq` returns an abstract event sequence:

    HALT 31
    hstp = 30
    seq = [30, 22, 28, 28, 30, 24, 28, 14, 16, 28, 24, 24, 8, 18, 12, 30,
           12, 14, 16, 28, 30, 26, 12, 14, 28, 14, 8, 26, 24, 22, 32]

`hstp = 30` is the local collision offset inside the final event, **not** the
total halting step. The evaluator fits formulas to a few sampled rungs and
iterates modular residues; it does not replay the whole machine, and the file
does not provide a Rocq proof of its extrapolation. Therefore it cannot
establish that this machine beats `4,622,083,548`.

Verdict: **UNVERIFIED**. Do not replace the verified CET(4) lower bound.

## 2. CET(2,3) “10-round champion”

Claimed machine:

    1LB2LB2RA_1RB1RA0LB|0RB2RB2LB_2LA1RB1LA

Claim: halts after 10 tower rounds and beats `1,528,952,999`.

### Rocq result

`CET23_R10.v` **does not compile** with Rocq 9.1:

    File "CET23_R10.v", line 106, characters 56-58:
    Error: Syntax error: '|' or ']' expected (in [or_and_intropattern]).

Even with the syntax repaired, it only states and proves
`no_collision_first_10`, exactly like the CET(4) scaffold. It does not prove the
10-round halt or a total step count.

### Independent replay

The same direct simulator ran 20,000,000 raw steps without collision. The
abstract Python helper returns:

    HALT 10
    hstp = 9
    seq = [12, 14, 12, 12, 14, 14, 14, 14, 14, 8]

Again, `hstp = 9` is a local final-event offset, not the total halting step. No
exact collision replay or Rocq theorem supports the claimed record.

Verdict: **UNVERIFIED**. Do not replace the verified CET(2,3) lower bound.

## 3. “Blank-tape ε1 machine”

`Eps1Complete.v` **does compile** with Rocq 9.1 (`rocq compile -Q . Top`), but
that is not the claimed result.

The file defines `btbl_eps1_clean` and proves exactly:

    Lemma eps1_clean_prologue :
      run btbl_eps1_clean 13 c0_eps1 =
      Some (mkConf (12 + ENTRY) [bl; bl; on; on] on
                   [bl; bl; on; bl; on]).

`Print Assumptions eps1_clean_prologue` is closed. That proves a 13-step
prologue reaches a configuration. It does **not** prove:

- that the machine halts at step 115 (or at any later step);
- that it produces 5 ones;
- that it implements `f_ε1` for general budget `a`;
- that it is a valid FGH-level machine under the project rule.

An independent Python replay of the prologue table in the submitted verifier
reached the ENTRY configuration and then halted at raw step **107** with 5 ones,
not step 115. That replay is not a Rocq theorem either, but it shows the
submitted prose and the submitted code are not even consistent about the step
count.

The file is therefore a finite prologue lemma, not an ε1 FGH machine.

## 4. Reproducibility problem

`verify_new_champions_and_eps1.py` hardcodes:

    /working_dir/c_b910ffe159ae7b24/...

and reads `mechs_cet4_hm.txt`, which is not present in the CET bundle. It cannot
run as delivered. The adapted local run used the actual bundle data and still
produced only the abstract evaluator results above.

## 5. Required standard

Under the project rule, an FGH-level claim needs an explicit table, an
unconditional halting proof, a well-founded descending measure, a constructed
campaign/chain witness, and a closed Rocq theorem tying exact machine steps to
`f_ordinal(n)`, with no axioms, parameters, admits, or conditional escape.

None of the three submitted files meets that standard.

## 6. Disposition

- Keep `CET4_R31.v`, `CET23_R10.v`, `Eps1Complete.v`, and the Python script in
  `gemini_incoming/` as unverified submissions.
- Do not merge them into `rocq/` or the verified artifact bundle.
- Do not update the CET records.
- If Gemini wants to continue, require a compiling Rocq theorem that explicitly
  states the total halt step and proves no earlier collision, plus a separate
  closed theorem for the FGH ordinal bound.
