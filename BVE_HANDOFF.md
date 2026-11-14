# BVE / ε₁ work handoff

Date: 2026-11-11.  This is a pause-point note; the ε₁ work is not a completed
FGH machine.

## 1. What is built

All paths are under `bbwork/tools/`.

| file | role | measured check |
|---|---|---|
| `eps1_bve.py` | binary Veblen term model, `fs`, `pred`, `model_fs`, `model_step` | `ALL OK` |
| `bve_tape.py` | single-field reversed-postfix codec | 107 terms OK |
| `bve_two_bank.py` | two-bank H/E codec, suffix access, `truncate_last` | 129 terms OK |
| `bve_cursor.py` | 18-state active-site core, 23-state H-end cursor | 207 terms OK in both modes |
| `bve_pred.py` | 24-state predecessor suffix-truncation arm with gap normaliser | 205 duplicate-tail terms OK |
| `bve_compose.py` | 46-state cursor + predecessor composition | 205 flag-1 / 204 flag-0; raw chain 24 OK |
| `bve_compose38.py` | observed-context quotient, cursor + predecessor | 38 states / 72 rows; 205/204/24 OK; 719 held-out tapes equal reference |
| `bve_fs_simple.py` | real fixed-case 5-tuple FS table, `omega[1] = 2` | 41 states, 40 rows, 28 -> 40 cells OK |
| `bve_fs.py` | general semantic FS arm and composed step driver | 200 limit terms, 200 steps, 43-case descent OK |

Existing documents:

* `BVE_TAPE_LAYOUT.md` — tape layout, cursor, predecessor, composition, and
  FS-arm status.
* `EPS1_67_PLAN.md` §11 — BVE prototype and current limits.

## 2. Tape representation

Four-cell tokens:

```text
1001 = 0
1011 = 1
1101 = phi_0
1111 = phi_1
```

Two banks:

```text
FIELD + H + DELIM + E + FIELD + [work] + FIELD + [index] + FIELD
FIELD = 0000, DELIM = 000
```

`H` is the right spine as fixed five-cell headers `(duplicate flag, op)`.
`E` contains the matching exponents in ordinary postfix, separated by `000`.
The last header and last exponent are suffixes, so a coefficient predecessor
is a suffix truncation.

## 3. Important current limitations

* The 38-state table is the **cursor + predecessor** quotient.  It is not a
  full ε₁ machine: its flag-0 route is still the unchanged/halt route, and
  `bve_fs.py` is semantic outside the predecessor route.
* The 46-state `bve_compose` table's raw flag-0 route still halts.  The
  `bve_fs.composed_step` driver expands flag-0 limits.
* The predecessor arm's 24th state is a gap normaliser: after a prior
  predecessor, it skips the whole H/E zero run and starts the E scan at the
  first 1.  The raw output can therefore feed a second predecessor without
  shifting cells or re-encoding the term.  The composed table is 46 states
  (the extra state is the normaliser).
* `bve_fs_simple.py` is a **fixed-case** real table, not a general FS table.
  It handles exactly the canonical `omega`, `n = 1` input and writes `1 + 1`.
* The general FS arm (`bve_fs.py`) is semantic: it decodes the tape, calls
  `B.model_fs`, and re-encodes.  It does not copy exponents or build towers on
  the tape and does not carry an index field.
* No blank-tape FGH machine, no full rewrite table, and no Rocq proof for the
  BVE work exists yet.
* The 38-state lowering is an observed-context result, not the general FS
  table: there is no exponent copy, tower construction, or index arm.  A full
  5-tuple ε₁ machine remains a new build; the 38-state count cannot be
  reported as a combined general-machine count.
* No `championsReal.txt` entry or champion claim has been changed.

## 4. Useful commands

```bash
cd bbwork
python tools/bve_two_bank.py
python tools/bve_cursor.py
python tools/bve_pred.py
python tools/bve_compose.py
python tools/bve_fs_simple.py
python tools/bve_fs.py
```

Expected current results:

```text
two-bank: 129 terms: ALL OK
cursor:   207 terms: OK (core and H-end entry)
predecessor: 205 duplicate-tail terms: OK
composition: flag1 205, flag0 204; raw chain 24: OK
38-state quotient: 38 states / 72 rows; 205/204/24 OK; 719 held-out equal
simple FS: 41 states, 40 rows; 28 -> 40 cells: OK
general FS: 200 limit terms; 200 composed steps: OK
descent:   43/43 terms match B.hardy (cap 40)
```

## 5. Full BVE ε₁ status

There is no full BVE ε₁ transition table yet.  The real 5-tuple objects are:

* 38 states — cursor + predecessor;
* 41 states — one fixed FS case, `omega[1] = 2`;
* no table for general flag-0 FS.

The general FS arm is still the semantic driver in `bve_fs.py`: it decodes the
term, calls `B.model_fs`, and re-encodes.  It passes 200 limit terms and 200
composed steps, and `bve_fs40.py` binds it to the 40-state predecessor, but
that is not a tape-level FS machine.  A full build still needs exponent copy,
tower construction, index transport, an FS/boot dispatcher, and a blank-tape
prologue.  No combined state count, FGH claim, or Rocq proof is available.

## 6. Rocq file verification

File:

```text
bbwork/bb-variants/CET/NonHalting_CET3_0LB.v
```

Command run:

```bash
cd bbwork/bb-variants/CET
rocq compile NonHalting_CET3_0LB.v
```

Result:

```text
ROCQ_COMPILE_EXIT: 0
Closed under the global context
```

The file's target theorem is:

```coq
Theorem target_never_halts :
  forall t : N,
    exists c : Config,
      run_N_opt t c0 = Some c /\ c.(pos1) <> c.(pos2).
```

This matches the header claim: from the blank tape with positions `0` and `2`,
both in `StA`, under the partial CET semantics, the run is defined for every
step count and never has a collision.  The agent tables in the file are the
advertised

```text
Agent 1: 0LB---_1LC1RB_0RB0LC
Agent 2: 1RB0RB_1LB1RC_1RA1LC
```

and `c0` has `pos1 = 0`, `pos2 = 2`, both `StA`, empty tape.

Additional checks:

* `Print Assumptions target_never_halts` reports
  `Closed under the global context`.
* `grep` for `Axiom`, `Admitted`, `Parameter`, and `admit` in the file returns
  no matches.
* The partial step matches the stated CET semantics: `None` on an undefined
  `---` transition, collision before a step, or collision after both moves.
  Agent 1 has priority in the shared write, matching the CET convention.

Scope of this verification: it verifies the Rocq development's own theorem and
its internal model, not an external wiki record or a claim that this machine is
a champion.  No source changes were made to the Rocq file.
