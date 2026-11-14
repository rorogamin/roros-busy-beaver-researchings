# CET research handoff — verification-first

## Scale correction — read this first

There are **2^64 = 18,446,744,073,709,551,616** labelled CET(4) tables
(`16^8 = 2^32` choices per agent, squared for two agents), about
`1.84 × 10^19`.  The number **15 is not the number of CET(4) holdouts in the
universe**.  It is only the number of lines still unresolved in one specific
54,828-line search-survivor file, `all_holdouts_cet4.txt`.

That file is a cutoff artifact, not an exhaustive classification of CET(4).
Statements such as “54,813 solved” always mean “54,813 of the 54,828 lines in
this one list,” never “54,813 of all CET(4) machines.”  When writing reports,
use that qualifier every time.

## Definitions for an AI starting from this text alone

Do not assume you will be in the originating directory, and do not pretend a
filename is a result.  These definitions make the brief usable without local
memory:

- **CET(n,k)**: two agents, `n` states each, `k` symbols, shared two-way
  tape, both agents start at 0 and 2, collision halts.
- **CET(4) holdout**: a line from a particular CET(4) search-survivor list
  that had not collided at that search's cutoff and had not yet been given a
  non-halting certificate.  “Holdout” is a search status, not a proof and not
  a total count of CET(4) machines.
- **The 15 holdouts mentioned here**: exactly the 15 table strings listed in
  the next subsection.  They are the unresolved lines of the 54,828-line
  list, not 15 machines out of the whole CET(4) universe.
- **Champion**: the largest verified halting collision step known for a
  domain.  A lower bound is not a maximum.
- **Local cycle certificate**: a transient plus an exact period of the two
  heads, states, and the complete tape window they read during the period,
  with no collision and with the outside of the window proved inert.
- **gem48**: the 48-state, 2-symbol blank-tape machine defined by the `trans`
  table in `rocq/gemini_epsilon1_tm_48s_v2_fix.v`.  It was presented by an
  earlier AI as an ε1-level machine using conditional worm-chain theorems.
  The audit `gem48_family_audit.md` found no chain witness, a 231-step worm
  collapse that violates the claimed inequality, and a growing quadratic
  bouncer instead of a descent.  It is not an accepted FGH machine.

### The 15 unresolved lines of this one list

If you do not receive `remaining_holdouts4.txt`, these are the complete
tables; indices are their positions in that file.

    1  1RB1RB_0LA1RB_1RB1RA_0RA1RC|0RC0LA_0LA1LB_1LA1RC_0LB0RD
    2  0LD0LA_0RB1LA_1RC1RD_1RB0LD|1RC1LC_0RA0RB_0RD0RC_0LC1RA
    3  1LC0LA_0LA0RD_1RD1LA_1LB0RB|0RC1RD_0RD1LB_0LA1RA_0RD1RB
    4  0LC1LB_1RC0RC_1LB0LB_0LC1LD|0RD1RD_1LC1RB_0RB0LC_0LB1RA
    5  1RC0LA_1RA1LB_0RC1LA_1LC1LA|0RD0LC_0LC1LB_0RB1LC_1RC0LC
    6  0LC0RD_0LA1RD_1RD1RA_0LB0RA|1LB1RA_0RA1LD_1RA1RA_0RD0LB
    7  0LC0RA_0LB1RC_1RA1LC_1LD0RC|0RD1RC_0RC1RB_0LA0LC_1RC1LC
    8  0RC1LA_0LB0LC_0LA0RC_0RD0RA|0RC0LA_1LA1RB_1LA1RB_0RA1LB
    9  1RB1LA_0LA0RB_0LB0RC_1RB0RD|0RC0RC_1LD1RD_0RD0RC_0LC1LD
    10 0LC0LD_0LA0LD_0RA1RB_0RA1LB|0RD0LD_0RC0LB_1LB1RC_1LA1LB
    11 0LB1RA_1RD1LB_1LB1LC_0LC0RD|0RB0RA_1RC1RD_0LC1RC_0LB0RD
    12 0LB0RA_1RA1LC_1LB1LA_1LC0LC|1RC0LA_1RB1RA_0RD1LB_0LC1RA
    13 1RD0RD_1LA1RC_0RC0LA_1LD0LB|1RD1LD_0RD0RD_1LB1RD_0LC1RC
    14 0LD0RB_0RD0RC_0RB1LA_0LB1LA|1LD1RA_1RA1LB_1RC1RA_0RA0LD
    15 0RA1LC_1RB1RB_0RC1LC_0RD1RD|1RC0LC_0RC0RB_0RD0LC_1LC1RD

Without the artifact bundle you can read these tables, but you cannot run the
independent checkers.  Ask for the bundle before claiming a verified result.

### Minimum artifact manifest

If the sender can provide only part of the bundle, these are the essential
items:

- this handoff;
- `all_holdouts_cet4.txt`;
- `solved_holdouts_combined3.txt`;
- `remaining_holdouts4.txt`;
- the scanner sources and their build/run instructions;
- `verify_all_champions.c`;
- `README.md` for the exact CET semantics and records;
- for period-9: `autonomous_20261112/PERIOD9_CLOSED.md` and
  `autonomous_20261112/period9_close_verify.py`;
- for FGH: the Rocq tree and `gem48_family_audit.md`.

## Mission

You are taking over the Catch-Em-Turing (CET) work in this artifact bundle. Your job is **not** to produce impressive-looking output. Your job is to leave every claim in one of these states:

1. **Exact finite certificate**, independently replayed;
2. **Exact halting run**, reproduced end to end;
3. **Rocq theorem**, with `Print Assumptions` closed and no axioms/admits;
4. **Explicitly unresolved**, with the failed attempts and the exact obstruction recorded.

“100% verified” means there is no claim that rests only on a simulation cutoff, a hash collision, a guessed invariant, an unreachable transition row, a conditional theorem, or a hand-wave. Negative results are valid deliverables. Do not upgrade a claim to satisfy a deadline.

This document is **portable**.  Do not assume the originating workstation,
absolute paths, or that the files are already mounted.  The CET artifact
bundle contains this handoff plus the files named below.  Set:

    BUNDLE_ROOT=/path/to/CET_ARTIFACT_BUNDLE
    CET_ROOT=$BUNDLE_ROOT/CET
    PERIOD9_DIR=$BUNDLE_ROOT/autonomous_20261112

and treat every unqualified CET filename below as relative to `CET_ROOT`.
The period-9 proof lives in `PERIOD9_DIR`.  If the bundle is absent, stop and
request it; do not invent results from filenames.

The packaged layout is:

    CET_ARTIFACT_BUNDLE/
      CET_AI_HANDOFF.md
      MANIFEST.md
      SHA256SUMS
      CET/                  (CET sources and data)
      autonomous_20261112/  (period-9 proof)
      rocq/                 (Rocq/FGH sources)
      verify.sh             (Rocq gate)

---

## 1. The CET model — use exactly this

CET(n) has two independent agents on one shared two-way infinite tape.

- Agent 1 starts at cell `0`.
- Agent 2 starts at cell `2`.
- Both start in state `A` (internal index 0).
- The tape starts all zero.
- At each step both agents read their current cell **before either writes**.
- Each writes its own symbol, moves one cell left/right, and changes its own state.
- If both write the same cell, the lower-numbered agent has priority.
- A run halts only when the agents occupy the same cell after a step.
- There is no separate individual HALT state.
- A table entry is `write + direction + next-state`, e.g. `0LA`.
- `---` is an undefined entry. Reaching it means the individual table is incomplete; in CET the normal convention is that this is a halting/undefined condition only if the model says so. Be explicit about which convention you use.
- CET(n,k) means two agents, `n` states each, `k` symbols.

A machine string is:

    Agent1Rows|Agent2Rows

with rows separated by `_`; each row has one 3-character entry per input
symbol. For example CET(4), 2 symbols:

    1LC0LC_1LA1RB_0RB1LC_0RA0RA|1RC0RA_1RA1RB_1LC0RD_0RA0RC

Before doing anything, read `README.md` in the bundle for the
authoritative current champion table and the full model statement.

---

## 2. Current verified baseline

These are the records to preserve; do not silently replace them.

| Domain | Record | Status |
|---|---:|---|
| CET(1) | `1` | exact |
| CET(2) | `97` | exact |
| CET(3) | the 3-round `1LB---_1LC1RB_0RB0LC \| 1RB0LB_0RC0LA_1LB1RC` formula | mathematical + Python verifier |
| CET(4) | `4,622,083,548` | verified lower bound |
| CET(2,3) | `1,528,952,999` | verified lower bound |

Relevant verified artifacts:

- `CET3_5e47.v` — Rocq/Lean-formalized older CET(3) record;
- `CET3_4e414.v` — older verified CET(3) record;
- `CET3_3round_10_10_10_13_analysis.md` — current CET(3) formula/proof;
- `NonHalting_CET3_0LB.v` — Rocq non-halting proof for a period-14 holdout;
- `verify_all_champions.c` — ground-truth collision verifier for the major records.

The CET(4) and CET(2,3) rows are **lower bounds**, not claimed maxima.
Never call a machine “the champion” if you only ran it under a cutoff.

---

## 3. CET(4) holdout state

Input list:

    all_holdouts_cet4.txt      54,828 candidate lines from ONE search

These are cutoff survivors from one CET(4) search, not the CET(4) universe and
not a mathematically defined set of “hard” machines.  Most are actually
periodic.  The 15 unresolved lines are a property of this list, not of CET(4).

Current classification:

- **53,073** with non-zero-displacement short translated local cycles:
  - `scan_period_small_all.c`
  - `solved_holdouts_small_all.txt`
- **44** more with larger non-zero-displacement cycles:
  - `scan_period_large.c`
  - `solved_holdouts_large.txt`
- **1,657** with zero-displacement fixed cycles:
  - `scan_fixed_all.c`
  - `solved_holdouts_fixed_all.txt`
- **39** more with larger fixed cycles:
  - `scan_fixed_huge.c`
  - `solved_holdouts_fixed_huge.txt`
- **54,813 / 54,828** union:
  - `solved_holdouts_combined3.txt`
- **15** remain in `remaining_holdouts4.txt`.

All 15 remaining were run for **10,000,000,000 steps** without halting:
`remaining15_10B.log`. They are **not proved non-halting**.

### Critical warning from the handoff author

Do not repeat the false-cycle mistake. A radius-16 hash detector found
apparent repeats for these 15, but extending the comparison window to radius
20 broke the equalities. Those were not cycles. A cycle claim is valid only
when:

1. the complete read window used by the whole cycle is included;
2. the transient is recorded;
3. positions and both states return exactly;
4. no collision occurs in the transient or period;
5. cells outside the window are proved inert (or are never read);
6. an independent replay reproduces the certificate.

For translated cycles, also prove the heads move by the same displacement and
that the tape outside the window cannot influence the future.

### Verification protocol for a local cycle

For a candidate table, produce a certificate with:

    index, table string, transient, period, displacement,
    head1/head2 positions at start, states, full window contents,
    maximum excursion, collision flag, frontier state

Then a checker must:

- replay the transient;
- verify the start key exactly;
- replay the period;
- verify the end key equals the start key (up to the recorded translation);
- scan all intermediate positions and ensure the recorded window covers them;
- ensure no collision;
- record whether any nonzero symbol exists outside the window in a direction
  the heads could later reach.

The existing scanners are fast screeners, not proof checkers. A hash is not a
certificate. Store exact keys for any final claim.

Do not repeat the earlier subset-index bug: when scanning `remaining_holdouts`,
the scanner's local line number is not the original index in
`all_holdouts_cet4.txt`. Map every result back to the original line before
merging.

---

## 4. Period-9 CET pair — closed, do not redo from scratch

The period-9 candidate

    A1 = 1LB---_1LC1RB_0RB0LC
    A2 = 1RB0LA_0RC0LA_1LB1RC

is **non-halting**.

The completed proof is:

- `PERIOD9_DIR/PERIOD9_CLOSED.md`
- `PERIOD9_DIR/period9_close_verify.py`

Key facts:

- Verified exit:
  - `P(70) = 2^72 - 74`
  - `t_exit = 2^72 + 599`
  - `pos1 = 69`, state B
  - `tape[-1..68] = 1`, `tape[-2] = 0`, `tape[69] = 0`
  - Agent 2 at `524,707,386,985,516,134,924`, phase 5.
- After 10 steps Agent 1 is at 59, state C.
- After 62 more steps it reaches `-1`, state B, with all cells in
  `[-20,68]` zero; the lone cell 69 is one and inert.
- One more step enters the exact period-254 fixed cycle at `-2`, state C.
- The cycle's complete excursion is `[-2,5]`.
- Agent 2 is a period-9 +1 glider, minimum position
  `524,707,386,985,516,134,922`, permanently outside Agent 1's window.
- Agent 1's halt row is unreachable.

Run:

    python "$PERIOD9_DIR/period9_close_verify.py"

Expected final line:

    RESULT: period-9 pair is non-halting; collision impossible.

This is a finite local proof, not Rocq. Do not “fix” it with the old W=69
wall-crossing argument; the exit tape has no wall of ones at 69, and the
wall argument was unnecessary.

---

## 5. FGH machines — strict status

The project rule is:

> when making an FGH-level machine, it must halt in the specified ordinal
> under `f_ordinal(n)` steps, correctly verified in Rocq with the rules.

This is a hard gate. A conditional theorem is not a machine result.

The bundle contains:

- `rocq/FGH_Eps2_Zeta0_Eta0.v` — definitions of `f_eps_k`, `f_zeta_k`,
  `f_eta0`, worm evaluation, and lower-bound lemmas;
- `rocq/gemini_epsilon1_tm_48s_v2_fix.v` — a 48-state gem48 table with
  conditional `worm_campaign_chain` theorems;
- `rocq/gemini_epsilon2_zeta0_tm.v` — conditional eps2/zeta0 versions.

These are **not** accepted FGH champion machines. `gem48_family_audit.md`
records that:

- no `worm_chain_fgh` inhabitant is constructed;
- the actual gem48 trajectory collapses a huge worm in 231 steps, violating
  the required runtime inequality;
- the run grows like a quadratic bouncer, not a descent;
- the gem48 table has no demonstrated halting run.

Do not register gem48 or any conditional table as an ε1/ζ0/η0 champion.
Do not relabel an old table. Do not use an assumption as a theorem.

A real FGH machine needs:

1. an explicit table;
2. an unconditional halting proof;
3. a well-founded descending measure;
4. a constructed campaign/chain witness;
5. a closed Rocq theorem tying exact machine steps to `f_ordinal(n)`;
6. no axioms, parameters, admits, or unreachable “conditional” escape.

The existing `./verify.sh` at the bundle root is the Rocq gate. It currently expects
**202 closed theorems** and `ALL CHECKS PASSED`. If you touch Rocq, run it and
preserve that standard. Never add `admit`, `Axiom`, or `Parameter` to make a
claim compile.

If you cannot build a genuine ε1/ζ0/η0 machine, write down the obstruction
precisely and leave the existing negative audit intact. That is better than a
false champion.

---

## 6. What to do, in priority order

### Priority 1 — audit the files just committed

The last commit added 160 CET files, including many search outputs. Build an
inventory:

- which scripts compile/run;
- which `.txt` files are raw search data, which are certificates, and which
  are merely exploratory logs;
- which claims are reproducible from a clean command;
- which are stale or superseded.

Write `CET_VERIFICATION_REPORT.md` with a table:

    file / claim / command / result / exact? / limitations

Do not assume that a file named `high`, `champ`, `pinned`, or `verified` is
actually verified.

### Priority 2 — resolve or precisely classify the final 15 holdouts

Starting from `remaining_holdouts4.txt`:

- Try exact fixed/translated cycles with a **larger complete window** and
  larger period, using exact state comparison and independent replay.
- If no cycle exists in a bounded search, record the bound and the heads'
  long-run range. Do not call it non-halting from a cutoff.
- If one halts, the result is a **new CET(4) champion candidate only if** the
  full run reaches the collision and beats `4,622,083,548`.
- If a candidate only produces neutral mutants at the same step count, it is
  not a record.

Every solved holdout should have a compact certificate file and a checker.
The goal is **not** to inflate the solved count with invalid radius-16
cycles.

### Priority 3 — re-verify the 54,813 certificates

The count is only useful if the certificates are sound.

- Sample or exhaustively replay all entries in `solved_holdouts_combined3.txt`.
- Check the window covers the maximum excursion, not just the final key.
- Check translated cycles have no nonzero material in the frontier they move
  into.
- Check fixed cycles do not later read a cell that changed outside the window.
- Produce a failure list with original indices. A certificate that fails is
  not a solved holdout.

### Priority 4 — champion verification and search

Re-run the known records with `verify_all_champions.c` before making any
comparison. For new searches:

- label every result as **exact halt**, **lower bound**, **cutoff survivor**,
  or **non-halting certificate**;
- do not use a hash collision as a cycle proof;
- do not use a finite cutoff as a halting proof;
- preserve the CET semantics above, especially lower-agent write priority and
  collision after the simultaneous move.

A one-entry mutation sweep of the CET(4) record found 56 neutral mutants at
the same `4,622,083,548` steps and no improvement. That is a bounded negative
result, not a proof that no better machine exists.

### Priority 5 — FGH machines only after the CET verification is clean

Do not touch the gem48 family with cosmetic changes. Either:

- construct an unconditional machine and Rocq proof satisfying the rule; or
- document the precise obstruction and stop.

The bundle already has the audit; preserve it.

---

## 7. Commands and files

Useful entry points:

    cd "$CET_ROOT"

    # current champion verification
    gcc -O3 -o verify_all_champions verify_all_champions.c
    ./verify_all_champions

    # holdout scanners (screeners, not proof checkers)
    # verify_all_champions is above; compile the four screeners first:
    gcc -O3 -o scan_period_small_all scan_period_small_all.c
    gcc -O3 -o scan_period_large scan_period_large.c
    gcc -O3 -o scan_fixed_all scan_fixed_all.c
    gcc -O3 -o scan_fixed_huge scan_fixed_huge.c
    ./scan_period_small_all
    ./scan_period_large
    ./scan_fixed_all
    ./scan_fixed_huge

    # period-9 closed proof
    python "$PERIOD9_DIR/period9_close_verify.py"

    # Rocq gate
    cd "$BUNDLE_ROOT"
    ./verify.sh

Important data:

    all_holdouts_cet4.txt
    solved_holdouts_combined3.txt
    remaining_holdouts4.txt
    remaining15_10B.log
    HOLDOUTS_SOLVED.md
    holdout_line0_certificate.md

Important records:

    CET3_3round_10_10_10_13_analysis.md
    CET3_5e47.v
    CET3_4e414.v
    NonHalting_CET3_0LB.v
    gem48_family_audit.md
    rocq/FGH_Eps2_Zeta0_Eta0.v

There are many exploratory files from several search campaigns. Do not delete
them just because they are untidy; first classify them in the inventory.
Do not commit generated `.exe` files; `.gitignore` already covers them.

---

## 8. Definition of done

A task is done only when:

- the table string is recorded verbatim;
- the exact simulator semantics are stated;
- a clean command reproduces the result;
- the result has an independent checker, not only the same script that found
  it;
- non-halting claims have complete local certificates, not just no halt under
  a cutoff;
- halting claims reach the actual collision and report the exact step;
- Rocq claims pass `./verify.sh` with 202 closed theorems and no forbidden
  vernacular;
- negative and unresolved results are written down with their bounds;
- `CET_VERIFICATION_REPORT.md` states exactly what is proved, what is only
  evidence, and what remains open.

If a claim cannot meet that standard, mark it **UNVERIFIED**. Do not smooth
over the gap.

---

## 9. Hard don'ts

- Don't call a cutoff survivor a non-halting machine.
- Don't call a hash repeat a cycle without exact replay.
- Don't use a window smaller than the cycle excursion.
- Don't ignore a nonzero cell outside a fixed-cycle window.
- Don't treat a neutral mutant as a new record.
- Don't call an unconditional conditional theorem a halting theorem.
- Don't add axioms/admits to close a Rocq goal.
- Don't relabel gem48 or any old table as ε1/ζ0/η0.
- Don't overwrite the verified champion rows without rerunning the verifier.
- Don't commit raw multi-hundred-megabyte search data without checking its
  purpose and size.

The useful output is a verified map of what is true, not a larger pile of
claims.
