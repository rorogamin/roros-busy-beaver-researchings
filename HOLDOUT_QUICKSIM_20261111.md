# QuickSim holdout screen — 2026-11-11

## Tool

- Source: `sligocki/busy-beaver` at
  `62f9c36e70d15b266a33a05b29e9c6de3e934916` (2026-11-11 17:02:44 -0500),
  "Reduce ExpInt max recursive depth to 500 ... New: ExpressionTooComplex".
- Fresh clone: `bbwork/vendor/quicksim-62f9c/`.
- Interpreter: `bbwork/.venv/Scripts/python.exe` (Python 3.14.7).
- The older `bbwork/vendor/busy-beaver` checkout was not used for the main run.
  It contains a pre-existing local `Code/Exp_Int.py` modification and could not
  fast-forward.

## Lists and coverage

Source page: https://wiki.bbchallenge.org/wiki/Holdouts_lists

| tag | source file | list size | tested | kind |
|---|---|---:|---:|---|
| `bb6` | `BB6_holdouts_608.txt` | 608 | 608 | exhaustive |
| `bb3x3` | `3x3_holdout_6.txt` | 6 | 6 | exhaustive |
| `bb2x5` | `BB2x5_Rocq_holdouts_37.txt` | 37 | 37 | exhaustive |
| `bb7` | `7x2_holdouts_17823260.zip` | 17,823,260 | 64 | first-64 sample |
| `bb2x6` | `2x6_holdouts_870085.zip` | 870,085 | 64 | first-64 sample |
| `bb3x4` | `3x4_holdouts_11362197.zip` | 11,362,197 | 64 | first-64 sample |

All 651 current small-list machines and 192 giant-list samples were tested:
**843 unique specifications, no duplicates**.

The downloaded archive labels are 17,823,260 for BB(7) and 870,085 for
BB(2,6); the wiki table also displays smaller counts (12,765,773 and 389,503).
Those may be different list revisions. The files used here are the ones
actually downloaded from the holdout page; no exhaustive claim is made for the
giant lists.

The giant-list samples are the first 64 non-comment records in each file. They
are deterministic but not statistically representative.

## Flags

The screen command used:

```text
Quick_Sim.py -q --no-steps --recursive \
  --exp-linear-rules --exp-meta-linear-rules \
  --max-loops=200000 \
  --max-steps-in-block=10000000 \
  --max-steps-in-backsymbol=1000000 \
  --max-block-size=100 --block-mult=3 <spec>
```

and a 20-second subprocess timeout per machine.

Important flag behavior from the current `--help` (saved at
`vendor/holdouts_20261111/quicksim_help.txt`):

- `-q` / `--quiet`: brief output.
- `--no-steps`: skip base-step counting, which is expensive with recursive
  proofs. Used for the screen; decisive rows were rerun without it.
- `-r` / `--recursive`: allow meta/recursive rules.
- `--exp-linear-rules`: enable experimental iterated/exponential-linear rules.
- `--exp-meta-linear-rules`: allow iterated rules inside meta rules.
- `--no-limited-rules`: force full-tape rules (not used in the screen).
- `--max-loops`: cap on macro-loop applications; reaching it yields `LOOPS`,
  not a proof.
- `--max-steps-in-block`, `--max-steps-in-backsymbol`: limits for proving
  block/backsymbol rules.
- `--max-block-size`, `--block-mult`: block-finder compression limits.
- `--bf-loops`: number of steps given to the Block Finder.
- `--max-prover-configs`, `--max-num-reps`: prover-memory and general-rule
  repetition limits.
- `--freeze-prover`: stop proving new rules after the first print.
- `--max-print-chars`, `--print-full-result`, `--print-time`,
  `--print-macro-ttable`, `--latex`, `--html-format`: output formatting.
- `--manual`, `-n`/`--block-size`, `-b`/`--no-backsymbol`,
  `-p`/`--no-prover`, `--full-reps`: simulator/manual/interaction controls.

## Results

| tag | tested | HALT | UNDEF (halt) | INF proof | LOOPS | TIMEOUT | ERROR |
|---|---:|---:|---:|---:|---:|---:|---:|
| `bb6` | 608 | 0 | 0 | 0 | 138 | 436 | 34 |
| `bb3x3` | 6 | 0 | 0 | 0 | 3 | 3 | 0 |
| `bb2x5` | 37 | 0 | 0 | 0 | 8 | 29 | 0 |
| `bb7` | 64 | 0 | 0 | 0 | 21 | 43 | 0 |
| `bb2x6` | 64 | 0 | 0 | 0 | 34 | 30 | 0 |
| `bb3x4` | 64 | 0 | 1 | 2 | 30 | 31 | 0 |
| **total** | **843** | **0** | **1** | **2** | **234** | **572** | **34** |

`LOOPS`, `TIMEOUT`, and `ERROR` are unresolved outcomes, not proofs of
non-halting. `UNDEF` is a halting witness because a standard Turing machine
halts when it reaches an undefined transition.

## Decisive BB(3,4) results

All three are in the first 64 records of the downloaded BB(3,4) list.

### Halting (undefined transition)

- ID: `bb3x4:58`
- Spec: `1RB1RC2RA2LC_2RC---2LB0RB_3LA3LB3LC3RA`
- QuickSim: `Turing Machine reached Undefined transition`, state 1, symbol 1,
  `Steps: 52_108_275`, nonzeros 45, span 48.
- Direct verification with the local `bb.py` simulator: halted, score 45,
  45 tape cells, after 52,108,274 executed transitions. The difference is the
  final undefined-transition step counted by QuickSim.

### Proven infinite

- ID: `bb3x4:41`
- Spec: `1RB3RA2LA0LC_2RC0RC0RA---_2LA3LC3RA1LB`
- QuickSim: `Turing Machine proven Infinite`, `Reason: INF_PROOF_SYSTEM`,
  1 Level-1 rule, 1,091 nonzeros.
- The older local QuickSim also reports `INF_PROOF_SYSTEM`.

- ID: `bb3x4:51`
- Spec: `1RB3LC2RA0LB_2LA---0LC2RB_2LA3RA0RA3LA`
- QuickSim: `Turing Machine proven Infinite`, `Reason: INF_PROOF_SYSTEM`,
  1 Level-1 rule, 1,378 nonzeros.
- The older local QuickSim also reports `INF_PROOF_SYSTEM`.

These are QuickSim proof-system results, not independently checked Rocq proofs.

## Newest-tool crash

34 BB(6) rows exited with code 1 and are recorded as `ERROR`. A representative
(`bb6:34042`, spec `1RB1LF_1LC0RD_---1LD_1RB1RE_1LA0LB_0LA0LE`) ends with:

```text
File ".../Code/Macro/Proof_System.py", line 1228, in prove_rule
  num_steps = ConstantToExpression(num_steps)
File ".../Code/Algebraic_Expression.py", line 195, in __init__
  self.is_const = len(self.terms) == 0 and is_const(self.const)
File ".../Code/NatExpr.py", line 15, in is_const
  return value.is_const
AttributeError: 'NoneType' object has no attribute 'is_const'
```

`num_steps` is `None` at that point. The older local QuickSim returns
`Maximum number of loops (200000) reached` on this representative, not a proof.
No result from the 34 error rows is counted as decisive.

## Limits

- This is a 20-second / 200,000-loop screen, not an exhaustive proof search.
- The three giant lists were only sampled; no claim of full coverage is made.
- `LOOPS` and `TIMEOUT` rows remain undecided and should not be presented as
  non-halting proofs.
- No exact step formulas were retained for the screen (`--no-steps`), except
  where decisive rows were rerun.
- No commit or push was made.

## Artifacts

Under `bbwork/vendor/holdouts_20261111/`:

- `jobs.tsv` — 843 `tag`, `id`, `spec` rows.
- `results.jsonl` — one JSON object per tested machine.
- `run.log` — full screen log and summary.
- `quicksim_help.txt` — current `--help`.
- `undef_full.log`, `undef_full_old.log` — exact halting result on new/old
  QuickSim.
- `error34042.log` — full newest-tool traceback.
