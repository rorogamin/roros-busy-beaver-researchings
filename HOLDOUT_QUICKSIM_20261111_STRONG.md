# Strong-rule QuickSim screen — six main domains, 2026-11-11

## Scope

Same six domains as the first screen, with the same deterministic coverage:

| tag | list | tested | coverage |
|---|---|---:|---|
| `bb6` | BB(6) | 608 | all current small-list machines |
| `bb3x3` | BB(3,3) | 6 | all current small-list machines |
| `bb2x5` | BB(2,5) | 37 | all current small-list machines |
| `bb7` | BB(7) | 64 | first 64 of 17,823,260 |
| `bb2x6` | BB(2,6) | 64 | first 64 of 870,085 |
| `bb3x4` | BB(3,4) | 64 | first 64 of 11,362,197 |

**843 unique machines.** No full sweep of the three giant lists was attempted.

Tool: `sligocki/busy-beaver` commit
`62f9c36e70d15b266a33a05b29e9c6de3e934916`, via
`bbwork/vendor/quicksim-62f9c/`.

## Strong configuration

The completed pass used:

```text
-q --recursive
--exp-linear-rules --exp-meta-linear-rules
--max-loops=2000000
--max-steps-in-block=50000000
--max-steps-in-backsymbol=5000000
--max-block-size=250
--block-mult=4
--max-block-mult=5
--bf-loops=50000
--max-prover-configs=500000
--max-num-reps=100
```

with a 30-second process timeout and 32 workers.

A full-tape version (`--no-limited-rules`, 100M block steps, 10M backsymbol
steps, 1,000 max block size) was tested first. It was stopped after 320 BB(6)
machines: all 320 were `TIMEOUT` at proof level 0. The full-tape data is kept
in `strong_results.jsonl` but is not the reported strong pass.

## Results

| tag | tested | INF | UNDEF (halt) | TIMEOUT | ERROR |
|---|---:|---:|---:|---:|---:|
| `bb6` | 608 | 0 | 0 | 607 | 1 |
| `bb3x3` | 6 | 0 | 0 | 6 | 0 |
| `bb2x5` | 37 | 0 | 0 | 37 | 0 |
| `bb7` | 64 | 0 | 1 | 63 | 0 |
| `bb2x6` | 64 | 1 | 1 | 62 | 0 |
| `bb3x4` | 64 | 2 | 3 | 59 | 0 |
| **total** | **843** | **3** | **5** | **834** | **1** |

There were no `Turing Machine Halted` results and no `LOOPS` results in this
pass. The five `UNDEF` results are undefined-transition halting witnesses.

## Infinite proofs

All three reproduce on the older local QuickSim with `INF_PROOF_SYSTEM`.

- `bb3x4:41` — `1RB3RA2LA0LC_2RC0RC0RA---_2LA3LC3RA1LB`
- `bb3x4:51` — `1RB3LC2RA0LB_2LA---0LC2RB_2LA3RA0RA3LA`
- `bb2x6:28` — `1RB3RA1LA4LA5RB1RB_2LA2RB3LB2RB5RA---`
  - Level 3 proof; nonzeros `~10^^18.3`.

These are QuickSim proof-system results, not Rocq-checked proofs.

## Halting witnesses

### Directly verified

The C++ direct simulator in the existing `vendor/busy-beaver/cpp` source was
compiled locally and run against each machine. It reports an exact halt at the
same step count as QuickSim:

| id | exact steps | direct result |
|---|---:|---|
| `bb2x6:52` | 592,874,170 | halted |
| `bb3x4:12` | 1,906,082,321 | halted |
| `bb3x4:37` | 383,327,384 | halted |
| `bb3x4:58` | 52,108,275 | halted |

Specs:

- `bb2x6:52` — `1RB3LB3RB2LB5RA---_2LA4RB1LB0RB3RA3LA`
- `bb3x4:12` — `1RB---0LB0RC_1LC2RC2LC0LB_1LA2RC3RC0LC`
- `bb3x4:37` — `1RB1LC3LC2LB_2RC---3RB2LA_0LA2RA1RC3LC`
- `bb3x4:58` — `1RB1RC2RA2LC_2RC---2LB0RB_3LA3LB3LC3RA`

### BB(7) witness

- `bb7:24` — `1RB---_1RC0LF_0RD0LE_1RE0LG_1LB1RA_1LD0LC_0LG0LF`
- QuickSim reports `Turing Machine reached Undefined transition`.
- Step claim: `~10^1875.0`; nonzeros `~10^937.5`.
- The older local QuickSim also reports the undefined transition.
- Direct verification is infeasible at this step count; this is reported as a
  QuickSim witness, not an independently simulated halt.

## Error

One BB(6) machine (`bb6:101957`,
`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`) still exits with the newest
QuickSim `ConstantToExpression(None)` / `AttributeError` crash. It is not a
decision.

## Artifacts

Under `bbwork/vendor/holdouts_20261111/`:

- `strong2_run.log` — full strong-run log and summary.
- `strong2_results.jsonl` — 843 result rows.
- `decisive_full/` — exact-step QuickSim reruns without `--no-steps`.
- `direct_specs.txt`, `direct_sim.exe`, `direct_*.log` — independent direct
  simulation.
- `strong_results.jsonl` — stopped full-tape attempt (all 320 rows timeout).

No commit or push was made.
