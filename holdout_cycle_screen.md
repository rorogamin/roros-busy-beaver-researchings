# BB(2,5) formal 37: cycle screen

Source list: `bb2x5_holdouts37.txt`.

## 10⁹ screen

Command shape:

```bash
./cyc.exe 1000000000 1000000 "<spec>"
```

run in parallel over all 37 formal holdouts, with translated-configuration
snapshots every 10⁶ steps.

- machines: **37**
- completed: **37/37**
- cycles: **0**
- halts: **0**
- every log ends `NO_CYCLE t=1000000000 ...`

This is a finite screen only.  It rules out a translated cycle with a
checkpoint period dividing 10⁶ within the first 10⁹ steps; it does not prove
nonhalting and it does not find an invariant.

## 10¹⁰ extension (2026-11-07)

Driver: `cycle_screen.py` (new; resume-aware, one `cyc.exe` process per
machine, exact row-count validation).  The run resumed eight machines whose
10¹⁰ logs survived an interrupted first launch, then ran the remaining 29:

```bash
python cycle_screen.py --list bb2x5_holdouts37.txt \
  --cap 10000000000 --interval 10000000 --jobs 8 \
  --out cycle37_1e10 --resume
```

- machines: **37**
- completed: **37/37**
- cycles: **0**
- halts: **0**
- errors: **0**
- every log ends `NO_CYCLE t=10000000000 ...`
- wall time: 275.2 s with 8 workers; slowest single machine 73.4 s

This rules out a translated cycle whose checkpoint period divides 10⁷ within
the first 10¹⁰ steps.  It is still a finite screen, not a nonhalting proof;
the checkpoint-period restriction is part of the result.  Artifacts:
`cycle37_1e10/results.csv`, `logs/`, and `summary.txt`.

The target machine (`1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`) remains the one with a
concrete deep-shield reduction.  Machine 14
(`1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`) remains the next structural candidate,
with the raw bridge and `BadR`/`BadW` search recorded separately.
