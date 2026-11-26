# bbsearch provenance

Copies of the raw search output and analysis tools behind the
`BBSEARCH CAMPAIGN -- 2026-11-16` and `LOADER-STYLE ANALYSIS -- fw1_6 4-state
machine` sections of `../championsreal.txt`. The working copies live in
`/.tmp_bbsearch` at the repo root; these are the archival copies so the
provenance is not only in a scratch directory.

## Search runs

| file | what it is |
|---|---|
| `all.log` | run A: all 48 cores, `--cap 3000 --budget 3e6` (baseline sweep) |
| `ext.log`, `hard.log` | the extra-state and hard-budget runs that preceded the campaign |
| `campaign.sh` | the four parallel 3e9 searches: fw1_5 7/5, fw1_6 4/6, fw3_5 8/5, fwm21_5 10/5 |
| `fw1_5_s7.log` | 3e9 search, fw1_5 with 7 states / 5 symbols |
| `fw1_6_s4.log` | 3e9 search, fw1_6 with 4 states / 6 symbols (source of the analysed machine) |
| `fw3_5_s8.log` | 3e9 search, fw3_5 with 8 states / 5 symbols |
| `fwm21_5_s10.log` | 3e9 search, fwm21_5 with 10 states / 5 symbols (no landmark) |

The search binary is loader3229/bbsearch (`bbsearch.cpp` in the scratch
directory), built with
`g++ -O2 -std=c++11 -o bbsearch.exe bbsearch.cpp`.

## Analysis of the fw1_6 4-state machine

| file | what it is |
|---|---|
| `banalysis.cpp` | phase tracer: tape RLE dumps plus `MINLINE` per new leftmost cell |
| `bstart.cpp` | runs a machine from a bbsearch-style start configuration (`bstart MACHINE CONFIG maxSteps`) |
| `sweep.sh` | k sweep (2-run length 0..10) at the landmark start, 2e9 cap |
| `psweep.sh` | p sweep (5-run length 0..12) at the landmark start, 2e9 cap |
| `ksweep.log` | k sweep results: no halt for any k, head ends at the same cell |
| `psweep.log` | p sweep results: no halt for any p, head ends at the same cell |
| `phase.log` | 3e8-step trace of the blank-start run: 15,469 `MINLINE` events + the step-3e8 dump |
| `phasefit.js` | phase segmentation and slope fit over `phase.log` (`node phasefit.js phase.log`) |

Measured results and their interpretation are in `../championsreal.txt`.
Nothing here is a proof, and none of it is Rocq-verified.
