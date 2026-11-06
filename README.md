# bbwork — a Busy Beaver holdout excursion

Autonomous session work on the current BB holdout lists. Everything here is
reproducible from the scripts in this directory; the machine lists are saved
verbatim so later work starts from the same inputs.

## Inputs (newest lists at the time of the run, 2026-11-05)

| Domain | File | Source | Size |
|---|---|---|---|
| BB(6) | `BB6_holdouts_608.txt` | BusyBeaverWiki, @mxdys, 30 Oct 2026 | 608 machines (up to equivalence), 608 unique specs, IDs 279–181655 |
| BB(3,3) | `3x3_holdout_6.txt` | BusyBeaverWiki holdout file | 6 machines (2 documented equivalence pairs, 4 effective) |
| BB(2,5) | `h25_37.txt` (from `bb2x5_holdouts37.txt`) | user-provided informal list, matches the wiki's 37 informal holdouts (9 Oct 2026) | 37 machines |
| BB(2,5) | `BB2x5_Rocq_holdouts_60.txt` | @mxdys, 8 Sep 2026 | 60 formal holdouts |

The BB(6) file is in `<id> <standard-spec>` format; `bb.load_list` strips
whitespace only, so scripts that read it should split the ID off first.

## Tooling

* `bb.py` — standard-format parser/printer (`_`-separated states, 3-char
  tokens `<write><L|R><next>`, `---`/`Z` halt), a reference simulator,
  configuration normalization (translation-invariant), and the symmetry
  transform used for the BB(3,3) merge check.
* `sim.c` / `sim.exe` — fast simulator: batch mode with step caps, RLE tape
  dump, incremental score, tape doubling. Verified against a known BB(3,3)
  halter (`1RB1LA2LA_1LB1RC1RZ_1LA2RC1LC`, S = 15,725,661, Σ = 4098;
  our executed-step count is S−1 because the halting attempt is the last
  counted step, matching the convention used by the wiki).
* `reach.py` — reachable `(state, symbol)` audit.
* `iso.py` — machine isomorphism under state permutation, symbol permutation,
  and mirroring.
* `merge.py` — the documented 153/758 merge check.
* `mergefind.c` — translation-normalized configuration hash search between two
  machines (with a skip window so the trivial shared prefix is not reported).
* `factory.py` — random-machine specimen hunt.
* `run_decide.sh`, `run_decide2.sh`, `qsim.sh` — wrappers for the
  [sligocki/busy-beaver](https://github.com/sligocki/busy-beaver) decider
  framework (`Enumerate.py`, `Quick_Sim.py`) used from a local venv
  (`vendor/` and `.venv/` are not part of the work product).

## Results

### 1. BB(3,3): the 153/758 equivalence, independently checked

The six current holdouts are Bigfoot (`1RB2RA1LC_2LC1RB2RB_---2LA1LA`), 153,
758, 531, 532, and 397. `iso.py` finds an exact machine isomorphism

```
153 -> 758 : state permutation (2,0,1)  = A->C->B->A
             symbol permutation (0,2,1) = 1<->2
             mirror = True
```

and `merge.py` confirms the documented configuration merge:

* 153 after **1,790,901** steps: state 0, head 5, 343 cells, score 343.
* 758 after **1,841,608** steps: state 2, head 12, 343 cells, score 343.
* Applying A→C→B→A, 1↔2, L↔R to 153's configuration gives a tape of
  normalized length **681** with head offset **170**, identical to 758's
  normalized configuration (head offset 170). Match: yes.

So one of the two documented equivalence pairs is now verified from the
standard-format strings alone (isomorphism + explicit merge point).

531/532 are **not** isomorphic (`iso.py`), and both machines do read the cell
where they differ — (C,1). `mergefind.exe` finds a transient configuration
match at 531@29,156 / 532@20,000 (verified exact in Python: state 1, head −88,
157 cells, normalized length 157, head offset 47), but the machines then read
(C,1) and **diverge 2 steps later**. No stable remerge appears within
2,000,000 steps, and 397 vs 531 shows no merge within 2M at all. So a simple
trajectory merge does **not** explain the documented 531≡532 equivalence; if
it holds it must be at the level of a shared rule system (both reduce to the
Wily Coyote rules), not identical runs. We did not verify it.

### 2. Decider sweeps: no new solves

The sligocki/busy-beaver decider stack was run with the heavy parameters from
the wiki's own recipe (`--exp-linear-rules`, `--block-mult 3`,
`--max-block-size 100`, recursive rules):

* BB(3,3), all 6 machines, 110 s each, `--max-loops 20,000,000`: **6/6
  unknown**.
* BB(2,5), all 37 machines, first pass 45 s each (`--max-loops 2,000,000`):
  **37/37 unknown**.
* BB(2,5), second pass 240 s each (`--max-loops 20,000,000`): **37/37
  unknown**.

Logs are in `logs*/` (not committed). This is expected — these lists are the
hardened residue of years of decider work — but it establishes that no
easy solve was left in the current newest lists for this particular stack.

### 3. The two "moderate rigor" halting claims

The wiki lists two BB(2,5) machines recently solved with AI assistance and
formalised in Lean but *not independently verified*:

* `1RB4RA1LA4RB2LA_2LB3LA1RB2RA---` (claimed ≈5.6×10^53 steps),
* `1RB3RB3LA4LA2RB_2LB3RA---1RA1LA` (claimed ≈7.3×10^28 steps).

`Quick_Sim.py -r --exp-linear-rules --max-loops=500000` ran both without
halting and proved no general rules ("General rules proven: 0"). The runs are
not a refutation — the longitudinal prover did not engage, and the macro
counter is far from the claimed halting scale — but the claims were **not
independently reproduced** in this session. Reproducing them needs a bespoke
longitudinal analysis, which is the logical next step.

### 4. Deep direct simulation

The two cleanest-looking BB(2,5) holdouts (list indices 3 and 4,
`1RB3LA1LA1RA3RA_2LB2RA---4RB1LB` and `1RB3LA1LA1RA1RA_2LB2RA---4RB1LB`)
were simulated to **10¹⁰ steps** each. Neither halted. Both settle into a
clean two-block tape, locally `1… <1> 3…` (scores 71,186 and 85,815), i.e.
counter-like behaviour rather than chaos — consistent with the "bouncer"
diagnosis and with why CTL/Quick_Sim do not close them.

### 5. Machine factory: a null result, recorded

40,000 random 2×5 machines at cap 10⁶: 8,624 halted, but the longest halting
run found was **48 steps** (score 7). Random tables in this space are
dominated by immediate halts; the interesting machines are structured, not
sampled. The specimens and TSV are in `specimens/` as a record of the negative
result. It is not a useful search method as written.

## Honest verdict

**No new holdout was decided.** All six BB(3,3) machines and all 37 BB(2,5)
informal holdouts survived the heavy decider sweeps; the deep runs and the
longitudinal attempt did not close the two claimed halting machines. The
current lists are genuinely cryptid-hard (Collatz-like), and nothing in this
session changes that.

What the session did produce, and what is checkable:

1. An independent verification of the **153 ≡ 758** BB(3,3) equivalence pair
   (exact isomorphism + explicit 1,790,901/1,841,608-step merge).
2. A failed reproduction of the 531/532 equivalence: the machines are not
   isomorphic, their only configuration match within 2×10⁶ steps is transient
   (they read (C,1) and diverge 2 steps later), and 397 does not merge with
   531 either. Their documented equivalence must be a rule-system equivalence,
   not a trajectory merge.
3. A calibrated fast simulator and tooling that reproduces a known halter's
   exact score and step count.
4. Negative evidence: heavy deciders, deep simulation, and random sampling all
   fail to move the newest lists.

## Reproduce

```sh
py -3.14 iso.py                 # 153/758 isomorphism, 531/532 not isomorphic
py -3.14 merge.py               # explicit 153/758 merge at the documented steps
py -3.14 reach.py               # reachable-pair audit of the six 3x3 holdouts
gcc -O3 -march=native -o sim.exe sim.c
./sim.exe -c 10000000 -f h25_37.txt -R -r 40
```

Deciders (requires the vendored framework and its venv):

```sh
py -3.14 -m venv .venv
./.venv/Scripts/python.exe -m pip install -r vendor/busy-beaver/requirements.txt
./run_decide2.sh runs25/h00     # one machine, heavy parameters
```
