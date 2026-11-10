# Double Turing Machines (DTM)

Web simulator, C/Python search stack, and verified champions for **Double Turing Machines** (`DTM(n,m)`), **Multi-Rule DTMs** (`DTM(n,m,a)`), and **Asymmetric DTMs** (`DTM(n,m,a,b)`).

## Specification

A Double Turing Machine runs two (or `a`) independent transition tables over a **single shared state register** (initialized to state `A`) and a **single tape head** starting at cell `0` on a bi-infinite all-`0` tape:

- At step `t = 0, 1, 2, ...`, the active table is **`Rule[(t mod a) + 1]`** (for standard 2-rule `DTM(n,m)`, steps alternate strictly: Rule 1 on even steps `t = 0, 2, 4, ...`, Rule 2 on odd steps `t = 1, 3, 5, ...`).
- In **multi-rule `DTM(n, m, a)`**, rules rotate cyclically modulo `a`: `Rule 1 -> Rule 2 -> ... -> Rule a -> Rule 1 -> ...`.
- In **asymmetric `DTM(n, m, a, b)`**, Rule 1 has dimensions `(n, m)` and Rule 2 has dimensions `(a, b)`.
- **Halting & step counting (Radó `S` convention):** only one rule needs a halt transition (`---` or `<w><d>Z`/`H`). In `DTM(n, m, a, b)`, entering a state `>= rule.states` or reading a symbol `>= rule.symbols` for the currently active rule also halts immediately. The halting transition itself counts as `+1` final step (`DTM(1,2) = 6`), and `Sigma` (`score`) counts total nonzero cells on the final tape.
- **Format:** rules are separated by `|`, states within each rule by `_`, and transitions within each state are 3-character tokens `<write><L|R><next>`.

## Champions & Verified Results

| Class | Best Steps (`S`) | `Σ` (Nonzeros) | Status | Champion Spec |
|---|---|---|---|---|
| `DTM(1,2)` | **6** | **4** | **Exact** | `1RA1LA\|1LA1RZ` |
| `DTM(2,2)` | **40** | **5** | **Exact** | `1RA0LA_1LA0RB\|1LA1LB_1RZ1RB` *(tie: `1RB0LB_1LB0RA\|1RZ1RB_1LA1LB`)* |
| `DTM(3,2)` | **≥ 16,244** | 73 | Lower bound | `1RB1RA_1LC1RC_0RA0LB\|1RZ1RB_1LB0RA_1LC0RB` |
| `DTM(3,2)` (`Σ`) | 5,610 | **≥ 84** | Best `Σ` seen | `1RA1LB_1LA1RB_1LC0LA\|0RB1RC_1RB0LA_1RZ1LC` |
| `DTM(2,3)` | **≥ 65,794** | **≥ 355** | Lower bound | `1RA0RA2LB_2RA0LB0LA\|1LA2LB1RB_2RB1LA1RZ` |
| `DTM(1,3)` | **12** | **6** | **Exact** | `1RA2LA1RA\|1LA2RA1RZ` |
| `DTM(1,2,3)` | **18** | **5** | **Exact** | `1RA0LA\|0RA1RA\|1LA1RZ` |
| `DTM(2,2,3)` | **≥ 26,336** | **≥ 132** | Lower bound | `0RB0RA_1LB1RB\|0LB1RZ_1RB0LA\|1RA1LB_1RB0RA` |
| `DTM(2,2,3,2)` | ≥ 27 | 6 | Asymmetric showcase | `1RA0LA_1LA1RB\|1LA1RB_0RC0RA_1RC1RZ` *(halts via state `C` out of range for Rule 1)* |

Additional notable specimens:
- `DTM(2,3)` 4% TNF raw best (pre-mutation): `1RB1LA2RB_0RB2LA1RA|1RB0LB1LB_2LA1RZ0RA` (`13,698` steps, `score=81`), plus `1RA1RZ2RB_2RB0LA0LB|1LB0RA1RB_2LA0RB1RA` (`13,111` steps, `score=95`, `ones=94`).
- `DTM(3,2)` compact binary counter holdouts (unhalted at `50,000,000` steps with logarithmic tape span):
  - `1RB0LA_1RA0LA_0RC1LA|1RA0LC_1LC1RA_1RB1RZ` (`span = 28`, `[-2..25]`)
  - `1RA0LB_1LB1RA_1LA0LC|1LC1RB_1RZ0LC_0RA0LC` (`span = 25`, `[-1..23]`)
  - `1RA1RB_1RZ0LB_1RC0RC|1LB0RA_1LC0LA_0LB1RC` (`span = 44`, `[-40..3]`)

## Growth Rate Analysis

How fast does `DTM(n, m)` / `DTM(n, m, a)` grow?

1. **Exact embedding sandwich theorem:** For every `n >= 1, m >= 2, a >= 1`,
   $$\mathrm{BB}(n, m) \le \mathrm{DTM}(n, m, a) \le \mathrm{BB}(a \cdot n, m)$$
   - *Lower bound:* duplicating any ordinary `(n, m)` Turing machine across all `a` rules yields a `DTM(n, m, a)` machine with identical trajectory, runtime, and score.
   - *Upper bound:* encoding `(rule_idx, state)` into a single state register `0 .. a*n - 1` embeds any equal-dimension `DTM(n, m, a)` into an ordinary `(a*n, m)` Turing machine (`DTM.to_equivalent_standard_tm()`). Similarly, `DTM(n, m, a, b) <= BB(n + a, max(m, b))`.
2. **Parity bottleneck:** Because Rule `r` may only transition into Rule `(r + 1) mod a`, DTMs occupy the **strictly `a`-partite (clocked)** subclass of `(a*n, m)` TMs:
   - At `(1, 2)`, the ordinary `BB(2) = 6` champion `1RB1LB_1LA1RZ` is already bipartite, so **`DTM(1,2) = 6 = BB(2)`** saturates the upper bound.
   - At `(2, 2)`, parity restricts capacity below `BB(4) = 107`, yielding **`DTM(2,2) = 40`**.
   - At `(1, 3)` (`<= BB(2,3) = 38`), **`DTM(1,3) = 12`**; at `(1,2,3)` (`<= BB(3) = 21`), **`DTM(1,2,3) = 18`**.
3. **Multiplicative state amplification (`a * n`):** Asymptotically `DTM(n, m, a)` is uncomputable and tracks the Busy Beaver hierarchy with an `a`-fold multiplier on state count—Jumping from `BB(3) = 21` to `>= 16,244` (plus logarithmic `2^k` counters) at `DTM(3,2)`, and from `BB(2,3) = 38` to `>= 65,794` at `DTM(2,3)`.

## Verification Details

- **`DTM(1,2) = 6`**: Unpruned TNF (`verify_small_dtm.c`, `cap=50`): `23` nodes, `10` halted, `13` timeouts, `0.000s`.
- **`DTM(2,2) = 40`**: Every `DTM(2,2)` embeds in `BB(4) = 107`; unpruned TNF (`cap=120 > 107`) checked all `94,101` nodes (`32,043` halted, `62,058` timeouts) in `0.040s`.
- **`DTM(1,3) = 12`**: Every `DTM(1,3)` embeds in `BB(2,3) = 38`; unpruned TNF (`cap=500 > 38`) checked all `241` nodes (`65` halted, `176` timeouts) in `0.000s`; open machines (e.g. `1RA0LA---|1LA0RA---`) exhibit periodic quadratic bouncer growth (`span = 632` at `100,000` steps).
- **`DTM(1,2,3) = 18`**: Every `DTM(1,2,3)` embeds in `BB(3) = 21`; unpruned TNF (`cap=100 > 21`) checked `223` nodes (`121` halted) in `0.000s`.
- **`DTM(3,2) >= 16,244`**: 4% filtered TNF sweep (`bouncer_tnf_dtm.c --stride 25 --tier3 40000`, `114.7M` nodes in `83.49s`), plus zero additional halts up to `2M` steps across `8,192` saved compact holdouts.
- **`DTM(2,3) >= 65,794`**: 4% filtered TNF sweep (`bouncer_tnf_dtm.c --stride 25 --tier3 40000`, `109.4M` nodes in `100.89s`) found `13,698`, `13,111`, and `6,830`; 1-mutant climb from `6,830` discovered `65,794` (`1RA0RA2LB_2RA0LB0LA|1LA2LB1RB_2RB1LA1RZ`). Zero halts up to `5M` steps across `8,192` compact holdouts.
- **`DTM(2,2,3) >= 26,336`**: 100% filtered TNF sweep (`bouncer_tnf_dtm.c --n 2 --m 2 --rules 3 --stride 1 --tier3 40000`, `180,696,549` nodes in `52.51s`, `445,840` unhalted holdouts).
- Cross-engine equivalence verified across Python (`dtm.py`), Native C (`dtm_fast.exe`), JS (`simulator.js`), and the HTTP API (`server.py`).

## Usage

### 1. Build Native C Accelerator (Optional, Recommended)

```powershell
gcc -O3 -fopenmp -Wall -o dtm_fast.exe dtm_fast.c
gcc -O3 -Wall -o verify_small_dtm.exe verify_small_dtm.c
gcc -O3 -fopenmp -Wall -o bouncer_tnf_dtm.exe bouncer_tnf_dtm.c
gcc -O3 -fopenmp -Wall -o break_holdouts.exe break_holdouts.c
```

### 2. Run Web Simulator & Server

```powershell
py -3.14 server.py --port 8765
```

Endpoints exposed by `server.py`:
- `GET /` — DTM Studio interactive web UI (rule editor, single-step/play, zooming space-time diagram, equivalent standard-TM export, live C-accelerated search/mutation hunter)
- `GET /api/health` — Engine status (`native_c` vs pure Python fallback)
- `GET /api/champions` — Verified champions and UI presets (`champions.json`)
- `POST /api/parse` — Normalize spec, extract signature, and compute `(k*n, m)` standard TM embedding
- `POST /api/simulate` — Simulate up to millions of steps with Brent cycler + translated-cycler detection
- `POST /api/search` — Random search or neighborhood mutation hunt (`--search` / `--mutate`)

### 3. Direct C Search & Verification Examples

```powershell
# Simulate a spec
./dtm_fast.exe --sim "1RA0RA2LB_2RA0LB0LA|1LA2LB1RB_2RB1LA1RZ" --cap 200000

# Reproduce exact small-class proofs
./verify_small_dtm.exe

# Filtered TNF sweep for DTM(3,2)
./bouncer_tnf_dtm.exe --n 3 --m 2 --rules 2 --split 4 --tier1 400 --tier2 6000 --tier3 40000 --threads 16 --stride 25
```

## Files

- `dtm.py` — Pure-Python reference engine (`DTM`, `DTMRule`, `Transition`) and standard-TM embedding.
- `dtm_fast.c` — Fast C11 simulator (`--sim`), random hunter (`--search`), and local mutator (`--mutate`).
- `server.py` — HTTP API and static server for the web studio.
- `index.html`, `style.css`, `simulator.js`, `spacetime.js`, `app.js` — Client web simulator and space-time viewer.
- `champions.json` — Verified champions, exact bounds, and UI presets.
- `verify_small_dtm.c` — Unpruned TNF verifier for exact small classes.
- `bouncer_tnf_dtm.c` — Multi-threaded TNF hunter with Brent, translated-cycler, and periodic-bouncer detectors.
- `break_holdouts.c` — Batch holdout evaluator and 1-mutant sweeper.
