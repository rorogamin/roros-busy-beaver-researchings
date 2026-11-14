# New CET(3) Champions, Rocq 9.1 Proof, and `residue_s20.txt` Holdout Analysis

## 1. Formally Verified 3-Round CET(3) Champion (`CET3_3round_champ.v`)

- **Machine**: `0LB---_1LC1RB_0RB0LC | 1RC1LC_1RA0RA_1LB0LB`
- **Rocq 9.1 Verification**: [`CET3_3round_champ.v`](./CET3_3round_champ.v) (2,141 lines) compiles cleanly under `rocq compile CET3_3round_champ.v` in `12.49s` with `814.7 MB` peak job memory (`Closed under the global context`, zero axioms and zero admits).
- **Main Theorem (`cet3_3round_champ_halts_exact`)**:
  For **every** transition placed in the unreachable `(StA, true)` (`---`) slot of Agent 1, the two agents starting at `(pos1 = 0, state1 = StA)` and `(pos2 = 2, state2 = StA)` on the all-blank tape execute 3 full binary-counter-vs-glider rounds with gap sequence `[10, 10, 8]` and halt by exact first head collision at step:
  $$T_{\text{halt}} = 70411 + 2^{4697} + 15 K_2 + 2^{m_3 + 2} + 15 K_3$$
  where:
  $$K_2 = \frac{2^{4697} - 242}{210} \equiv 3 \pmod 4, \qquad m_3 = 4712 + 15 K_2, \qquad K_3 = \frac{2^{m_3 + 2} - 128}{210} \equiv 0 \pmod 4.$$
- **Verified Modular Structure (`K2_arithmetic`, `K3_arithmetic`, `pow2_4697_mod840`)**:
  - Round 1 reaches `state_70429` at $t_1 = 70,429$ with `pos1 = 4657`, `pos2 = 4697` ($L_2 = 4699$).
  - Since $2^{4697} \equiv 32 \pmod{840}$, Round 2 decouples for $n_{\text{cyc2}} = 14(K_2 + 1)$ glider cycles ($P=15, D=1, M=14$), chases for $15 K_2$ steps to reach bounce gap $G_2 = 10$, and executes the 45-step bounce (`bounce_G10`).
  - Writing $K_2 = 4 q_2 - 1$ ($q_2 \ge 1$) yields $m_3 + 2 = 12(391 + 5 q_2) + 7$, so $2^{m_3 + 2} \equiv 2^7 = 128 \pmod{840}$ (`pow2_12k_plus_7_mod840`).
  - Thus Round 3 lands on $G_3 = 8$, terminating in the 7-step collision (`suffix_7`).
  - **Magnitude**: $\log_{10}(m_3) \approx 1412.7918$, and $\log_{10}(\log_{10}(T_{\text{halt}})) \approx 1412.2704$, i.e. $T_{\text{halt}} \approx 10^{10^{1412.2704}}$ steps.

---

## 2. Larger Multi-Round CET(3) Champion (`1LB---_1LC1RB_0RB0LC | 1LB0RC_1RA0LC_1RB1RA`)

- **Machine**: `1LB---_1LC1RB_0RB0LC | 1LB0RC_1RA0LC_1RB1RA` (completed as `1LB0LA_1LC1RB_0RB0LC | 1LB0RC_1RA0LC_1RB1RA` in [`mechs_cet3_exh.txt`](./mechs_cet3_exh.txt))
- **Glider & Boundary Parameters**: Period $P = 16$, drift $D = 4$, modulus $M = 12$, minimal gap $mg = 8$, Round 1 exit gap $G_1 = 18$, $L_2 \approx 1.78957 \times 10^8$. Agent 1 with `1LB---` executes the first 100,000 steps of Round 1 without hitting `---` or halting early.
- **Tower Evaluation**:
  - Round 2 exponent alone reaches $\log_{10}(2^{178956976}) \approx 5.3871 \times 10^7$, so Round 3 already exceeds $10^{10^{5.387 \times 10^7}}$ steps.
  - Modular tower tracing continues cleanly past Round 3 to halting: [`true_exact_eval.py`](./true_exact_eval.py) evaluates `status=HALT` in 6 rounds (`[18, 8, 14, 14, 10, 12]`, halting at step 15 of Round 6 for `L2=178956976`), while [`eval_towers.py`](./eval_towers.py) / [`verify_all3_champions.py`](./verify_all3_champions.py) reports `status=HALT` in 7 rounds (`[18, 8, 14, 14, 10, 18, 12]` for `L2=178956975`). In either case, total halting time is a multi-level exponential power tower far beyond $\approx 10^{10^{5.387 \times 10^7}}$.

---

## 3. Analysis of the 17,843 Holdouts in `s18/residue_s20.txt`

- **Bounded Simulation Check (`solve_true_cet3.exe` up to $10^6$ steps)**:
  Running [`solve_true_cet3.exe`](./s18/solve_true_cet3.exe) on [`residue_s20.txt`](./s18/residue_s20.txt) (`17,843` machines, all contained in `s18`) gives:
  - `HALT`: `0`
  - `UNDEF`: `0`
  - `OOB (> +-524288 cells)`: `0`
  - `BOUNDED (span <= 300)`: `774`
  - `REMAINING (expanding)`: `17,069`
- **Structural Breakdown**:
  - `4,715` unique Agent 1 tables and `2,979` unique Agent 2 tables.
  - `1,153` unique Agent 2 rightward solo gliders and `1,529` unique Agent 1 leftward solo gliders.
  - `528` holdouts use known CET(3) counter Agent 1 templates from [`mechs_cet3_exh.txt`](./mechs_cet3_exh.txt), including `12` exact table matches and `89` `(known counter Ag1, rightward glider Ag2)` holdout pairs.
- **Mathematical Behavior of Counter-vs-Glider Holdouts**:
  1. **Logarithmic In-Place Binary Counters + Linearly Escaping Gliders**:
     Machines such as `0RA0LB_1LC1RB_0RB0LC | 1RB1RC_0RC0LA_1LB1RC` (`t=4000: ag1=[0..28], ag2=[2..248]`) and `0RB0LA_1LC0RC_1LA1RC | 1RB---_0RC0RB_1LC1RB` (`ag1=[-1..10], ag2=[1..97]`) increment an anchored binary counter in place, expanding rightward only logarithmically as $\Theta(\log t)$ without triggering a superlinear chase overflow, while Agent 2 glides linearly rightward as $\Omega(t)$. Because $\max_{s \le t} p_1(s) = O(\log t) < p_2(t) = \Omega(t)$, they never collide.
  2. **Trapped Counter Templates + Escaping Gliders (12 `mechs_cet3_exh.txt` matches)**:
     Pairs such as `0RB0LC_1LC1RB_0RB0LA | 1RB0RB_1LA1RC_1LC1LA` (along with the remaining 11 matches in `mechs_cet3_exh.txt`, all having `r1 = R1=BIG:tsym=1`) keep Agent 1 trapped in a bounded local cycle near `0..2` (`t=50000: p1=0, max=14`) instead of entering their exponential sweep, while Agent 2 gliders escape freely to $+\infty$ (`p2=7144..16668` by $t=50,000$).
  3. **Shift-Overflow Counters (`[01]LB---_1LC1RB_0RB0LC`) + Gliders in `residue_s20.txt`**:
     There are `152` holdouts in `residue_s20.txt` featuring the `1LC1RB_0RB0LC` shift-overflow transition block (`52` with `[01]LB*_1LC1RB_0RB0LC`). Some of these bounce early off slower/complex gliders and enter giant Round-2 counters within the $10^6$-step simulation window—for example:
     - `0LB---_1LC1RB_0RB0LC | 1RB0RA_1LC0RB_1LA0LA` bounces at $t \approx 1269$ (`pos1 = 247, pos2 = 251`) and settles into a 250-cell Round-2 counter (`t=50000: p1=0, p2=9802`).
     - `1LB---_1LC1RB_0RB0LC | 1RB1RC_0RC0LA_1LB1RC` bounces around $t \approx 606$ (`pos1 = 64, pos2 = 70`) and enters a 70-cell Round-2 counter (`t=50000: p1=0, p2=3872`).
     - `0LB---_1LC1RB_0RB0LC | 0RC1LC_0LA1RA_1RB0LA` (matching `P=6, D=2, M=4`, `B(9), B(10), B(11), H(8)`) exits Round 1 at $t \approx 196,620$ (`L2 = 65,554`, `G1 = 10`) and enters Round 2 (`t=200000: p2=65581`); modulo $P \cdot M = 24$, its $2^{L_r}$ recurrence preserves the fixed non-halting bounce residue $G_r = 10 \notin \{8\}$, yielding the infinite bounce sequence `[10, 10, 10, ...]`.
