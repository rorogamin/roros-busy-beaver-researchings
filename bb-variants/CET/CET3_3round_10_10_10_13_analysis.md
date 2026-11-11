# Mathematical Halting Proof for a 3-Round CET(3) Machine (~10^(10^(2.824 × 10^13)) Steps)

**Machine (CET(3), TNF notation):**
```text
1LB---_1LC1RB_0RB0LC | 1RB0LB_0RC0LA_1LB1RC
```

**Claim:** Starting from an all-`0` tape with Agent 1 at position `0` in `StA` and Agent 2 at position `2` in `StA`, this machine halts on collision (`pos1' = pos2'`) after **exact step count**:

$$T_{\text{halt}} = \frac{13 \cdot 2^{L_3 + 2} + 13 \cdot 2^{93{,}824{,}992{,}236{,}935} + 14{,}636{,}698{,}788{,}961{,}028}{12}$$

where

$$L_3 = \frac{2^{93{,}824{,}992{,}236{,}935} + 1{,}125{,}899{,}906{,}843{,}188}{12}$$

and both divisions by $12$ are **exact integers**. Numerically:
- $L_1 = 48$
- $L_2 = 93{,}824{,}992{,}236{,}933 \approx 9.3825 \times 10^{13}$
- $L_3 \approx 10^{28{,}244{,}137{,}006{,}257.58} \approx 10^{2.8244 \times 10^{13}}$
- $\log_{10}(\log_{10}(T_{\text{halt}})) \approx 2.8244137 \times 10^{13}$, so:
  $$T_{\text{halt}} \approx 10^{10^{2.8244137 \times 10^{13}}} \approx 10^{10^{10^{13.4509}}}$$

For comparison, the previous formally verified CET(3) champion (`1LB1RA_0RB1LC_1RA0LB | 1RB0RC_1LB1LC_1RA0RB`, verified in Lean and `CET3_5e47.v`) bounces once and halts in Round 2 after $\approx 10^{5.28 \times 10^{47}}$ steps (height-2 tower), whereas this machine bounces cleanly twice more after initial setup and halts at the end of Round 3 (height-3 tower).

Also note: transition `(Agent 1, StA, 1)` is `---` (arbitrary/unused) and is **provably unreachable** for any transition choice, just as `(StA, 1)` in `0LB---_1LC1RB_0RB0LC` (`CET3_4e414.v`).

---

## 1. CET(3) Semantics & Transition Tables

Under standard Catch-Em-Turing (`CET(3)`) rules:
- Infinite binary tape `tape : Z -> {0, 1}`, initialized to `0` everywhere.
- Initial heads: `pos1 = 0`, `state1 = StA`; `pos2 = 2`, `state2 = StA`.
- If `pos1 != pos2`, one synchronous step applies both agents' rules independently (reading `tape[pos1]` and `tape[pos2]`, writing `w1` to `pos1` and `w2` to `pos2`, shifting `pos1' = pos1 + d1` and `pos2' = pos2 + d2`, and updating states).
- The machine **halts** at step $t \ge 1$ when `pos1' == pos2'` (landing on the same cell simultaneously).

### Transition Tables

**Agent 1 (`1LB---_1LC1RB_0RB0LC`):**
| State | Read `0` | Read `1` |
|---|---|---|
| `StA` | `1, L, StB` (`1LB`) | `---` *(unreachable)* |
| `StB` | `1, L, StC` (`1LC`) | `1, R, StB` (`1RB`) |
| `StC` | `0, R, StB` (`0RB`) | `0, L, StC` (`0LC`) |

**Agent 2 (`1RB0LB_0RC0LA_1LB1RC`):**
| State | Read `0` | Read `1` |
|---|---|---|
| `StA` | `1, R, StB` (`1RB`) | `0, L, StB` (`0LB`) |
| `StB` | `0, R, StC` (`0RC`) | `0, L, StA` (`0LA`) |
| `StC` | `1, L, StB` (`1LB`) | `1, R, StC` (`1RC`) |

---

## 2. Core Lemmas

### Lemma 1 (Unreachability of `(Agent 1, StA, 1)`)
At step $t = 1$, Agent 1 starts at `pos1 = 0` in `StA` reading `0`, so it executes `A0 -> 1LB` and enters `StB`. Looking at the rows of Agent 1 above, every transition from `StB` and `StC` targets only `{StB, StC}`. Therefore Agent 1 never re-enters `StA` for any $t \ge 1$, so `(Agent 1, StA, 1)` is never executed regardless of how `---` is instantiated.

### Lemma 2 (Binary Counter Clear `P(k) = 2^{k+2} - k - 4`)
Define `P(k)` for $k \ge 0$ to be the execution of Agent 1 alone starting at `(pos = x_B, state = StB)` on a tape satisfying:
- `tape[x_B - 1] = 0`
- `tape[z] = 0` for all $z \in [x_B, x_B + k - 1]$

**Statement:** In exact time $P(k) = 2^{k+2} - k - 4$ steps, Agent 1 reaches `(pos = x_B + k, state = StB)` with:
1. All intermediate head positions satisfying $x_B - 1 \le \text{pos}(t) \le x_B + k - 1$ for all $0 \le t < P(k)$ (no cell outside $[x_B - 1, x_B + k - 1]$ is ever read or written before step $P(k)$).
2. Final tape values: `tape'[x_B - 1] = 0`, and `tape'[z] = 1` for all $z \in [x_B, x_B + k - 1]$, and all $z \notin [x_B, x_B + k - 1]$ unchanged.

**Proof by induction on $k$:**
- **Base case ($k = 0$):** At $t = 0$, `pos = x_B + 0` and `state = StB`; $P(0) = 2^2 - 0 - 4 = 0$, vacuously true.
- **Inductive step ($k \to k + 1$):** Suppose the block of `0`s covers $[x_B, x_B + k]$ and `tape[x_B - 1] = 0`.
  1. By the induction hypothesis on $[x_B, x_B + k - 1]$, in $P(k)$ steps Agent 1 reaches `pos = x_B + k`, `state = StB`, with $[x_B, x_B + k - 1] = 1^k$ and `tape[x_B + k] = 0` untouched.
  2. Step $P(k) + 1$: at `x_B + k` reading `0` in `StB`, rule `B0 -> 1LC` writes `1` to `x_B + k` and moves to `x_B + k - 1` in `StC`.
  3. Next $k$ steps: while reading `1` across `x_B + k - 1` down to `x_B`, rule `C1 -> 0LC` turns `[x_B, x_B + k - 1]` back to `0^k` and lands at `x_B - 1` in `StC`.
  4. Next $1$ step: at `x_B - 1` reading `0` in `StC`, rule `C0 -> 0RB` preserves `0` at `x_B - 1` and lands at `x_B` in `StB`. Now `[x_B, x_B + k - 1] = 0^k` and `tape[x_B + k] = 1`.
  5. By the induction hypothesis on $[x_B, x_B + k - 1]$, in $P(k)$ steps Agent 1 converts `[x_B, x_B + k - 1]` to `1^k` and arrives at `x_B + k` in `StB`.
  6. Final $1$ step: at `x_B + k` reading `1` in `StB`, rule `B1 -> 1RB` preserves `1` and steps right to `x_B + k + 1` in `StB`.
- Summing step counts:
  $$P(k+1) = 2 P(k) + k + 3 = 2(2^{k+2} - k - 4) + k + 3 = 2^{k+3} - (k + 1) - 4.$$
- All intermediate positions lie in $[x_B - 1, x_B + k]$. $\blacksquare$

### Lemma 3 (Right-Walk in `StB` and Left-Reset in `StC`)
- **Right-walk (`StB` over `1^d`):** Since `B1 -> 1RB`, starting at `pos = x` in `StB` with `tape[x .. x+d-1] = 1^d`, in $d$ steps Agent 1 moves cleanly to `x + d` in `StB` leaving the tape unchanged.
- **Left-reset (`StC` after bounce):** Suppose after a bounce at step $t_{\text{end}}$ Agent 1 is at `pos = p1_end` in `StC`, with `tape[-2] = 0`, `tape[-1 .. p1_end] = 1^{p1_end + 2}`, and `tape[p1_end + 1 .. x_ze] = 0^Z` (where `x_ze >= p1_end`).
  - Rule `C1 -> 0LC` executes `p1_end + 2` times walking left over `[-1 .. p1_end]`, writing `0` everywhere and landing at `-2` in `StC`.
  - Rule `C0 -> 0RB` at `-2` executes once, preserving `tape[-2] = 0` and landing at `pos = -1` in `StB`.
  - Thus in exact time $p_{1,\text{end}} + 3$ steps (at $t_B = t_{\text{end}} + p_{1,\text{end}} + 3$), Agent 1 resets to the exact starting configuration of **Lemma 2** at `x_B = -1` with length $L = (x_{\text{ze}}) - (-1) + 1 = x_{\text{ze}} + 2$ contiguous `0`s (`M = 0`).

### Lemma 4 (Agent 2 Canonical Period-13 Rightward Glider, `phase 7`)
Say Agent 2 is in **canonical glider configuration `Glider(X)`** if:
- `pos2 = X`, `state2 = StB`
- `tape[z] = 1` for all $z < X$ (within the clear zone)
- `(tape[X], tape[X+1], tape[X+2]) = (0, 1, 1)`
- `tape[z] = 0` for all $z \ge X + 3$

Tracing 13 transitions of Agent 2 alone from `X = 0` (tape column shows `tape[X-1 .. X+4]` **before** each step):

| Step | `pos2` | `state2` | Read | Action | `tape[-1..+4]` (before step) |
|---:|---:|:---:|:---:|:---:|:---:|
| `0` | `0` | `StB` | `0` | `0RC` | `1 \| 0 1 1 0 0` |
| `1` | `1` | `StC` | `1` | `1RC` | `1 \| 0 1 1 0 0` |
| `2` | `2` | `StC` | `1` | `1RC` | `1 \| 0 1 1 0 0` |
| `3` | `3` | `StC` | `0` | `1LB` | `1 \| 0 1 1 0 0` |
| `4` | `2` | `StB` | `1` | `0LA` | `1 \| 0 1 1 1 0` |
| `5` | `1` | `StA` | `1` | `0LB` | `1 \| 0 1 0 1 0` |
| `6` | `0` | `StB` | `0` | `0RC` | `1 \| 0 0 0 1 0` |
| `7` | `1` | `StC` | `0` | `1LB` | `1 \| 0 0 0 1 0` |
| `8` | `0` | `StB` | `0` | `0RC` | `1 \| 0 1 0 1 0` |
| `9` | `1` | `StC` | `1` | `1RC` | `1 \| 0 1 0 1 0` |
| `10` | `2` | `StC` | `0` | `1LB` | `1 \| 0 1 0 1 0` |
| `11` | `1` | `StB` | `1` | `0LA` | `1 \| 0 1 1 1 0` |
| `12` | `0` | `StA` | `0` | `1RB` | `1 \| 0 0 1 1 0` |
| `13` | **`1`** | **`StB`** | — | — | `1 \| 1 [0 1 1] 0` $\implies$ `Glider(X + 1)` |

Crucially, across all 13 steps $k = 0 \dots 12$:
- $\min \text{pos}_2 = X$ (Agent 2 **never** reads or touches any cell $< X$),
- $\max \text{pos}_2 = X + 3$, and
- `Glider(X)` transitions cleanly to `Glider(X + 1)` with `tape'[X] = 1` left behind.

By induction on $K \ge 0$, if Agent 2 starts in `Glider(X)` and Agent 1 stays strictly to the left of $X$ during all $13K$ steps, Agent 2 ends at `Glider(X + K)` after $13K$ steps with `tape[X .. X + K - 1] = 1^K`.

### Lemma 5 (Sync & Catch Formula Between Counter Exit and Glider)
Suppose after Round $r-1$ (for $r \in \{1, 2, 3\}$):
- Agent 1 resets at step $t_{B,r}$ at `pos1 = -1` (`StB`) with clean counter `0^{L_r}` across `[-1 .. L_r - 2]` and `tape[-2] = 0`, `tape[>= L_r - 1]` untouched ($= 1$ up to Agent 2).
- By **Lemma 2**, Agent 1 exits the counter at:
  $$t_{\text{exit},r} = t_{B,r} + 2^{L_r + 2} - L_r - 4, \qquad x_{\text{exit},r} = L_r - 1, \quad \text{state1} = \text{StB}.$$
- Meanwhile, Agent 2 entered `Glider(p2_gl,r)` at step $t_{\text{gl},r}$ (with $t_{\text{gl},r} \le t_{\text{exit},r}$ and all cells `[x_exit,r .. p2_gl,r - 1]` equal to `1`).

For any integer $K_r \ge 0$, consider the synchronization step:
$$t_{\text{sync},r} = t_{\text{gl},r} + 13 K_r.$$
Provided $t_{\text{sync},r} \ge t_{\text{exit},r}$ and Agent 1 has not overtaken Agent 2 (`p1 < p2` at all intermediate times), at $t = t_{\text{sync},r}$:
- Agent 2 is in `Glider(p2_gl,r + K_r)` at position $X_{\text{sync},r} = p_{2,\text{gl},r} + K_r$.
- Agent 1 has walked right in `StB` over `1`s (**Lemma 3**) to position $x_{\text{exit},r} + (t_{\text{sync},r} - t_{\text{exit},r})$.
- The separation $G_r = X_{\text{sync},r} - p_1(t_{\text{sync},r})$ satisfies:
  $$G_r = G_{0,r} - 12 K_r, \qquad \text{where } G_{0,r} = (p_{2,\text{gl},r} - x_{\text{exit},r}) + (t_{\text{exit},r} - t_{\text{gl},r}).$$

Since $\Delta K_r = 1$ shifts $G_r$ by $-12$, picking any target integer gap $G_r > 0$ with $G_r \equiv G_{0,r} \pmod{12}$ determines the unique non-negative integer $K_r = (G_{0,r} - G_r)/12$ directly!

---

## 3. Complete Step-by-Step Verification Across All 4 Phases

### Phase 0: Concrete Bootstrap (`t = 0 .. 629 -> 630`)
Simulating the machine directly from the blank tape (`pos1 = 0 (StA)`, `pos2 = 2 (StA)`):
- At `t = 1..168`, Agent 1 establishes an initial 7-bit counter on `[-1 .. 5]` while Agent 2 enters its `(13, 1)` glider.
- At `t = 566..598`, the initial `L_0 = 7` counter overflows and bounces off Agent 2 once (`mx1 = 48`).
- At exact step **`t = 629`**:
  - `pos1 = -1`, `state1 = StB`
  - `pos2 = 51`, `state2 = StA`
  - `tape[z] = 0` for all $z < -1$ and all $z \in [-1, 46]$ (`0^{48}` across `[-1 .. 46]`, so **`L_1 = 48`**)
  - `tape[47..55] = 1, 1, 1, 1, 0, 0, 1, 1, 0`, and `tape[z] = 0` for all $z \ge 55$.

Note carefully what happens on the decoupling boundary `t = 629 -> 630`:
- At `t = 629`, Agent 1 starts **Lemma 2** cleanly at `x_B = -1` with `L_1 = 48` zeros (`M = 0`), taking $P(48) = 2^{50} - 52$ steps inside `[-2 .. 46]` before exiting at `x_exit1 = 47 (StB)` at exact step:
  $$t_{\text{exit},1} = 629 + 2^{50} - 52 = 2^{50} + 577 = 1{,}125{,}899{,}906{,}843{,}201.$$
- Meanwhile at step `t = 630` (`629 -> 630`), Agent 2 at `pos2 = 51 (StA)` reads `0` (`A0 -> 1RB`), writing `1` at `51` and landing at **`pos2 = 52`, `state2 = StB`** with `tape[47..51] = 1^5` and `(tape[52], tape[53], tape[54]) = (0, 1, 1)`, `tape[>=55] = 0`.
- That puts Agent 2 in **`Glider(52)`** at `t_gl1 = 630`, strictly separated from the counter zone `[-2 .. 46]` by `1^5` across `[47 .. 51]`.

---

### Round 1: Catch & Bounce (`L_1 = 48` $\to$ `L_2 = 93,824,992,236,933`)

Applying **Lemma 5** with `x_exit1 = 47`, `t_exit1 = 2^50 + 577`, `p2_gl1 = 52`, `t_gl1 = 630`:
$$G_{0,1} = (52 - 47) + (2^{50} + 577 - 630) = 2^{50} - 48 = 1{,}125{,}899{,}906{,}843{,}088.$$
Notice $2^{50} \equiv 4 \pmod{12}$ (since $50$ is even and $\ge 2$) and $48 \equiv 0 \pmod{12}$, so:
$$G_{0,1} \equiv 4 \pmod{12}.$$
Choose the minimal decoupled collision gap **$G_1 = 16$** ($\equiv 4 \pmod{12}$):
$$K_1 = \frac{2^{50} - 48 - 16}{12} = \frac{2^{50} - 64}{12} = 93{,}824{,}992{,}236{,}880.$$
At $t_{\text{sync},1} = 630 + 13 K_1$, relative to $x_{\text{sync},1} = 52 + K_1 - 16 = 93{,}824{,}992{,}236{,}916$:
- Agent 1 is at `rel_p1 = 0` (`StB`) on `1^inf` on the left,
- Agent 2 is in `Glider(16)` (`rel_p2 = 16`, `StB`, `[16..18] = 011`).

**Finite 28-step collision (`G_1 = 16`):**
Tracing 28 steps from `rel_p1 = 0 (StB)`, `rel_p2 = 16 (StB)`:
- During all 28 steps, $\min(\text{rel\_p1}) = 0$ (cells `< 0` are untouched `1`s), heads never collide (`p1 != p2`).
- At `s = 28`: `rel_p1 = 6 (StC)`, `rel_p2 = 18 (StB)` in `Glider(18)`, and the local tape `[0 .. 20]` is `1^7 0^9 11 [011]` (`[7..15]` = 9 zeros, `[16..17]` = `11`).
- Thus at $t_{\text{gl},2} = t_{\text{sync},1} + 28$:
  $$t_{\text{gl},2} = 1{,}219{,}724{,}899{,}080{,}098, \qquad p_{2,\text{gl},2} = x_{\text{sync},1} + 18 = 93{,}824{,}992{,}236{,}934$$
  $$p_{1,\text{end},1} = x_{\text{sync},1} + 6 = 93{,}824{,}992{,}236{,}922, \qquad x_{\text{ze},1} = p_{1,\text{end},1} + 9 = 93{,}824{,}992{,}236{,}931.$$
- By **Lemma 3** (`p1_end,1 + 3` additional steps), Agent 1 clears `[-1 .. p1_end,1]` to `0` and resets to `pos1 = -1 (StB)` on `0^{L_2}` at:
  $$L_2 = x_{\text{ze},1} + 2 = 93{,}824{,}992{,}236{,}933, \qquad t_{B,2} = t_{\text{gl},2} + p_{1,\text{end},1} + 3 = 1{,}313{,}549{,}891{,}317{,}023,$$
  $$x_{\text{exit},2} = L_2 - 1 = 93{,}824{,}992{,}236{,}932,$$
  leaving `tape[x_exit,2 .. p2_gl,2 - 1] = 1^2` (`p2_gl,2 - x_exit,2 = 2`). Note $t_{B,2} - t_{\text{gl},2} = 93{,}824{,}992{,}236{,}925 > 0$ so $t_{\text{gl},2} < t_{\text{exit},2}$.

---

### Round 2: Catch & Bounce ($L_2 \to L_3$)

By **Lemma 2** and **Lemma 5**, Agent 1 exits the $L_2$-counter at:
$$t_{\text{exit},2} = t_{B,2} + 2^{L_2 + 2} - L_2 - 4, \qquad x_{\text{exit},2} = L_2 - 1.$$
Substitute `t_B2 - t_gl2 = p1_end,1 + 3` and `p2_gl2 - x_exit2 = p2_gl2 - L2 + 1` into $G_{0,2}$:
$$G_{0,2} = (p_{2,\text{gl},2} - L_2 + 1) + (2^{L_2 + 2} + p_{1,\text{end},1} + 3 - L_2 - 4) = 2^{L_2 + 2} + p_{2,\text{gl},2} + p_{1,\text{end},1} - 2 L_2.$$

Using the concrete integers above:
$$p_{2,\text{gl},2} + p_{1,\text{end},1} - 2 L_2 = 93{,}824{,}992{,}236{,}934 + 93{,}824{,}992{,}236{,}922 - 2(93{,}824{,}992{,}236{,}933) = -10.$$
Hence:
$$G_{0,2} = 2^{93{,}824{,}992{,}236{,}935} - 10.$$
Since the exponent $L_2 + 2 = 93{,}824{,}992{,}236{,}935$ is odd ($\ge 3$), $2^{L_2 + 2} \equiv 8 \pmod{12}$, so:
$$G_{0,2} \equiv 8 - 10 \equiv 10 \pmod{12}.$$

Choose the collision gap **$G_2 = 22$** ($\equiv 10 \pmod{12}$, with `1^inf` on the left extending $> 9 \times 10^{13}$ cells; choosing $G_2 = 34$ runs 13 steps longer and never visits `< 0` in relative coordinates, giving the exact same `L_3` and `T_halt`):
$$K_2 = \frac{G_{0,2} - 22}{12} = \frac{2^{93{,}824{,}992{,}236{,}935} - 32}{12}.$$

**Finite 49-step collision (`G_2 = 22`):**
Tracing 49 steps from `rel_p1 = 0 (StB)`, `rel_p2 = 22 (StB)` in `Glider(22)` (with `1`s at all relative positions $< 22$ down to $-3$, well within `x_sync2 ~ 10^{2.82e13}`):
- Heads never collide during steps `1..49` ($\min(\text{rel\_p1}) = -3$).
- At `s = 49`: `rel_p1 = -3 (StC)`, `rel_p2 = 25 (StB)` in `Glider(25)`, with `[-2 .. 21]` equal to `0^{24}` (`24` zeros) and `[22 .. 24]` equal to `111`.
- Therefore:
  $$t_{\text{gl},3} = t_{\text{gl},2} + 13 K_2 + 49, \qquad p_{2,\text{gl},3} = p_{2,\text{gl},2} + K_2 - 22 + 25 = p_{2,\text{gl},2} + K_2 + 3,$$
  $$p_{1,\text{end},2} = p_{2,\text{gl},2} + K_2 - 22 - 3 = p_{2,\text{gl},2} + K_2 - 25, \qquad x_{\text{ze},2} = p_{1,\text{end},2} + 24 = p_{2,\text{gl},2} + K_2 - 1.$$

By **Lemma 3**, Agent 1 wipes back to `-1 (StB)` leaving a clean `0^{L_3}` block of exact length:
$$L_3 = x_{\text{ze},2} + 2 = p_{2,\text{gl},2} + K_2 + 1 = \frac{2^{93{,}824{,}992{,}236{,}935} - 32 + 12(p_{2,\text{gl},2} + 1)}{12} = \frac{2^{93{,}824{,}992{,}236{,}935} + 1{,}125{,}899{,}906{,}843{,}188}{12}.$$
Divisibility check: $1{,}125{,}899{,}906{,}843{,}188 \equiv 4 \pmod{12}$ and $2^{93{,}824{,}992{,}236{,}935} \equiv 8 \pmod{12}$, so $8 + 4 \equiv 0 \pmod{12}$; the division is **exact**.

---

### Round 3: Final Catch & Halt

To determine $G_{0,3} \bmod 12$, we need $2^{L_3 + 2} \bmod 12$, which depends only on the parity of $L_3 + 2$ (equivalently $L_3 \bmod 2$)!
And to find $L_3 \bmod 2$ (and $L_3 \bmod 156$ for full cross-checking), we evaluate $2^{L_2 + 2} \bmod 144 \cdot 13 = 1872$:
- First factor $1872 = 2^4 \cdot 3^2 \cdot 13$.
- $\operatorname{ord}_{3^2}(2) = 6$, $\operatorname{ord}_{13}(2) = 12$, so $\operatorname{ord}_{117}(2) = \operatorname{lcm}(6, 12) = 12$.
- Since $L_2 + 2 = 93{,}824{,}992{,}236{,}935 \equiv 3 \pmod{12}$ and $L_2 + 2 \ge 4$:
  $$2^{L_2 + 2} \equiv 2^3 = 8 \pmod{117}, \qquad 2^{L_2 + 2} \equiv 0 \pmod{16}.$$
  Since $16^{-1} \equiv 22 \pmod{117}$, CRT gives $2^{L_2 + 2} \equiv 16 \cdot (8 \cdot 22 \bmod 117) = 16 \cdot 59 = 944 \pmod{1872}$ ($944 \equiv 8 \pmod{117}$ and $944 \equiv 0 \pmod{16}$).
- Plug into $L_3 = (2^{L_2 + 2} + 1{,}125{,}899{,}906{,}843{,}188)/12$:
  - Working mod $12 \cdot 156 = 1872$:
    $$944 + (1{,}125{,}899{,}906{,}843{,}188 \bmod 1872) = 944 + 1204 = 2148 \equiv 276 \pmod{1872}.$$
  - Dividing by $12$:
    $$L_3 \bmod 156 = \frac{276}{12} = 23.$$
  *(In particular, $L_3 \equiv 23 \pmod{156}$ is odd, so $L_3 \equiv 1 \pmod 2$ and $L_3 + 2 \equiv 1 \pmod{12}$.)*

Now compute $G_{0,3}$ via **Lemma 5** at Round 3:
$$G_{0,3} = 2^{L_3 + 2} + p_{2,\text{gl},3} + p_{1,\text{end},2} - 2 L_3.$$
From Round 2, $p_{2,\text{gl},3} = X_2 + 3$, $p_{1,\text{end},2} = X_2 - 25$, and $L_3 = X_2 + 1$ (where $X_2 = p_{2,\text{gl},2} + K_2$):
$$p_{2,\text{gl},3} + p_{1,\text{end},2} - 2 L_3 = (X_2 + 3) + (X_2 - 25) - 2(X_2 + 1) = -24 \equiv 0 \pmod{12}.$$
And since $L_3 + 2 \ge 3$ is odd ($L_3 \equiv 23 \equiv 1 \pmod 2$), $2^{L_3 + 2} \equiv 8 \pmod{12}$, giving:
$$G_{0,3} \equiv 8 + 0 \equiv 8 \pmod{12}.$$

Choose the minimal collision gap **$G_3 = 8$** ($\equiv 8 \pmod{12}$), with $K_3 = (G_{0,3} - 8)/12 \ge 0$:
$$K_3 = \frac{2^{L_3 + 2} - 32}{12}.$$
*(Alternatively, $G_3' = 20$ halts at step 21 and yields the exact same total step count.)*

**Final 8-step collision & HALT (`G_3 = 8`):**
At $t_{\text{sync},3} = t_{\text{gl},3} + 13 K_3$, relative to $x_{\text{sync},3} = p_{2,\text{gl},3} + K_3 - 8$:
- Agent 1 is at `rel_p1 = 0 (StB)` with `1^8` across `[0 .. 7]`.
- Agent 2 is at `rel_p2 = 8 (StB)` in `Glider(8)` (`[8..10] = 011`, `[>=11] = 0`).

| Step `s` | `rel_p1` (before $\to$ after) | Rule 1 | `rel_p2` (before $\to$ after) | Rule 2 |
|---:|---|:---:|---|:---:|
| `1` | `0 (B)` $\to$ `1 (B)` | `B1 -> 1RB` | `8 (B)` $\to$ `9 (C)` | `B0 -> 0RC` |
| `2` | `1 (B)` $\to$ `2 (B)` | `B1 -> 1RB` | `9 (C)` $\to$ `10 (C)` | `C1 -> 1RC` |
| `3` | `2 (B)` $\to$ `3 (B)` | `B1 -> 1RB` | `10 (C)` $\to$ `11 (C)` | `C1 -> 1RC` |
| `4` | `3 (B)` $\to$ `4 (B)` | `B1 -> 1RB` | `11 (C)` $\to$ `10 (B)` | `C0 -> 1LB` |
| `5` | `4 (B)` $\to$ `5 (B)` | `B1 -> 1RB` | `10 (B)` $\to$ `9 (A)` | `B1 -> 0LA` |
| `6` | `5 (B)` $\to$ `6 (B)` | `B1 -> 1RB` | `9 (A)` $\to$ `8 (B)` | `A1 -> 0LB` |
| `7` | `6 (B)` $\to$ `7 (B)` | `B1 -> 1RB` | `8 (B)` $\to$ `9 (C)` | `B0 -> 0RC` |
| **`8`** | **`7 (B)` $\to$ `8 (B)`** | `B1 -> 1RB` | **`9 (C)` $\to$ `8 (B)`** | `C0 -> 1LB` |

At step **`s = 8`**, both agents land simultaneously at **`rel_p1 = rel_p2 = 8` (`pos1' = pos2'`)** and the machine **HALTS**.

---

## 4. Exact Closed-Form Step Count Derivation

Summing from $t_{\text{gl},2}$ through Round 3 halt:
$$T_{\text{halt}} = t_{\text{gl},3} + 13 K_3 + 8 = t_{\text{gl},2} + 13 K_2 + 49 + 13 K_3 + 8.$$
Multiply by $12$:
$$12 T_{\text{halt}} = 12 t_{\text{gl},2} + 13(12 K_2) + 12(49) + 13(12 K_3) + 12(8).$$
Substitute $12 K_2 = 2^{L_2 + 2} - 32$ and $12 K_3 = 2^{L_3 + 2} - 32$:
$$12 T_{\text{halt}} = 13 \cdot 2^{L_3 + 2} + 13 \cdot 2^{L_2 + 2} + C_T,$$
where:
$$C_T = 12(1{,}219{,}724{,}899{,}080{,}098) + 13(-32) + 12(49) + 13(-32) + 12(8) = 14{,}636{,}698{,}788{,}961{,}028.$$

### Exact Divisibility Verification
Modulo $12$:
- $L_2 + 2 = 93{,}824{,}992{,}236{,}935$ is odd $\implies 2^{L_2 + 2} \equiv 8 \pmod{12}$.
- $L_3 + 2$ is odd ($L_3 \equiv 23 \pmod{156}$) $\implies 2^{L_3 + 2} \equiv 8 \pmod{12}$.
- $14{,}636{,}698{,}788{,}961{,}028 \equiv 8 \pmod{12}$.
- Sum: $13(8) + 13(8) + 8 = 104 + 104 + 8 = 216 = 12 \times 18 \equiv 0 \pmod{12}$.

Thus:
$$T_{\text{halt}} = \frac{13 \cdot 2^{L_3 + 2} + 13 \cdot 2^{93{,}824{,}992{,}236{,}935} + 14{,}636{,}698{,}788{,}961{,}028}{12}$$
is an exact integer.

---

## 5. Standalone Verification Script (Python 3)

Anyone can run this self-contained script (`< 0.1s`, no external packages) to verify:
1. $P(k)$ induction check for $k = 0 \dots 10$,
2. exact simulation of `t = 0 .. 630` and verification of `t = 629 -> 630`,
3. exact 13-step `Glider(X)` transition table,
4. concrete Round-1 (`28` steps), Round-2 (`49` steps), and Round-3 (`8` steps) collision blocks,
5. exact closed-form expressions for $L_2$, $L_3$, and $T_{\text{halt}}$, including modular consistency up to $12^4 \cdot 13^2$.

```python
def parse_mach(s):
    res = []
    for ag in s.split('|'):
        sts = []
        for st in ag.split('_'):
            row = []
            for b in (0, 1):
                tok = st[3*b : 3*b+3]
                row.append(None if tok == '---' else (int(tok[0]), 1 if tok[1] == 'R' else -1, ord(tok[2]) - 65))
            sts.append(row)
        res.append(sts)
    return res

M = parse_mach("1LB---_1LC1RB_0RB0LC|1RB0LB_0RC0LA_1LB1RC")

def cet_step(tp, p1, s1, p2, s2):
    t1 = M[0][s1][tp.get(p1, 0)]
    t2 = M[1][s2][tp.get(p2, 0)]
    assert t1 is not None and t2 is not None
    tp[p2] = t2[0]
    tp[p1] = t1[0]
    return p1 + t1[1], t1[2], p2 + t2[1], t2[2]

# 1. Counter Lemma P(k) = 2^(k+2) - k - 4 for k = 0..10
for k in range(11):
    tp = {-1: 0}
    pos, st, steps = 0, 1, 0
    while pos < k:
        tr = M[0][st][tp.get(pos, 0)]
        assert pos >= -1 and tr is not None
        tp[pos] = tr[0]; pos += tr[1]; st = tr[2]; steps += 1
    assert steps == (1 << (k + 2)) - k - 4 and pos == k and st == 1
    assert all(tp.get(x, 0) == 1 for x in range(k)) and tp[-1] == 0

# 2. Phase 0: t = 0 .. 630
tp = {}; p1, s1, p2, s2 = 0, 0, 2, 0
for t in range(1, 631):
    assert p1 != p2
    p1, s1, p2, s2 = cet_step(tp, p1, s1, p2, s2)
    if t == 629:
        assert (p1, s1, p2, s2) == (-1, 1, 51, 0)
        assert all(tp.get(x, 0) == 0 for x in range(-20, 47))
        assert [tp.get(x, 0) for x in range(47, 56)] == [1, 1, 1, 1, 0, 0, 1, 1, 0]
        assert all(tp.get(x, 0) == 0 for x in range(55, 80))

assert (p1, s1, p2, s2) == (-2, 2, 52, 1)
assert [tp.get(x, 0) for x in range(47, 56)] == [1, 1, 1, 1, 1, 0, 1, 1, 0]

# 3. Canonical 13-step Glider Cycle
tp_g = {x: (1 if x < 0 else (1 if x in (1, 2) else 0)) for x in range(-10, 20)}
qg, sg, min_pg = 0, 1, 0
for _ in range(13):
    tr = M[1][sg][tp_g.get(qg, 0)]
    tp_g[qg] = tr[0]; qg += tr[1]; sg = tr[2]
    min_pg = min(min_pg, qg)
assert qg == 1 and sg == 1 and min_pg == 0
assert [tp_g[x] for x in range(-4, 5)] == [1, 1, 1, 1, 1, 0, 1, 1, 0]

def run_block(G, steps_cnt):
    tp = {x: (1 if x < G else (1 if x in (G + 1, G + 2) else 0)) for x in range(-20, G + 20)}
    a1, sa1, a2, sa2, mn1 = 0, 1, G, 1, 0
    for _ in range(steps_cnt):
        assert a1 != a2
        a1, sa1, a2, sa2 = cet_step(tp, a1, sa1, a2, sa2)
        mn1 = min(mn1, a1)
    return tp, a1, sa1, a2, sa2, mn1

# 4. Round 1 (G1 = 16, 28 steps)
tp1, a1_1, sa1_1, a2_1, sa2_1, mn1_1 = run_block(16, 28)
assert (a1_1, sa1_1, a2_1, sa2_1, mn1_1) == (6, 2, 18, 1, 0)
assert all(tp1[x] == 1 for x in range(-10, 7))
assert all(tp1[x] == 0 for x in range(7, 16))
assert [tp1[x] for x in range(16, 22)] == [1, 1, 0, 1, 1, 0]

# 5. Round 2 (G2 = 22, 49 steps)
tp2, a1_2, sa1_2, a2_2, sa2_2, mn1_2 = run_block(22, 49)
assert (a1_2, sa1_2, a2_2, sa2_2, mn1_2) == (-3, 2, 25, 1, -3)
assert all(tp2[x] == 1 for x in range(-10, -2))
assert all(tp2[x] == 0 for x in range(-2, 22))
assert [tp2[x] for x in range(22, 29)] == [1, 1, 1, 0, 1, 1, 0]

# 6. Round 3 Halt (G3 = 8, 8 steps)
tp3 = {x: (1 if x < 8 else (1 if x in (9, 10) else 0)) for x in range(-10, 20)}
a1, sa1, a2, sa2 = 0, 1, 8, 1
for s in range(1, 9):
    if s < 8:
        assert a1 != a2
    a1, sa1, a2, sa2 = cet_step(tp3, a1, sa1, a2, sa2)
assert a1 == a2 == 8 and sa1 == sa2 == 1

# 7. Exact Closed-Form Arithmetic & Modular Cross-Check
t_exit1 = (1 << 50) + 577
K1 = ((52 - 47 + t_exit1 - 630) - 16) // 12
assert (52 - 47 + t_exit1 - 630 - 16) % 12 == 0 and K1 == 93824992236880
t_gl2 = 630 + 13 * K1 + 28
p2_gl2 = 52 + K1 - 16 + 18
p1_end1 = 52 + K1 - 16 + 6
L2 = p1_end1 + 9 + 2
assert L2 == 93824992236933
assert t_gl2 == 1219724899080098

MOD = 12**4 * 13**2
p2L2 = pow(2, L2 + 2, 12 * MOD)
assert (p2L2 + 1125899906843188) % 12 == 0
L3_m = ((p2L2 + 1125899906843188) // 12) % MOD
assert L3_m % 156 == 23 and (L3_m + 2) % 12 == 1

oddM = 3**4 * 13**2  # lcm(ord_{3^4}(2)=54, ord_{13^2}(2)=156) = 1404
r_odd = pow(2, (L3_m + 2) % 1404, oddM)
p2L3 = ((1 << 8) * ((r_odd * pow(1 << 8, -1, oddM)) % oddM)) % (12 * MOD)

C_T = 14636698788961028
assert (13 * 8 + 13 * 8 + C_T) % 12 == 0

# Direct round-by-round mod (MOD // 12) check vs closed form
K2_m = ((pow(2, L2 + 2, 12 * MOD) - 32) // 12) % MOD
t_gl3_m = (t_gl2 + 13 * K2_m + 49) % MOD
K3_m = ((p2L3 - 32) // 12) % MOD
T_direct_m = (t_gl3_m + 13 * K3_m + 8) % (MOD // 12)
T_closed_m = ((13 * (p2L3 % (12 * MOD)) + 13 * (p2L2 % (12 * MOD)) + C_T) // 12) % (MOD // 12)
assert T_direct_m == T_closed_m

print("ALL VERIFIED! L2 =", L2, "L3 % 156 =", L3_m % 156, "T_halt % (MOD/12) =", T_closed_m)
```
