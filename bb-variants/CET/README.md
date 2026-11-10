# Catch-Em-Turing (CET)

**Catch-Em-Turing** is a Busy Beaver variant proposed by [NathFR76](https://wiki.bbchallenge.org/wiki/User:NathFR76) in November 2026. Instead of one Turing-machine head, a CET machine runs **two independent agents simultaneously on one shared tape**. The agents do not halt individually; the machine halts only when the two agents occupy the same cell at the same time.

This README follows the [Catch-Em-Turing page on the BusyBeaverWiki](https://wiki.bbchallenge.org/wiki/Catch-Em-Turing), last edited 10 November 2026. The champion tables below are copied from that page and preserve its exact-versus-lower-bound distinctions.

## The model

For each integer `n >= 1`, a **CET(n)** machine has:

- exactly **2 agents**;
- exactly **n states per agent**;
- a separate transition table for each agent;
- a bi-infinite tape, initially all `0`;
- Agent 1 starting at position `0`, Agent 2 at position `2`;
- both agents starting in their initial state (state `A`, called state `0` in the wiki's numbering).

At each step, both agents:

1. read the symbol in their current cell;
2. write a symbol in that cell;
3. move one cell left or right;
4. change state according to their own transition table.

The reads happen before either write, and the writes and moves happen simultaneously. If both agents try to write to the same cell in the same step, the lower-numbered agent has priority (this rule is stated explicitly for the multi-agent extension).

A **collision** is the halting event. There is no separate HALT state. A machine is halting only if the two agents eventually occupy the same cell after a step; otherwise it runs forever.

> **CET(n)** is the maximum number of steps before collision among all halting CET(n) machines.

A transition is written as `write + direction + next state`, for example `0LB` means “write 0, move Left, go to state B.” A `---` denotes a transition that is not defined. In the current CET(3) champion, that transition is never reached.

## Growth and search space

The wiki informally notes two lower-bound relationships:

- `CET(n) >= BB(n)`;
- `CET(n,k) >= BBB(n,k)` when the champion is a translated cycler, where BBB is the Beeping Busy Beaver.

For `n` states and `k` symbols, each transition has `2kn` choices: `k` write symbols, 2 directions, and `n` next states.

- CET has 2 agents, so `2nk` transition entries and at most `(2kn)^(2nk)` transition tables.
- MCET has `n` agents, so `n^2k` transition entries and at most `(2kn)^(n^2k)` transition tables.

These counts assume labelled agents, deterministic tables, and no individual halting state. The search space is finite for every fixed `(n,k)`, but it grows extremely quickly.

## Current CET champions

These are all CET records currently listed on the wiki. `CET(n)` uses 2 symbols; `CET(n,k)` uses `k` symbols.

| Domain | Best known runtime | Status | Discovered by |
|---|---|---|---|
| **CET(1)** | `1` | exact | NathFR76 — Brute Force Research |
| **CET(2)** | `97` | exact | NathFR76 — Brute Force Research |
| **CET(3)** | `(2^1379 + 16483) / 3` (≈ `4.39 × 10^414`) | exact formula | star (second account), Claude; independent verification by sheep and NathFR76 |
| **CET(4)** | `>= 4,622,083,548` | verified lower bound | roromachine14 — TNF Research |
| **CET(2,3)** | `>= 1,528,952,999` | verified lower bound | roromachine14 — TNF Research |

The wiki displays CET(3) as `> 4.39 × 10^414`; that is a rounded display of the exact value, not a separate lower-bound claim. The exact value is the 415-digit integer `exact_halt_steps` in this repository's `CET3_4e414.v` proof, and it equals the formula above.

### CET(1) — 1 step

```text
Agent 1: 1RA---
Agent 2: 1LA---
```

### CET(2) — 97 steps

```text
Agent 1: 1LB0LB_1RB0LA
Agent 2: 1RB1LA_1LA1RB
```

### CET(3) — exact `(2^1379 + 16483) / 3` steps

```text
Agent 1: 0LB---_1LC1RB_0RB0LC
Agent 2: 0RB0LC_1RC1LB_1LB1RA
```

Agent 1's undefined `---` transition is never reached. The local Rocq development proves this for **any** transition placed in that slot.

### CET(4) — at least 4,622,083,548 steps

```text
Agent 1: 1LC0LC_1LA1RB_0RB1LC_0RA0RA
Agent 2: 1RC0RA_1RA1RB_1LC0RD_0RA0RC
```

### CET(2,3) — at least 1,528,952,999 steps

```text
Agent 1: 1RB0RA2LB_2LA2RB1LB
Agent 2: 2RB0RA2RB_2LB1RA0RB
```

## Multi Catch-Em-Turing (MCET)

**MCET(n)** is NathFR76's extension to `n` agents, each with `n` states and its own transition table. All agents share the binary tape and start at positions `0, 2, 4, ...`; Agent `i` starts at `2(i-1)`. All agents start in the initial state and act simultaneously.

Writes are simultaneous. If multiple agents write to the same cell, the lowest-index agent has priority. An MCET machine halts only when **all** agents occupy the same cell at the same time. There is no individual HALT state.

These are all MCET records currently listed on the wiki:

| Domain | Best known runtime | Status | Discovered by |
|---|---|---|---|
| **MCET(1)** | `1` | exact | NathFR76 — analogous to BB(1) |
| **MCET(2)** | `97` | exact | NathFR76 — analogous to CET(2) |
| **MCET(3)** | `>= 1,292,061,272` | verified lower bound | NathFR76 — Simulated Annealing Research |
| **MCET(3,3)** | `>= 34,399` | verified lower bound | NathFR76 — Exhaustive Research |

### MCET(1) — 1 step

```text
Agent 1: 1RA---
```

### MCET(2) — 97 steps

```text
Agent 1: 1LB0LB_1RB0LA
Agent 2: 1RB1LA_1LA1RB
```

### MCET(3) — at least 1,292,061,272 steps

```text
Agent 1: 1LC1LB_1RC1LC_1RA1RB
Agent 2: 1LB0RA_1LC1RA_0RC1LA
Agent 3: 1LB1RA_0RA1LC_1LA1LC
```

### MCET(3,3) — at least 34,399 steps

```text
Agent 1: 2RB2RC1LA_0LA2RA2RB_0LA2RA0LA
Agent 2: 2LC1RC0RA_1LA0RA1LA_0LA2RB
Agent 3: 2RB2LC2RC_0RC1RC2RB_1RC2RA2RC
```

## Verification

The champion table distinguishes:

- **exact** — the value is known, not merely a lower bound;
- **`>=`** — the machine is verified to run at least that many steps; the true maximum may be larger.

All listed champions have been verified to reach their listed step counts before satisfying the collision condition.

For CET(3), this repository contains a separate machine-checked development:

- `CET3_4e414.v` proves `star_cet3_halts : forall undef, halts_at_exact ... exact_halt_steps`.
- `coqc -q CET3_4e414.v` succeeds.
- `Print Assumptions star_cet3_halts` reports **“Closed under the global context”** (no extra axioms).
- The proof covers an arbitrary transition in Agent 1's unreachable `---` slot.

## Local working files

The local `cet*_all_champions.txt` and `*_seeds.txt` files are search working records and may lag the wiki. They are not the canonical current champion list; use the wiki table above.

In particular, older local entries such as the `3,092,745,703`-step CET(3) machine and the `211,190,346`-step MCET(3) machine have been superseded by the current wiki records.

Other local assets:

- `cet.cpp`, `cet_cli.py` — simulator and command-line interface;
- `index.html` — interactive web studio;
- `hunt_*.c`, `hunt_*.cpp` — CET/MCET search engines;
- `CET3_4e414.v` — Rocq proof of the current CET(3) champion;
- `cet3_all_champions.txt`, `cet4_all_champions.txt`, `cet23_all_champions.txt`, `mcet3_all_champions.txt` — historical/working ledgers.

## Source

- [BusyBeaverWiki — Catch-Em-Turing](https://wiki.bbchallenge.org/wiki/Catch-Em-Turing), last edited 10 November 2026.
- Retrieved 10 November 2026.
