# BB(2,5): evidence audit of the 36 non-Hydra machines

Hydra is excluded: `1RB3RB---3LA1RA_2LA3RA4LB0LB0LA`.

The corrected target is to prove each machine's actual status: a halting
certificate or a nonhalting invariant. The first question is **whether all 36
are plausible nonhalting targets**; they are not.
At least two have evidence-backed halting expectations, two more have weak
halting hunches, four have "probviously nonhalting" evidence, and five are
cryptids. The remaining 23 are open, chaotic, or undecided with no decisive
local note.

This is an evidence classification, not a set of proofs. A "likely halts"
entry is a warning that a blanket nonhalting theorem would be false if that
machine halts; it is not itself a halting proof.

Evidence was taken from the local wiki and forum snapshot under
`corpus/knowledge/`, with the 10^10 deep-screen results used only to rule out
small halts. See `bbwork/deep_37_1e10/results.csv` and
`bbwork/cycle4.txt`.

| # | machine | class | evidence |
|---:|---|---|---|
| 1 | `1RB3RB---3LA1RA_2LA3RA4LB0LB1LB` | CRYPTID / OPEN | Bonus Cryptid; re-enters `A(a,b)` at `A(1287547464911049659,10)`, then a biased random walk. Not a proof. |
| 2 | `1RB2RA3LA4LA2RB_2LA3RA---0RA1LA` | OPEN | Chaotic under longitudinal analysis (mxdys notes). |
| 3 | `1RB2RA3LA4LA2RB_2LA3RB---0RA1LA` | OPEN | Chaotic under longitudinal analysis; no decision. |
| 4 | `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA` | **HALT-LIKELY** | LegionMammal978: expected to halt in `exp(exp(O(n)))`; later "probably halts by a harmonic-series argument"; 1.25e13 no-halt is only a lower bound. |
| 5 | `1RB3RB1LA2LA3RA_1LB2RA4RB0LA---` | OPEN | Cascading/random-walk analysis; halting condition not worked out. |
| 6 | `1RB2RA4LA1RB4RB_1LB2LA3RA---0LB` | OPEN | 5e13 no-halt only; no decisive analysis in the local text. |
| 7 | `1RB---4LB0LA4RA_2LB2LA3RA4LB0RB` | OPEN | 1.6e13 no-halt; companion analysis is incomplete. |
| 8 | `1RB2RB3LA4LA1LA_2LB3RA---4RA1RB` | WEAK HALT HUNCH | One member's "feeling" it should halt, with no evidence; chaotic counter, 3.4e13 no-halt. Treat as open. |
| 9 | `1RB---3LB4RB0LA_2LB3LA3RB4RA0RA` | OPEN | No decisive note in the local snapshot. |
| 10 | `1RB3RB---4RA2RA_2LA2RA3LB4LB1LB` | OPEN | Start-in-B variant is nonhalting by CTL; the standard start-in-A machine is not handled. Do not transfer the result. |
| 11 | `1RB3LA1LA2RB2RA_2LA4RA3LB1RA---` | OPEN | `13^n 332$` line: `n` fluctuates; whether it reaches 0 is unresolved. |
| 12 | `1RB4RB4RA1LA3LA_1LB2LA3RB2RB---` | **NONHALT-LIKELY** | "Probably non-halting": a growing right-end periodic pattern is said to block the only halting condition. No proof. |
| 13 | `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA` | OPEN | Nearly closed mixed-digit counter; only halt route is `2>` meeting `21$`. See the separate gap-aware bridge test. |
| 14 | `1RB3LB---4LA1RB_2LA4LA4LB3RB1RA` | CRYPTID / OPEN | 1dCA-like pseudorandom walk; potential cryptid. |
| 15 | `1RB3LA1LA1RA3RA_2LB2RA---4RB1LB` | CRYPTID / OPEN | Collatz-like `C(n)` rules; confirmed cryptid. |
| 16 | `1RB3LA1LA1RA1RA_2LB2RA---4RB1LB` | CRYPTID / OPEN | Collatz-like rules; confirmed cryptid. |
| 17 | `1RB---0RB0LA2RA_2LB2LA3RA4LB0LB` | OPEN | Shift-overflow counter; external Lean `C3` is about a heuristic `nextEra`, and the TM bridge theorem is `sorry` and documented false as stated. |
| 18 | `1RB2RA3LB---2LB_2LA0LA4RB0RB1LA` | **HALT-LIKELY** | "Probviously halting" tetrational overflow counter; estimated 25-50% chance of beating the champion. |
| 19 | `1RB---4LB1RA4RA_2LB2LA3RA4LB0RB` | OPEN | 5e12 no TC; analysis incomplete; moving 13s can halt if two collide. |
| 20 | `1RB---4RB2RB4LA_2LB3LA3LB0RA0RB` | **NONHALT-LIKELY** | "Probviously nonhalting if the counter digits are random"; bouncer plus digit-regrouping binary counter. No proof. |
| 21 | `1RB2LA0RB0LB3LB_2LA4RB3RA0RA---` | OPEN | Peacemaker II analysis; no decision in the local snapshot. |
| 22 | `1RB2RA3LB4LA---_2LA0RB1LA2RB0RA` | OPEN | Cascading rules but chaotic; recurring cell patterns at irregular positions. |
| 23 | `1RB2RA3LA---2LB_2LA4RA4RB0RB0LA` | OPEN | "Spaghetti"; 4e13 no-halt only. |
| 24 | `1RB3LA3LB0RB0LA_2LA4RB1LB1RA---` | OPEN | Permutation of the Spaghetti machine; no decision. |
| 25 | `1RB2RA3LA4LA2RB_2LA---3LB1RA3RA` | **NONHALT-LIKELY** | Likely nonhalting cryptid; right counter simulated to ~8e14 counter steps, no halt. No proof. |
| 26 | `1RB2LB3LA0RA1LB_2LA4RA3RB3LA---` | OPEN | Bouncer/counter; left tail complicated; undecided. |
| 27 | `1RB3LB4LA0LB---_2LA0LA1RB0RA3RA` | OPEN | Related Peacemaker II thread; no decision. |
| 28 | `1RB3RB1LB2RA---_2LA2RB1LA4LB0RA` | OPEN | 27 macro rules listed; state-B-start permutation is solved, standard start is not. |
| 29 | `1RB4LA1RA1RB1LA_2LB3LA---4RA2RB` | OPEN | Analysis exists only as an image; no conclusion. |
| 30 | `1RB3RA3RB4LA1LA_1LB2LA1LA---1RB` | WEAK HALT HUNCH | LegionMammal978 suspected a halt past the simulated range, but a 34-hour, 1.2 TB run reached cell 178 without one; still open. |
| 31 | `1RB2LA4LA1RA1LA_2LB3RB4RB---2RA` | OPEN | Chaotic exponential cascader; cell 155 no-halt only. |
| 32 | `1RB2RB4LA2RA1LA_2LA4RA3LA---3RA` | **NONHALT-LIKELY** | "Probviously nonhalting"; two overflow kinds roughly balance. No proof. |
| 33 | `1RB2LA4RA1LA3LA_0LA2RB3RB2LB---` | CRYPTID / OPEN | Longitudinal rules; unusual overflow halting condition; "looks like a cryptid". |
| 34 | `1RB2LA4RA1LA3LA_0LA3RB3LB2RB---` | OPEN | No decisive local note; 10^10 survival only. |
| 35 | `1RB2LA1LA4RA2LA_0LA3RB3LB2RB---` | OPEN | No decisive local note; 10^10 survival only. |
| 36 | `1RB2LA3LA4RA1LA_0LA3LB3RB1RB---` | OPEN | LegionMammal978's nonhalting argument was retracted; remains open. |

## Tally

- **HALT-LIKELY: 2** (#4, #18)
- **WEAK HALT HUNCH: 2** (#8, #30)
- **NONHALT-LIKELY: 4** (#12, #20, #25, #32)
- **CRYPTID / OPEN: 5** (#1, #14, #15, #16, #33)
- **OPEN: 23**

Corrected count: `2 + 2 + 4 + 5 + 23 = 36`.

The immediate consequence is that "prove all 36 nonhalting" is not a safe
program: it would be false if either HALT-LIKELY machine halts, and no
existing local note proves any of the NONHALT-LIKELY machines nonhalting.
