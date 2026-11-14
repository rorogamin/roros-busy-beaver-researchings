# Machine 14 — dyuan `A/2>` closed-invariant search

Target: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`

Source table: `machine14_2026_rules.md`, interpreted as a rightmost-active-control
rewrite system. The active `A` or `2>` reads the block immediately to its right.
This is an assumption about the regrouped table; it has not been validated
against the raw five-symbol machine.

## Simulation facts (200,000 macro steps)

- No halt; maximum block-word length 91.
- Immediate predecessor of the final `21$`:
  - `214`: 199,920 times
  - `14`: 41 times
  - `A`: 39 times
- No occurrence of adjacent `2> 2>`.
- No occurrence of `22 21$`, `21 21$`, `24 21$`, `221 21$`, or `A 221 21$`.
- The only `22 14 21$` occurrence is the initial suffix. It is consumed by a
  `2>` immediately; the run then settles behind a growing `214` buffer.
- A `2>` can be left of an internal `21` (first seen at step 23), but the
  `214` blocks to its right absorb the resulting `221` before it reaches the
  final `21$`.

## Fixed-window invariant search

For a window length `W`, the search starts with every `W`-window observed in the
200,000-step run plus the initial windows, and closes the set under every rule
with the exact `W-1` left and right context tokens. If the halt window
`2> 21$ #...` enters the closure, no sound `W`-window invariant exists for this
rightmost-head system.

| W | Result | First halt witness |
|---|--------|--------------------|
| 2 | fails | `2> 21$` |
| 3 | fails | `2> 2> A 221 21$ #` |
| 4 | fails | `2> 2> 2> A 221 21$ #` |

The extra `2>` padding grows with `W`: the closure can always put an arbitrary
run of `2>` controls to the left of `A 221 21$`. The dangerous step is the
rule

```
A 221 -> 22 A 2>
```

when that `2>` lands immediately before the final `21$`.

## Why a fixed window is insufficient

The causal chain is unbounded on the left:

```
A 22* 14 21$  ->  ... A 14 21$  ->  A 24 21$  ->  A 21 21$  ...
```

and independently

```
2> 22* 21 21$  ->  2> 21 21$  ->  221 21$  ->  A 221 21$  ->  halt.
```

A finite forbidden-pattern test confirms the first step: forbidding
`A 14 21$` is not enough, because the context `A 22 14 21$` creates it via
`A 22 -> 22 A A`. The same happens for any finite number of `22` blocks, so
the obstruction is a regular-language (`22*`) or stack/buffer condition, not a
bounded local window.

## Reset-automaton attempt

The observed reset states are very small. If `R` is the last occurrence of
`2>` or `214` and `s` is the suffix after it, the 200,000-step run has only
four reset suffixes:

```
21$   (199,920 times)
14 21$      (40)
A 21$       (39)
22 14 21$    (1, the initial suffix)
```

Adding the token immediately left of `R` gives 11 guarded states. The automaton
is implemented in `machine14_reset_automaton.py`. Its exhaustive closure is not
closed: it produces the unobserved state

```
(g, R, s) = (2>, 214, 21$)
```

and then `2> 214` consumes the reset and loses the reset suffix. The script
reports this as `LOST_RESET_GUARD` rather than silently excluding it.

## The 214 run is not a fixed threshold invariant

The final `21$` is often preceded by a contiguous run of `214`s, but that run is
not eventually stable. Over 500,000 macro steps it first reaches length 2 at
step 15, then falls below 2 on 214 separate steps. It reaches length 0 at steps
333,953–333,954, length 1 at step 333,955, then recovers to a run of 6 by step
333,960. The maximum observed run is 6, and there is no halt.

Therefore a language requiring two consecutive `214`s before `21$`—even after a
finite transient—is false. The buffer must be represented by a counter or a
more general automaton state, not by a fixed lower bound on the contiguous run.

## Two-token guard refinement

Adding the token immediately left of the one-token guard gives states
`(g2, g, R, s)`, where `g2` is two tokens left of the reset. The run has 42
observed such states. A closure that explicitly forgets `g2` as `?` after a
one-token rule output (otherwise the closure is spuriously too small) grows to
62 states and 100 transitions, then fails at

```
(g2, g, R, s) = (A, 2>, 214, 21$)
```

Here the `2>` is immediately before the last `214`, so

```
2> 214 -> 22 14
```

destroys the reset before the `A` to its left can act. This is reported as
`LOST_G`, not converted into an invariant.

## Right-of-head suffix closure

A more structural state is `(h, s)`, where `h` is the rightmost `A`/`2>` and
`s` is the finite word strictly to its right (so `s` contains no heads). The
500,000-step run has 425,100 distinct observed `(h, s)` states; the longest
observed suffix has 40 tokens.

Two closures were checked:

- **Nondeterministic next head.** After a rule output contains no head, allow
  either `A` or `2>` as the next head. The closure reaches 1,230,948 states and
  reports a halt at `(2>, 21$)`. This is an overapproximation: the halt state is
  not reached by the actual run.
- **Opposite-head successor.** Assume the untouched left prefix is
  `(A 2>)^inf`, so the next head has the opposite type. This is false: 199,910
  of 200,043 no-head transitions violate it. Head clusters remain to the left
  (for example `A 22 -> 22 A A`), so a single head type is not enough.

The deterministic version gives a 799,917-state closure with no halt, but it is
not a valid invariant because its successor rule is refuted. The suffix-only
abstraction therefore loses the left head stack; the next model needs a
pushdown/stack of controls, not a regular suffix state.

## Status

- No sound closed invariant was found in the fixed-window family `W <= 4`.
- The observed `214` buffer is the apparent shield, but it has not been proved
  inductive.
- This is a search result for the `A/2>` abstraction, not a proof for the raw
  Turing machine.
- No Rocq theorem was produced.
- `championsReal.txt` was not modified.
