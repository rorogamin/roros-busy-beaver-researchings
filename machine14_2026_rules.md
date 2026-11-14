# Machine 14 — supplied 2026 block rules

Target: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`

Source: Discord `#bb2x5`, hipparcos/dyuan01 discussion supplied by the user on 2026-11-06. These are transcriptions of the posted tables, not independently verified rules.

## Hipparcos blocks

```
L  = ^11
R  = 1$
X  = 142
Y  = 031
U  = 01
W  = 11
V  = 22
C  = 14
F  = 03
C1 = 24
C2 = 21
P  = 2
Q  = 1
```

Heads: `<`, `>`, and `w>` (`w>` is the RightWide head, `0B>`).

The block simulation starts after 14 base steps at:

```
L U Q < R
```

Hipparcos's rules:

```
W <  -> < V
U <  -> W >
> V  -> U >
L <  -> L w>
w> V -> U w>

> X  -> < C1 P
w> X -> Y w>
w> R -> < X R
Y <  -> < X

F <  -> < C
> C  -> < C1
> C1 -> < C2
> C2 -> F >

w> C  -> F Q >
w> C1 -> U Q >
w> C2 -> W w>
Q <  -> < P
w> P  -> U >
> P   -> w>
```

## First supplied table

Columns are the block read by the head. Rows are the head type.

```
|      | 22       | 14      | 24      | 21      | 214       | 224        | 221       | 21$         |
| A>   | 01 A>    | <A 24   | <A 21   | 03 A>   | 03 1 A>   | 01 1 A>    | 11 A> 2>  | <A 14 21$   |
| 2>   | 22 2>    | 214     | 224     | 221     | 22 14     | 22 24      | 22 21     | ---         |
```

Left-moving `<A` table; these columns are the block to the left of the head.

```
|      | 01     | 11    | 03     | 1      | ^11         |
| <A   | 11 A>  | <A 22 | <A 14  | <A 2>  | ^11 A> 2>   |
```

Start:

```
^11 01 <A 21$
```

## Regrouped `A = [<A^-1 A>]` table

```
|      | 22      | 14   | 24   | 21   | 214       | 224         | 221        | 21$      |
| A    | 22 A A  | 24   | 21   | 14 A | 14 2> A   | 22 A 2> A   | 22 A 2>    | 14 21$   |
| 2>   | 22 2>   | 214  | 224  | 221  | 22 14     | 22 24       | 22 21      | ---      |
```

Start:

```
(A 2>)^inf 22 14 21$
```

## Status

- The table transcribes the missing 2026 information.
- A rightmost-head block simulation with a finite 10-pair left stack ran 20,000 macro steps without `2> 21$`; this is only an experiment.
- The hipparcos single-head model was implemented in `machine14_block_rules.py`. It reproduces the posted early trace and ran 1,000,000 macro steps with no stuck head (`machine14_block_rules_1m.json`).

## Partition invariant for the single-head block model

At the start `L U Q < R`, the left side is
`{L,U,W,F,Y,Q}` and the right side is `{R,X,V,C,C1,C2,P}`.

Every hipparcos rule preserves that split:

- `<` reads a left block. Its rule either keeps/replaces a left block or removes it and writes only right blocks; the next `<` reads the preceding left block.
- `>`/`w>` read a right block. Their rules either keep/replace right blocks or move a block to the left side; the next head still reads a right block.
- `L` is never removed, and `w> R -> < X R` keeps `R`, so both sides remain nonempty.
- Every rule has a defined output for its allowed block; there is no halting rule in this model.

This proves nonhalting for the **block abstraction**. It is not yet a proof for the raw machine: each macro rule still has to be shown to be a finite raw-machine simulation, starting from the concrete 14-step prefix. That finite simulation/case analysis is the remaining Rocq obligation.
