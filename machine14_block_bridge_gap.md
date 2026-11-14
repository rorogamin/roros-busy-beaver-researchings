# Machine 14: gap-aware raw-to-block bridge test

Machine: `1RB2LA0RB4LB1RA_1LA3RA1RA---0LA`.

## Why a gap is needed

The block model in `machine14_block_rules.py` encodes tokens as strings:

```text
L=11  R=1   X=142  Y=031  U=01  W=11  V=22
C=14  F=03  C1=24  C2=21  P=2   Q=1
```

A direct concatenation of the blocks works for the first two macro rules but
fails at `> P -> w>`: the raw tape is `111101`, not `11111`. The extra `0` is
a blank cell at the head boundary. The correct reading is therefore

```text
raw = enc(left blocks) + 0^gap + enc(right blocks),   gap in {0,1}
```

with the head at:

- the last cell of the left block for `<` (state A);
- the first cell of the right block for `>` (state A);
- the first cell of the right block for `w>` (state B).

The starting raw configuration is the configuration after 14 ordinary steps:
`110111`, head offset 4, state A, gap 0. This is exactly `L U Q < R`.

## Reproducible test

```bash
cd bbwork
py -3.14 machine14_block_bridge_gap.py --steps 5000
```

The script starts the raw machine at step 14, applies one block rule at a time,
and requires a **unique exact raw endpoint** for each macro step. It fails on
a missing or ambiguous endpoint.

Result from `machine14_block_bridge_gap.json`:

```text
block_steps:                 5000
raw_steps:                   12119
rules_seen / expected:       19 / 19
missing rules:               none
gap counts:                  0 -> 4855, 1 -> 145
max raw steps per macro:     6
initial raw:                 110111, head offset 4, state A
```

All rule pairs that occur in the model were exercised:

```text
<:F  <:L  <:Q  <:U  <:W  <:Y
>:C  >:C1 >:C2 >:P  >:V  >:X
w>:C w>:C1 w>:C2 w>:P w>:R w>:V w>:X
```

## What this establishes

- The direct no-gap encoding is wrong at `> P`.
- With an explicit boundary gap, the raw machine exactly follows the block
  model for 5,000 macro steps, including every one of the 19 rule pairs.
- The block model does not get stuck on this trajectory.
- Gaps observed on this trajectory are only 0 or 1.

## What the Python test alone does not establish

- It is a **finite empirical bridge test**, not a Rocq theorem.
- It does not prove that every reachable block context has a matching raw
  endpoint; the gap choice was selected by exact endpoint matching.
- It does not prove the gap transition rule, locality, or the partition
  invariant for arbitrary contexts.
- It is **not** a nonhalting proof for machine 14.

A formal proof would need:

1. a deterministic gap transition function derived from the raw rules;
2. a locality lemma showing each macro rule reads/writes only its finite
   neighbourhood;
3. an induction over block steps connecting the raw run to the block run;
4. a proof that the block model is total on every reachable configuration.

Until those exist, the block model should be described as a validated
abstraction on the tested trajectory, not as a certificate.

## Formal status (2026-11-08)

`bbwork/lean/Machine14Bridge.lean` now proves the finite raw-to-block bridge
for the two-sided block language, not merely the tested trajectory.  The raw
encoding is deterministic:

- gap `0` for `<` and `>`;
- gap `1` for `w>`;
- `rawLeft` is the nearest-first concatenation of each block's reversed digits.

The checked theorems are:

- `rawOf_init`: the encoding of `initB` is exactly `initRaw`.
- `rawOf_stepB`: for every `Inv2` block state and every defined `stepB s = some s'`,
  there is `k ≤ 6` with `rawRunK k (rawOf s) = some (rawOf s')`.
- `rawOf_runB`: every defined stage of `runB` has a raw run from `rawOf initB`.
- `rawRun_bridges_runB`: every defined block stage is reached by the actual
  `rawRun` from `rawStart` after the 14-step prefix plus a finite macro run.

`#print axioms` reports only `propext` for `rawOf_stepB`, `rawOf_runB`, and
`rawRun_bridges_runB`; `rawOf_init` uses no axioms.  The proof is checked by:

```text
LEAN_PATH=. lean Machine14Bridge.lean
```

This closes the local raw macro bridge for the two-sided language.  It is not
a nonhalting proof: `stepB` still has no rule for `>` reading `R`, and the
formal theorem is conditional on the block run remaining defined.
