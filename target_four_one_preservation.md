# Target: the 4-1 A3 boundary and deep-shield preservation

Target: `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`.

## Formal result

`bbwork/lean/TM25.lean` now defines:

```lean
def A3MarginOne (l : List Sym) : Prop :=
  ∃ u zs, l = u ++ 4 :: 1 :: zs ∧ ∀ s ∈ u, s ≠ 1
```

and proves:

- `a3MarginOne_deep`: `A3MarginOne l -> ShieldBeforeOneDeep l`;
- `shieldDeep_cons`: `a ≠ 1 -> ShieldBeforeOneDeep l ->
  ShieldBeforeOneDeep (a :: l)`;
- `a3MarginOne_prefix`: the margin-1 shape is preserved by prepending a
  non-`1` cell;
- `a3_margin_one_cascade`: from an `A`-on-`3` with the `4 1` boundary there
  are `N`, `d` with no halt before `N`, `iter N = some d`, and
  `CascadeOver d`.

`a3_margin_one_cascade` reports only `[propext, Quot.sound]`; `shieldDeep_cons`
reports `[propext]`.  Both are checked by Lean 4.35.  There is no `sorry`.

## Finite successor check

`a3margin.exe 10000000000` follows every margin-1 A3 to the next A3:

```text
steps=10000000000 margin1=68 next=68 next_deep=68 next_margin1=52
```

Here “deep” means `d4 >= 1` and there is a genuine cell beyond the nearest
`4`.  Seven early events have `d4=1` but `pre[1]=1`, so they are deep; an
earlier counter incorrectly required `d4 >= 2` and reported them as failures.

This is finite evidence that the 4-1 boundary does not immediately destroy
the shield.  It does **not** prove that every future A3 successor is deep, nor
does it close the global nonhalting question.
