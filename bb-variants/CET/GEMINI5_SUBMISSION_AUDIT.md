# Gemini 5 submission — local Rocq 9.1 audit

Date: 2026-11-12

Status: **NOT VERIFIED**

The three files are preserved in `gemini5_incoming/`. They were compiled from
`gemini5_check/` against the verified bundle:

    rocq compile -Q CET_ARTIFACT_BUNDLE/rocq Top <FILE>.v

Rocq version:

    The Rocq Prover, version 9.1.0

No textual `admit`, `Admitted`, `Axiom`, or `Parameter` tokens were found.

## 1. CET4_R8.v

**Compile failed.**

```text
File "gemini5_check/CET4_R8.v", line 523, characters 2-38:
Error: Unable to find an instance for the variable z.
```

Line 523 is:

```coq
apply check_range_bool_sound in Hrng.
```

`check_range_bool_sound` ends in `forall z, ...`; applying it to the
hypothesis leaves `z` uninferrable. The claimed `Hfc0`/`run_N_proper` change
does not remove this earlier blocker. No `cet4_r8_halts` verification.

## 2. CET23_R8.v

**Compile failed.**

```text
File "gemini5_check/CET23_R8.v", line 290, characters 72-75:
Error:
In environment
t : BTree
p : Z
v : Sym
z : Z
n : z <> p
Heq : z_to_pos p = z_to_pos z
The term "Heq" has type "z_to_pos p = z_to_pos z"
while it is expected to have type "z_to_pos z = z_to_pos p".
```

This is the same `bt_interp_set` orientation error reported for the earlier
submission. It is still present at line 290:

```coq
apply z_to_pos_inj; exact Heq.
```

No `cet23_r8_halts` verification.

## 3. Eps1Complete.v

**Compile failed.**

First error:

```text
File "gemini5_check/Eps1Complete.v", line 113, characters 4-14:
Error: Found no subterm matching "hd bl V" in the current goal.
```

Line 113 is in `rung_reaches_copy_gen`:

```coq
rewrite HV. reflexivity.
```

After removing that unnecessary rewrite in a scratch copy, the next failure is:

```text
File "gemini5_check/Eps1Complete.v", line 137, characters 23-34:
Error: ...
Unable to unify
 "Some {| cst := WALK; clft := L; ccur := hd bl (s :: Z); crgt := tl (s :: Z) |}"
with
 "Some {| cst := WALK; clft := L; ccur := bl; crgt := s :: Z |}"
```

This is `walk_WALK_zeros` with `k = 0` and `Z = s :: Z`. Its stated result is
false for a nonempty `Z`: the initial current symbol is `bl`, while the claim
uses `hd bl Z` (which is `s`). The lemma needs a condition such as
`hd bl Z = bl`, or a corrected statement.

The later FGH theorem is therefore not established.

## Bottom line

The gemini5 submission does not compile. In particular:

- `CET4_R8.v` still fails at `check_range_bool_sound`;
- `CET23_R8.v` still has the original `bt_interp_set` orientation error;
- `Eps1Complete.v` fails at `rung_reaches_copy_gen` and its next lemma is
  actually false for arbitrary `Z`.

No records were updated and no files were added to `CET_ARTIFACT_BUNDLE`.
