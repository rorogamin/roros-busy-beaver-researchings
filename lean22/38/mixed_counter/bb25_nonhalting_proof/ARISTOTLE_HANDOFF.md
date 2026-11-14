# Formalization handoff

Target machine: `1RB2LA0RB1LA3LB_1LA3LB1RA4RA---`.

This is a plan for formalizing the complete argument in `NONHALTING_PROOF.md`, not a claim that the new lemmas already compile. No new Lean file or new kernel-checked theorem is included in this package.

## Existing interfaces to reuse

The uploaded project supplies:

- `TM25.ACfg`, `TM25.astep`, `TM25.arun`, `TM25.conc` in `Closed.lean`.
- `TM25.astart`, `TM25.AReach`, `TM25.arun_sound`, `TM25.halts_iff_ahalt`, and `TM25.not_halts_of_never` in `Reduction.lean`.
- The blank-tape bootstrap `TM25.start_21` in `Rules.lean`.
- Composition of abstract runs via `arun_add` and the existing sweep/carry lemmas.

It is preferable to add a module for the whole mixed counter, rather than continue strengthening clean-prefix estimates in the older reduction. The key is that `D` divides remaining capacity by two.

## 1. Mixed left counter

Define structurally on `List LB`, nearest head first:

```
K []       = 0
K (U :: l) = 2 * K l + 1
K (W :: l) = 2 * K l
K (D :: l) = K l / 2
```

The saturation image is also structural, but appends on the right:

```
Phi []       = []
Phi (U :: l) = Phi l ++ [V]
Phi (W :: l) = Phi l ++ [V]
Phi (D :: l) = Phi l ++ [if K l % 2 = 0 then C else C1]
```

Prove two operational statements, for every arbitrary right suffix `rs`:

1. If `0 < K l`, there are `l'` and `t > 0` with
   `arun t <l,lt,rs> = some <l',gt,rs>`,
   `K l' + 1 = K l`, and `Phi l' = Phi l`.
2. If `K l = 0`, there is `t >= 0` with
   `arun t <l,lt,rs> = some <[],lt,Phi l ++ rs>`.

The second permits `t=0` when `l=[]`. The first always has positive time. In the `D` branch of the first theorem use the theorem for the shorter tail twice. In the `D` branch of the second theorem split `K tail` into 0 and 1. Keep the saturation-image equality in the induction hypothesis; it is what avoids reconstructing all the mixed digits later.

An optional functional implementation of a multi-increment operation can recurse structurally on the list with an arbitrary request `n`:

```
consume [] n: succeeds iff n=0
consume (U :: l) n: recurse into l with n/2;
                     output U if n is even, W if n is odd
consume (W :: l) n: recurse into l with (n+1)/2;
                     output U if n+1 is even, W otherwise
consume (D :: l) n: recurse into l with 2*n; retain D
```

Then success is equivalent to `n <= K l`, the new capacity is `K l - n`, and the saturation image is unchanged. This avoids defining a doubly recursive `I(D::l)=D::I(I(l))` directly.

## 2. Cascade arithmetic and emitted image

Use a three-letter reset-body type, or a predicate restricting `List RB` to `V`, `C`, `C1`. Do not confuse block digits `C/C1` with raw tape symbols 0/1.

Define the scan with height `Int`, debt `Nat`, promotion count `Nat`, and output word. Updates are exactly the table in Section 3 of the proof. The output at `C` depends on the *incoming* debt parity. Define normalized debt with rational powers of two, or work throughout with scaled integer inequalities.

Generalize the local wide-zero lemma to arbitrary left words with `K l >= 6`. Its operation is six applications of the mixed-left lemma followed by insertion of `D`. Similarly, the wide-one lemma needs only `K l >= 1`. No parity restriction on a clean left counter is needed.

Prove the cascade theorem carrying these simultaneous facts:

- every consumed prefix has exact capacity `2^h - 1 - x`;
- the left saturation image is the emitted scan word;
- the head is `wgt` and the unconsumed right suffix is unchanged;
- the computation has finite abstract length.

First prove this under explicit local capacity preconditions. Separately prove that final normalized debt at most `1/256` implies every local precondition, using prefix monotonicity. This avoids a circular operational proof.

## 3. Right counter and exact reset return

Prove complete right returns at a fixed left boundary on pure binary right words with tail `[]` or `[P,Q]`. The integer enumeration is

```
F = R + (2+j)*2^n - 2
j=0 for [], j=1 for [P,Q].
```

A complete right return adds one to `F` and leaves the old left word unchanged. Temporary `D`s from a carry must be flushed before declaring the return complete.

Handle `C G G` by the six explicit returns in the proof, after which the right word is `C C C` with empty tail. Combine right returns with the mixed-left theorem to make `K m` whole cycles and then take the zero-capacity saturation step.

The exact return theorem should use a *positive* existential step count:

```
w = u ++ [C1]
H = h w
z = x u
N = H-3
d = z-9
```

Under safe-cascade preconditions, `2^(H-1)-z-2 >= 6`, and `0 <= d < 2^N`, prove

```
exists t > 0,
  arun t (reset w) = some (reset (image u ++ complementBits d N)).
```

For Lean's natural subtraction, explicitly carry `z >= 9` and `H >= 3` where needed. The closed invariant gives much stronger lower bounds. The bootstrap cases also satisfy these domain conditions by computation.

The seven-step bottom lemma is independent of the arbitrary residual left word and can be proved by direct reduction.

## 4. Pure arithmetic invariant

Define `GoodReset w` as the conjunction:

```
countV w = countC w + countC1 w + 2
trailingOnes w >= 6
promotions w >= 3
normalizedDebt w <= 1/256
```

Prove the following algebraic lemmas independently of the TM:

1. Normalized debt is nondecreasing under every appended source letter.
2. `height (image a) = height a + 2 * promotions a`.
3. If `p=0`, output debt is zero and source debt is even. If `p>0`, output debt is at most `4^(p-1)` times source debt.
4. The suffix-cost recurrence `tau` satisfies `tau d <= 8*d+2`.
5. Reading a finite padded complemented bitword adds at most `tau d` units of initial-height-scaled normalized debt.
6. The successor has normalized debt at most `3/8` times the input's debt.
7. Six trailing ones give `d % 32 = 21`; the successor suffix starts `01010`, forcing at least three promotions.
8. The count excess and at least six trailing ones are preserved.

The universal reset theorem then supplies `GoodReset w -> exists t>0, ... GoodReset w'`.

## 5. Bootstrap and final theorem

Encode reset 8 as `V^6 ++ [C1,C,C1,C1]`. Direct reduction gives

```
arun 504 astart = some (reset w8).
```

Use the general reset theorem four times, checking the small finite inputs by decision procedures, to reach the 50-letter seed printed in the proof. Its invariant is a finite calculation. This avoids asking Lean to normalize more than eighteen million individual block steps.

Finally use the standard progress-invariant lemma: if every state satisfying an invariant makes a positive finite run to another state satisfying it, no such state can halt at finite time. Prove this by strong induction on a putative halting time, or by constructing arbitrarily long abstract runs. Include the finite bootstrap and transfer to `not_halts_of_never` / the concrete machine semantics.

## Important audit points

The exact map removes only the *last* input `C1` before taking the emitted image. Its parameters are `N=H-3` and `d=z-9`, not a clean-counter deficit from the old analysis. The promotion count is the number of source `C` letters read at even debt, not the total number of zeros or ones. The normalized-debt estimate is a prefix-safety certificate; a bound on final capacity alone would not suffice.
