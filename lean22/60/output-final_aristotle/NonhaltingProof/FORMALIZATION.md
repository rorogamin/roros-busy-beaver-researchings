# Formalization handoff

## What is and is not finished

`PROOF.md` contains the mathematical proof, including the closed simultaneous induction and the finite-prefix soundness argument. `proof.py` is a constructive witness generator and executable checker, not a Lean proof. The original `RequestProject/NonHalting.lean` is deliberately unchanged. No claim is made that its `sorry` has been eliminated or that `lake build` has succeeded for a new proof.

The first file to read is `PROOF.md`, not the older fixed-window reduction. The new argument starts directly on the blank tape and does not use `orbitWord`, `MacroClosed`, or the admitted `never_halts` theorem.

## Suggested minimal interface

Import `RequestProject.Machine` and introduce a three-letter type:

```text
Cross.a = (A,B)
Cross.b = (B,B)
Cross.c = (A,A)
```

Lists are preferable to streams: the proof needs only finite rectangles and a finite-prefix safety theorem.

A convenient syntactic relation is

```text
Cell : Sym -> List Cross -> List Cross -> Sym -> Prop
```

with an empty-history constructor, temporal composition, and the seven single-visit constructors from Section 2 of `PROOF.md`. These are an inductively defined relation, NOT axioms about the machine. Prove their microstep soundness from `Machine.step`. In particular, the zero-cell b constructor has the arbitrary finite output `a^k ++ [c]`; its correctness follows by induction on k.

Define finite rectangles by spatial concatenation of cells:

```text
Rect : List Sym -> List Cross -> List Cross -> List Sym -> Prop

Rect.empty W : Rect [] W W []
Rect.cons : Cell s R M t -> Rect ss M L ts -> Rect (s::ss) R L (t::ts)
```

The lists of tape cells are ordered RIGHT TO LEFT. Prove spatial append, temporal append, and spatial cut. The cut lemma must return the common finite boundary word H, with both component rectangles. No guessed formula for H is needed.

Use `Z length R L` as an abbreviation for a rectangle from `replicate length 0` to `replicate length 1`.

## The finite lemmas to prove

Use D=cab, E=cba, F=bca.

1. `ones_b`: `[1^l] b -> b [0^l]`.
2. `ones_wall`: for odd l=2h+1, m>=1, q>=h,
   `[1^l] D^m E^q -> a^l b a^k D^(m-1)c a^(2q-l+1) [1^l]`.
3. The base reset with its explicit two-cell witness:
   `ab F^m a^(3+2q) -> b D^m E^(q+1) -> a^k D^m c a^(2q+2)`.
4. The base triangle with its explicit one-cell witness.

For the wall, use the two-cell identity in `PROOF.md`; it avoids a complex induction over a long ordinary run.

## State the induction existentially

There is no need to define a dependent recursive Lean function for P_r. Prove that for every rank there EXISTS a word P satisfying both parameterized families, each universally quantified over m,q,k.

Given such a P, derive the echo `Z n (P ++ a^n) P`, cut it at width w, obtain H, and use `H ++ [b] ++ P` as the existential witness at the next rank. The cut is of a rectangle already proved at the old rank, not an assumed future orbit.

The constructions are exactly:

```text
E_r = spatial(R_r(0,(w-1)/2,1), T_r(0,0,0))
X_r = first w cells of E_r
Y_r = last d cells of E_r
P_next = H ++ b ++ P

R_next(m,q,k) = spatial(
    temporal(Y_r, ones_b(d), R_r(m,q+M,0)),
    R_r(m+M,q,k))

T_next(m,q,k) = spatial(
    T_r(M+m,n-M+q,n),
    temporal(E_r, ones_wall(n,M+m,n-M+q,1)),
    temporal(X_r, ones_b(w), T_r(m,q,k)))
```

The exact word conjugacy used in the reset is

```text
b (cab)^j c a = (bca)^(j+1).
```

In the triangle the only wall side condition is

```text
n-M+q >= (n-1)/2,
```

which follows from n=w+2M and positive odd w.

### Keep the arithmetic simple

Instead of repeatedly normalizing natural subtraction and division in powers, the induction can carry dimensions recursively:

```text
(n,d,w,M) starts at (3,2,1,1)
(n,d,w,M) -> (3n,2d,2w+n,2M)
```

Preserve `n=w+d`, `d=2M`, and oddness/positivity of n,w. Use an explicit h with w=2h+1 in the echo specialization. The formulas n=3^r and d=2^r can be proved afterwards; the nonhalting argument only needs w and M unbounded. Each is at least its rank index, which is a simpler adequate lower bound.

## Connect to the actual machine

Prove the three parametric right-excursion rules from Section 7. Alternatively adapt already verified right-engine lemmas, after checking their orientations and blank-exterior conditions. The actual right-input driver is `a(cab)^omega` when all cells start at 0. It is `(cab)^omega` only AFTER the first two ordinary steps, when the first cell already contains 1. Do not mix these two starting conventions.

The finite-prefix safety lemma should be stated in ordinary TM semantics. Keep a stack, or equivalent local-history cursors, of suspended visits. A crossing to an internal left neighbor matches the next shared boundary pair. A crossing beyond the exposed left edge is where the guarantee stops: never assume its oracle return is physically supplied.

A sufficient form is:

```text
A width-w finite rectangle starting with the correct all-zero tape,
whose right word agrees with a(cab)^omega for L letters,
excludes a halt at every time h with h < w and h+1 < L.
```

Then use the proved instance T_r(0,0,0), for which w=3^r-2^r and L=3*2^(r-1) are unbounded.

Do not formalize progress as merely `exists c, step^[n] init = c`: that is vacuous in the supplied total-step model with absorbing H. The conclusion needed here is that every covered ordinary transition avoids A4, hence H cannot have been reached.

## Final audit

Prove a new theorem, e.g. `fractal_never_halts`, from `Machine` and the new finite-rectangle development, without importing the admitted theorem as a dependency. Then replace the existing `never_halts` proof with that theorem once the build succeeds. Run `#print axioms` on the final result and inspect for `sorryAx` or any machine-specific assumed theorem. No such formal build or axiom audit has been performed in this package.
