# A closed reset invariant for a mixed-digit shift-overflow counter

## Result and verification status

The following argument proves nonhalting, from the blank tape in state A, of

```
1RB2LA0RB1LA3LB_1LA3LB1RA4RA---
```

The new result is a mathematical proof using the block semantics in the supplied Aristotle project. **This document is not a Lean-checked extension of that project.** The accompanying Python program checks the finite bootstrap, the arithmetic, and many instances of the identities independently; those finite tests are not being substituted for the universal proof below.

The essential new idea is to assign an exact remaining capacity to the *whole* mixed left word, including every buried `D`. This produces an exact reset-to-reset map and an invariant under which normalized debt decreases by a factor of at least 3/8 at every reset.

## 1. Machine and block conventions

The transition table is:

| State | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| A | 1RB | 2LA | 0RB | 1LA | 3LB |
| B | 1LA | 3LB | 1RA | 4RA | halt |

Use the uploaded project's blocks:

- Left: `U=01`, `W=11`, `D=04`.
- Right: `V=22`, `C=13`, `C1=23`, `G=33`, `P=2`, `Q=1`, `S=3`.
- The left boundary is an infinite blank region followed by `11`.
- `<`, `>`, `w>`, and `lB` are the project's heads `lt`, `gt`, `wgt`, and `lB`.

In a *reset word* write `0` for the block `C`, and `1` for the block `C1`. These are not individual tape symbols. The right word is read from the head toward the right. In recursive left-word formulas the first block is nearest the head, as in `ACfg.bs`.

Write

\[
\mathcal R(w)=\langle [],<,wPQ\rangle,
\qquad w\in\{V,0,1\}^*.
\]

The suffix `PQ` will be implicit in reset words. One block step changes the head at this reset from `<` to `w>`.

For reference, the complete block rules needed here are the following. In these displayed local rewrites, ordinary tape order is used.

```
L <       -> L w>
W <       -> < V
U <       -> W >
D <       -> < C

> []      -> < P Q
> V       -> U >
> C       -> < C1
> C1      -> D >
> G       -> < C
> P       -> w>
> S       -> < Q
> Q       -> < P

w> []     -> lB G
w> V      -> U w>
w> C      -> < C S
w> C1     -> < P V
w> G      -> < C Q
w> P      -> U >
w> S      -> D >
w> Q      -> < C

U lB      -> < C
W lB      -> lB G
D lB      -> halt
L lB      -> the proved left-end nonhalting loop
```

These are `TM25.astep` in `RequestProject/Closed.lean`. The supplied `start_21`, `arun_sound`, and `halts_iff_ahalt` link this system to the original machine. The proof below constructs infinitely many finite sequences of `.next` steps; in particular it never uses a halting or loop step as an ordinary transition.

## 2. The whole mixed left word has an exact capacity

Define a nonnegative integer on nearest-head-first left words:

\[
K(\epsilon)=0,\qquad
K(U\ell)=2K(\ell)+1,\qquad
K(W\ell)=2K(\ell),\qquad
K(D\ell)=\left\lfloor K(\ell)/2\right\rfloor.
\tag{1}
\]

For a fixed right suffix, let a *complete left excursion* start with head `<` and end with head `>` at the same boundary, leaving that suffix unchanged and without reaching the left end. Let \(I(\ell)\) denote its resulting left word when it exists.

**Mixed-left lemma.** Such an excursion exists if and only if \(K(\ell)>0\). It is finite and safe, and

\[
K(I(\ell))=K(\ell)-1.
\tag{2}
\]

More explicitly,

\[
I(U\ell)=W\ell,\qquad
I(W\ell)=U I(\ell),\qquad
I(D\ell)=D I^2(\ell).
\tag{3}
\]

The second formula is valid when \(K(\ell)\ge1\), and the third when \(K(\ell)\ge2\).

To see the third formula, `D <` first produces `< C`. One excursion into the remaining left word returns to `> C`, which changes to `< C1`. A second left excursion returns to `> C1`, which reinstates `D` and moves right. Thus a parked `D` doubles the increment demand on the remaining left word. Formula (1), not a clean-prefix binary capacity, is the correct capacity for arbitrary buried `D` blocks. The `U` and `W` cases follow directly from their sweep rules. This is a structural induction on the left word and proves finiteness as well as the numerical assertions.

### 2.1 The saturation image

Define \(\Phi(\ell)\) by scanning a left word in *physical order*, from the left boundary toward the head, starting with \(c=0\):

| Left block | Output | New c |
|---|---|---|
| U | V | 2c+1 |
| W | V | 2c |
| D | the digit c mod 2 | floor(c/2) |

At the end, \(c=K(\ell)\). Every successful left excursion preserves this image:

\[
\Phi(I(\ell))=\Phi(\ell).
\tag{4}
\]

In the `U` and `W` cases the affected outer output is simply `V`. In the `D` case the inner capacity changes by two, so the output parity at that `D` is unchanged. This proves (4) by the same structural induction as (3).

When \(K(\ell)=0\), the next left excursion reaches the left end and places precisely \(\Phi(\ell)\) before the unchanged right suffix. For `W` this follows from the sweep rule. For `D`, the inner capacity is either 0 or 1: respectively the excursion leaves `C`, or makes one successful inner return and leaves `C1` before overflowing. Those are exactly the parity outputs in the table.

Consequently, after exactly \(K(\ell)\) complete left excursions, the following one reaches the left end and emits \(\Phi(\ell)\). All these excursions are finite and safe. This is the saturation law we will use to skip an entire steady phase, not merely its clean binary prefix.

## 3. A debt transducer for the wide cascade

Suppose a wide head encounters a reset-body letter and the current mixed-left capacity is \(E\). The exact actions are:

| Letter | Left-word action | New E | Required E |
|---|---|---|---|
| V | append U next to head | 2E+1 | E >= 0 |
| 1 | one complete left excursion; append U | 2E-1 | E >= 1 |
| 0 | six complete left excursions; append D | floor((E-6)/2) | E >= 6 |

For `1`, use `w> C1 -> < P V`, one left return, and `> P V -> w> V -> U w>`.

For `0`, `w> C` creates `< C S`. Two left excursions change this to `< C Q`; two more change it to `< C P`; two more finish at `D w>`. In detail, each pair passes through `> C1`, temporarily parks a `D`, and either flushes it back to `C` after the marker is rewritten, or retains it at the final `> P`. Thus six excursions are sufficient for an arbitrary mixed left word, with no clean-prefix assumption.

Define \(h(w)\), \(x(w)\), and an emitted word \(\mathcal P(w)\) by scanning from initial \(h=x=0\):

| Read | New h | New x | Emitted letter |
|---|---|---|---|
| V | h+1 | 2x | V |
| 1 | h+1 | 2x+2 | V |
| 0 | h-1 | floor(x/2)+3 | 1 when incoming x is even, otherwise 0 |

Let \(p(w)\) be the number of source zeros for which the incoming debt is even. Equivalently, \(p(w)\) is the number of `1` letters in \(\mathcal P(w)\). The letter-by-letter definition makes sense for every finite word, even if it is not a valid cascade.

Whenever the cascade has been valid up to a prefix, its exact capacity is

\[
E=2^h-1-x.
\tag{5}
\]

The capacity transformations prove (5) inductively. The emitted word is the saturation image of the left word constructed so far: a `V` or `1` appends `U` after zero or one image-preserving excursions; a `0` appends `D` after six image-preserving excursions. Its emitted digit is the old capacity modulo two, namely \(1-(x\bmod2)\), at a valid zero step.

### 3.1 A global bound certifies all local preconditions

For every word define its normalized debt

\[
\mu(w)=\frac{x(w)}{2^{h(w)}}.
\tag{6}
\]

Allow integer heights and dyadic denominators for this auxiliary definition. During a scan, normalized debt is nondecreasing. A `V` leaves it unchanged. At incoming height \(h\), a `1` increases it by \(2^{-h}\); a `0` increases it by

\[
\bigl(6-(x\bmod2)\bigr)2^{-h}.
\tag{7}
\]

**Safe-cascade lemma.** If \(\mu(w)\le1/256\), every letter of the wide cascade through \(w\) is valid.

Indeed, the same bound holds for every prefix. Immediately after a `1`, the debt is at least 2, so the new height is at least 9. The incoming height is at least 8 and (5) gives incoming capacity at least

\[
(255/256)2^8-1=254\ge1.
\]

Immediately after a `0`, the debt is at least 3, so the new height is at least 10. Its incoming height is at least 11, and incoming capacity is at least

\[
(255/256)2^{11}-1=2039\ge6.
\]

The argument is inductive: `V` steps are always valid; the inequalities supply the necessary precondition at every other step and then preserve (5). The heights actually encountered in a valid scan are nonnegative. Thus there is no circular assumption of cascade validity and no unexamined prefix-overflow case.

## 4. The exact reset-to-reset map

Suppose \(w=u1\), its cascade is safe, and set

\[
H=h(w),\qquad z=x(u),\qquad N=H-3,\qquad d=z-9.
\tag{8}
\]

Assume also

\[
K_m:=2^{H-1}-z-2\ge6,
\qquad 0\le d<2^N.
\tag{9}
\]

The claim is an exact finite safe return

\[
\boxed{
\mathcal R(w)\ \longrightarrow^+\
\mathcal R\!\left(\mathcal P(u)\,
\overline{\operatorname{bits}_N(d)}\right).
}
\tag{10}
\]

Here \(\operatorname{bits}_N(d)\) lists the \(N\) binary digits least-significant first, with high zero padding; the bar complements every bit. This is a genuine orbit identity, not an asymptotic approximation.

### 4.1 The bottom is safe

The last `1` of the cascade appends `U`. In nearest-first notation the left word is therefore `U :: m`. At the bottom the following seven block steps hold, with the suffix `m` unchanged:

```
(U :: m,       w>, P Q)
(U :: U :: m,   >, Q)
(U :: U :: m,   <, P)
(W :: U :: m,   >, P)
(W :: U :: m,  w>, [])
(W :: U :: m,  lB, G)
(U :: m,      lB, G G)
(m,            <, C G G)
```

In particular `lB` sees `W` followed by `U`, never `D`. If the left word just before the last `1` was \(\ell\), then \(m=I(\ell)\). Equations (4) and (5) give

\[
\Phi(m)=\mathcal P(u),\qquad
K(m)=2^{H-1}-z-2=K_m.
\tag{11}
\]

### 4.2 The right counter after the bottom

A *complete right excursion* starts at `>` and returns to `<` at the same boundary without entering the old left word. On a binary word of length \(n\), with least-significant-first value \(R\), and final suffix either `[]` or `PQ`, define

\[
F=R+(2+j)2^n-2,
\qquad
j=0\text{ for []},\quad j=1\text{ for PQ}.
\tag{12}
\]

Every complete right excursion is finite and safe and increases \(F\) by one. A run of `1`s is carried by parking `D`s; they are flushed back into zero digits before the excursion re-enters the old left word. At the far end the only possibilities are `> [] -> < PQ` and `> PQ -> w> Q -> < C`, both safe. Formula (12) includes these changes of representation.

The normalized binary words and two tails are uniquely enumerated by the integers \(F\ge0\). At fixed \(n\), the two consecutive intervals are

\[
[2^{n+1}-2,\,3\cdot2^n-3]
\quad\hbox{and}\quad
[3\cdot2^n-2,\,4\cdot2^n-3].
\]

The initial word `C G G` has \(F=8\), interpreting `G` provisionally as the digit -1. More directly, six right excursions give

```
0 G G -> 1 G G -> 0 0 G -> 1 0 G
      -> 0 1 G -> 1 1 G -> 0 0 0,
```

with empty far-right tail. Thereafter the right word is normalized and has \(F=14\).

Alternate \(K_m\) complete left excursions and right excursions, beginning at `m < C G G`. Every pair decreases left capacity by one and increases \(F\) by one, leaving the left saturation image unchanged. By (9), all the `G`s have disappeared before the left word saturates. The next left excursion reaches the left end and emits \(\Phi(m)\).

The right counter at that point has

\[
F=8+K_m=2^{H-1}-z+6.
\tag{13}
\]

Putting \(N=H-3\) and \(d=z-9\) gives

\[
F=(2^N-1-d)+3\cdot2^N-2.
\]

By (9) and uniqueness of (12), its tail is `PQ`, and its \(N\) binary digits have value \(2^N-1-d\): precisely the complemented digits in (10). This proves the full return identity, including the constants 8, 9, and 3.

## 5. The closed invariant

For a reset word \(w\), impose the four conditions

\[
\boxed{
\begin{aligned}
\#V(w)-\#0(w)-\#1(w)&=2,\
w&\text{ ends in at least six 1s},\
p(w)&\ge3,\
\mu(w)&\le1/256.
\end{aligned}}
\tag{14}
\]

We prove that (10) is well-defined, safe, and preserves all four conditions.

### 5.1 Domain and trailing ones

Let \(b=\#1(w)\). The count condition gives

\[
H=\#V+b-\#0=2+2b\ge14.
\tag{15}
\]

Write \(w=u1\). Since \(u\) ends in at least five ones, iterating \(x\mapsto2x+2\) gives \(z=x(u)\ge62\), hence \(d=z-9\ge53\).

Also

\[
\mu(w)=\frac{2z+2}{2^H}
       =\frac{z+1}{2^{H-1}}\le\frac1{256}.
\]

Therefore

\[
0\le d<2^{H-9}=2^{N-6}.
\tag{16}
\]

This proves the required bound \(d<2^N\), and the six most significant bits in the padded \(N\)-bit expansion of \(d\) are zero. Its complement ends in at least six ones. The same bound gives

\[
K_m\ge2^{H-1}-2^{H-9}-1\ge8159>6.
\]

Section 3.1 supplies all cascade preconditions, so (10) is valid.

### 5.2 The count condition

Write \(v=\#V(w)\), \(a=\#0(w)\), and \(b=\#1(w)\). The emitted prefix \(\mathcal P(u)\) contains \(v+b-1\) copies of `V` and \(a\) digit letters. The appended suffix has

\[
N=v+b-a-3
\]

digits. Thus the successor's excess of `V`s over digits is

\[
(v+b-1)-(a+N)=2.
\tag{17}
\]

### 5.3 Three new even-debt zero events are forced

If \(w\) ends in \(1^k\), \(k\ge6\), then for some nonnegative integer \(x_0\),

\[
z=(x_0+2)2^{k-1}-2,
\qquad
 d=(x_0+2)2^{k-1}-11\equiv21\pmod{32}.
\tag{18}
\]

The first five letters of the appended complemented suffix are consequently

```
01010
```

The emitted prefix \(\mathcal P(u)\) ends in `V`, because \(u\) ends in `1`. Its debt is therefore even. The first zero in `01010` is read at even debt. Each of the other two zeros immediately follows a `1`, whose update \(x\mapsto2x+2\) again makes the debt even. Thus the successor has at least three source-zero events counted by \(p\):

\[
p(\mathcal T(w))\ge3.
\tag{19}
\]

This is the regeneration mechanism: the three events needed for contraction are recreated by every return.

## 6. The contraction estimate

Two elementary estimates finish the invariant proof.

### 6.1 The emitted prefix attenuates inherited debt

For any source word \(a\), put

\[
x=x(a),\quad p=p(a),\quad y=x(\mathcal P(a)).
\]

Then

\[
h(\mathcal P(a))=h(a)+2p.
\tag{20}
\]

Moreover,

\[
\begin{cases}
y=0\text{ and }x\text{ is even},&p=0,\\[2mm]
y\le4^{p-1}x,&p\ge1.
\end{cases}
\tag{21}
\]

This is an induction on source letters. Before the first source zero all source letters are `V` or `1`, so \(x\) is even and the entire output consists of `V`s. The first zero is therefore counted by \(p\), and changes output debt to 2 while source debt becomes at least 3.

Afterward, write \(m=4^{p-1}\). A source `V` doubles both debts. A source `1` doubles the output debt while changing source debt to \(2x+2\). At a source zero with even \(x\), the new output is `1`: output debt changes to \(2y+2\), source debt to \(x/2+3\), and \(m\) changes to \(4m\), so the inequality persists. At a source zero with odd \(x\), the output is `0`, and both debts take the map \(t\mapsto\lfloor t/2\rfloor+3\). For odd \(x=2r+1\),

\[
\left\lfloor y/2\right\rfloor+3
\le mr+\lfloor m/2\rfloor+3
\le m(r+3).
\]

The last inequality holds for every integer \(m\ge1\). This proves (21). Equation (20) follows immediately by counting: each counted zero changes a height decrement in the source into a height increment in the output.

### 6.2 Cost of the complemented binary suffix

Let \(\tau(d)\) bound the normalized debt added by reading the complemented binary expansion of \(d\), followed by infinitely many padding ones, in units of the initial height. The one-letter increments (7) give the recurrence

\[
\tau(0)=2,\qquad
\tau(2n)=1+\tfrac12\tau(n)\ (n\ge1),\qquad
\tau(2n+1)=6+2\tau(n).
\tag{22}
\]

For \(d=0\), all letters are ones and the total is \(1+1/2+1/4+\cdots=2\). For positive even \(d\), its low complemented digit is 1, costing one unit and doubling the height scale for the remaining digits. For odd \(d\), that digit is zero, costing at most six units and halving the height scale. The actual zero cost is sometimes five; using six is an upper bound.

Induction gives

\[
\tau(d)\le8d+2\qquad(d\ge0).
\tag{23}
\]

Indeed, the odd case gives equality in this upper estimate; the positive even case gives the stronger bound \(4n+2\le16n+2\). Any finite padded suffix is bounded by the infinite one because every normalized increment is nonnegative.

### 6.3 Combining the estimates

Use \(w=u1\), \(z=x(u)\), \(p=p(w)=p(u)\), and \(d=z-9\). Let \(y=x(\mathcal P(u))\). By (20), the starting height of the appended suffix is \(H-1+2p\). Equations (21) and (23) imply

\[
\begin{aligned}
\mu(\mathcal T(w))
&\le \frac{y+\tau(d)}{2^{H-1+2p}}\\
&\le \frac{4^{p-1}z+8(z-9)+2}{4^p2^{H-1}}\\
&=\frac{(4^{p-1}+8)z-70}{4^p2^{H-1}}\\
&\le\left(\frac14+\frac8{4^p}\right)
        \frac{z}{2^{H-1}}\\
&\le\frac38\,\mu(w),
\end{aligned}
\tag{24}
\]

because \(p\ge3\) and \(\mu(w)=(z+1)/2^{H-1}\). In particular the successor again has normalized debt at most \(1/256\).

Together, (16), (17), (19), and (24) prove that (14) is a closed invariant of exact, finite, safe reset returns.

## 7. A reachable seed satisfies the invariant

The invariant is not asserted for the early startup. A finite bootstrap reaches a suitable seed.

From the blank tape the machine reaches the supplied `astart` after 21 raw steps. From `astart`, 504 block steps reach

```
w8 = VVVVVV1011
```

with empty left word, head `<`, and tail `PQ`. The accompanying verifier checks every one of these 504 block steps against the raw machine; the total raw time is 1094 steps.

Apply (10) four times. All local cascade preconditions and both conditions (9) are checked as finite integer calculations, independently of the later invariant. The relevant values are:

| Reset | H | x(w) | p(w) | Trailing ones | z | d | N |
|---|---:|---:|---:|---:|---:|---:|---:|
| 8 | 8 | 22 | 1 | 2 | 10 | 1 | 5 |
| 9 | 12 | 110 | 1 | 4 | 54 | 45 | 9 |
| 10 | 14 | 126 | 3 | 3 | 62 | 53 | 11 |
| 11 | 22 | 1406 | 4 | 5 | 702 | 693 | 19 |
| 12 | 36 | 1106942 | 6 | 9 | 553470 | 553461 | 33 |

The seed body at reset 12 is exactly

```
VVVVVVVVVVVVVVVV1VVVV1V1V10VVVV0101001010111111111
```

Its length is 50; it has 26 `V`s, 7 zeros, and 17 ones. Consequently

\[
\#V-\#0-\#1=26-7-17=2,
\qquad h=36,
\qquad p=6.
\]

It ends in nine ones, and

\[
\mu=\frac{1106942}{2^{36}}
    =\frac{553471}{34359738368}
    <\frac1{256}.
\tag{25}
\]

Thus it satisfies every clause of (14). The seed also agrees with an independent run of the uploaded C block accelerator: reset 12 occurs at block step 18,416,173, counted from `astart`, and has exactly this body followed by `PQ`.

For reproducibility, the Python verifier checks the mixed capacity and saturation-image identities on 3,280 mixed left words, the image estimate on 29,524 source words, the tail-cost estimate on 65,536 integers, and the invariant returns through reset 22. It also verifies the raw startup correspondence and the exact arithmetic bootstrap above. These checks are supplementary evidence and debugging checks; the induction in Sections 2-6 is the proof for all lengths and all subsequent resets.

## 8. Nonhalting

Starting at the reachable reset-12 seed, apply the invariant theorem repeatedly. Each application gives a finite, positive-length block computation to another reset satisfying the same invariant. Every step on every such segment is a `.next` step, including the only `lB` cleanup, which encounters `W` then `U` and is safe.

The concatenated computation therefore contains arbitrarily many block steps without halting. Block-step soundness gives positive finite raw computations for these steps. Together with the finite blank-tape bootstrap, this proves

\[
\boxed{
\neg\operatorname{Halts}
\bigl(1RB2LA0RB1LA3LB\_1LA3LB1RA4RA---\bigr).
}
\]

The remaining implementation task for Aristotle is to formalize the mixed-left lemma, the exact reset-return theorem, and preservation of (14). No unproved asymptotic claim, empirical growth assumption, clean-prefix assumption, or conjectured avoidance of the dangerous pattern remains in the mathematical argument.
