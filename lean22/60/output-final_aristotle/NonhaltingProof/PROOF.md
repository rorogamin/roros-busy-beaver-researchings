# A finite-rectangle nonhalting proof for the BB(2,5) fractal

**Machine:** `1RB2LA3LB4LB---_0LA4LB3RA4LA0RB`.

**Conclusion:** the machine started in state A on the all-zero tape never takes its A4 halting transition. In the supplied Lean model, this is `forall n, not (Halted (run n))`.

**Validation status:** this document gives the complete mathematical induction and its connection to ordinary execution. `proof.py` implements the construction, without orbit sampling, and checks instantiated rectangles directly against the transition table. A second, separately coded whole-block interpreter checks their outer specifications. No Lean, Lake, or Rocq compiler was available here. This is not a claim of a kernel-checked completion of `NonHalting.lean`; the original file and its admitted theorem are unchanged.

The missing idea is to prove two parameterized finite rectangle families simultaneously. Their composition gives an echo; a cut of that echo defines the next transient prefix. The transient prefixes need no guessed closed formula.

## 1. Finite longitudinal rectangles

Use the boundary alphabet

\[
a=(A,B),\qquad b=(B,B),\qquad c=(A,A).
\]

A letter records entry into a region from its right, and the state of the eventual exit back to its right. At its left boundary, the same letter describes an excursion requested from the neighboring region: departure in its first state, return in its second state.

For a single cell, a **finite conditional history** consists of its initial symbol, a finite right-input word, a finite left-output word, and its final symbol. Interpret each right letter by actually running the TM at that cell. Whenever it steps left, consume the next left letter, check the departure state, and supply that letter's stated return. Whenever it steps right, check the requested right-exit state. Every transition must be nonhalting; all words must be consumed exactly.

A finite rectangle is a list of such neighboring cell histories with equal shared boundary words. We write

\[
[S]\quad R\longrightarrow L\quad[T]
\]

for a rectangle with initial tape word S, final tape word T, right boundary R, and left boundary L. Tape words, cells, and internal boundaries are ordered **from right to left**. The notation includes the existence of the internal boundary words, not just an unverified pair of outer words.

These are conditional histories, not an assertion that an arbitrary exterior supplies the left word. We will only use their ordinary-execution consequences before the actual head crosses the exposed left boundary.

### Composition rules

Spatial composition identifies a shared history:

\[
[S]\ R\to M\ [S'],\quad [T]\ M\to L\ [T']
\quad\Longrightarrow\quad
[ST]\ R\to L\ [S'T'].
\]

Temporal composition concatenates histories when the intermediate tapes match:

\[
[S]\ R_1\to L_1\ [T],\quad [T]\ R_2\to L_2\ [U]
\quad\Longrightarrow\quad
[S]\ R_1R_2\to L_1L_2\ [U].
\]

A rectangle can be cut at any internal boundary. These facts follow directly from its list of cell histories. Equivalently, spatial composition executes matching nested calls: a caller is suspended while its left neighbor runs, and resumes in exactly the state written on their shared boundary. The finite words determine finite conditional executions; no infinite-return hypothesis is involved.

Write

\[
Z_\ell(R,L):=[0^\ell]\ R\to L\ [1^\ell].
\]

## 2. Elementary single-cell histories

The following are sufficient; no claim that they enumerate every conceivable boundary description is needed.

| Initial symbol | Right input | Left output | Final symbol |
|---:|:---:|:---|---:|
| 0 | a | empty | 1 |
| 0 | b | a^k c, any k >= 0 | 1 |
| 1 | a | cba | 0 |
| 1 | b | b | 0 |
| 1 | c | a | 3 |
| 3 | a | b | 0 |
| 3 | b | a | 0 |

For example, the second row repeats B0 with returns in B exactly k times, then returns in A and takes A0. Its left letters are `a^k c`, and its eventual right exit is B. For the third row the local transitions are A1, A2, B3, B4, with the intervening left letters c, b, a. Every row is verified in the same way against the nine nonhalting transitions.

Define the three words

\[
D=cab,\qquad E=cba,\qquad F=bca.
\]

Several immediate consequences will be used repeatedly:

\[
[1]\ aa\to E\ [1],\qquad
[1]\ E\to aa\ [1],\qquad
[1]\ b\to b\ [0].
\]

In particular, for every positive length \(\ell\),

\[
[1^\ell]\ b\to b\ [0^\ell]. \tag{B}
\]

For a cell initially containing 1, one D produces

\[
[1]\ D\to ab\,a^k c\ [1].
\]

Choose the displayed k for the first D and zero for subsequent copies. For m >= 1 this gives

\[
[1]\ E^jD^mE^s
\to a^{2j+1}b\,a^kD^{m-1}c\,a^{2s}\ [1]. \tag{C}
\]

Here the word identity \(c(abc)^t=D^t c\) accounts for the displayed form.

### An odd all-ones wall

For every odd \(\ell=2h+1\), every m >= 1, q >= h, and k >= 0,

\[
[1^\ell]\ D^mE^q
\longrightarrow
 a^\ell b\,a^kD^{m-1}c\,a^{2q-\ell+1}\ [1^\ell]. \tag{U}
\]

Here is a direct proof that also specifies all its internal boundaries. For j=0,...,h-1, a pair of 1-cells transforms

\[
E^jD^mE^{q-j}
\longrightarrow
E^{j+1}D^mE^{q-j-1}.
\]

The intermediate boundary between those two cells is

\[
a^{2j+1}bD^{m-1}c\,a^{2(q-j)}.
\]

The first cell uses (C) with k=0. In the second cell, the initial \(a^{2j+1}\) emits \(E^{j+1}\) and leaves symbol 0; b emits c and restores symbol 1; the remaining letters emit \(D^mE^{q-j-1}\) after concatenation. The condition q-j >= 1 is exactly what supplies the two final a's needed for this return to symbol 1.

After h such pairs the history is \(E^hD^mE^{q-h}\). Apply (C) to the final cell, now using the requested k. This proves (U), including the endpoint tape. The limiting case h=0 is just (C) with j=0.

## 3. The two simultaneous induction assertions

For rank r >= 1, put

\[
n=3^r,\qquad d=2^r,\qquad w=n-d,\qquad M=d/2.
\]

Thus n and w are positive odd integers, d is even, and M >= 1. Define

\[
\Theta(m,k)=
\begin{cases}
\varepsilon,&m=0,\\
a^kD^m,&m\ge1.
\end{cases}
\]

We construct a finite word P=P_r for which BOTH of the following hold for **every** m,q,k >= 0:

### Reset rectangle R_r(m,q,k)

\[
\boxed{
Z_d\left(
 P F^m a^{d+1+2q},\quad
 a^kD^{M-1+m}c\,a^{2q+2}
\right).
} \tag{R_r}
\]

### Triangle rectangle T_r(m,q,k)

\[
\boxed{
Z_w\left(
 aD^{M-1+m}c\,a^{w+1+2q},\quad
 P\Theta(m,k)E^q
\right).
} \tag{T_r}
\]

The parameter m changes the length of the periodic part; q supplies finite trailing context; k is the exposed B0 return count. When m=0 in the triangle, k is intentionally irrelevant.

### Derived echo and the next prefix

Given R_r and T_r, specialize the reset to

\[
(m,q,k)=\left(0,(w-1)/2,1\right).
\]

Its right boundary is \(Pa^n\); its left boundary is

\[
aD^{M-1}c\,a^{w+1}.
\]

That is exactly the right boundary of T_r(0,0,0). Spatial composition gives

\[
\boxed{Z_n(Pa^n,P).} \tag{Echo_r}
\]

This echo has a finite witness with n+1 boundary words. Cut it after the first w cells, and call the shared word H=H_r. We therefore have

\[
X_r:=Z_w(Pa^n,H),\qquad
Y_r:=Z_d(H,P). \tag{XY}
\]

Define, once and for all for this rank,

\[
\boxed{P_{r+1}=H_r\,b\,P_r.} \tag{P}
\]

H is cut from an already constructed finite echo. It is not read from an assumed future orbit, and it is fixed independently of the parameters m,q,k in the next rank. The dependencies are well-founded: R_r and T_r give Echo_r and H_r, which give the single word P_(r+1), after which we prove R_(r+1) and T_(r+1).

## 4. Base rank

Take

\[
n=3,\quad d=2,\quad w=1,\quad M=1,\quad P_1=ab.
\]

For R_1 the two cell histories have the three boundaries

\[
abF^m a^{3+2q},\qquad
bD^mE^{q+1},\qquad
 a^kD^mc\,a^{2q+2}.
\]

Both cells start at 0 and end at 1. The first consumes ab, emitting b and returning to 0. Each subsequent F on symbol 0 emits D and returns to 0, using zero repeated B0 returns. The remaining odd run of a's emits E^(q+1) and leaves symbol 1. In the second cell the first b emits a^k c and leaves symbol 1; the D's use zero repeated B0 returns; and the E's emit pairs of a's. Thus R_1 holds for all parameters.

For T_1 we need the one-cell relation

\[
[0]\ aD^mc\,a^{2+2q}
\longrightarrow ab\Theta(m,k)E^q\ [1].
\]

The first a changes 0 to 1 and emits nothing. If m=0, the following `caa` emits `ab` and returns the cell to 1. If m>=1, the first D emits `ab a^k c`, the remaining D's use zero repeated B0 returns, and the final `caa` emits `ab`. Together these give `ab a^k D^m`. Each remaining pair `aa` emits E and preserves symbol 1. This proves T_1 in both cases.

The derived first echo has boundaries

\[
abaaa\ \to\ bcba\ \to\ acaa\ \to\ ab.
\]

Hence H_1=bcba and P_2=bcbabab, as a first check of the recursion.

## 5. Induction step for the reset

Assume R_r and T_r for P, with n,d,w,M as above. The derived Echo_r, X_r and Y_r are now available. Set

\[
P'=HbP,\quad n'=3n,\quad d'=2d,\quad
w'=2w+n,\quad M'=d=2M.
\]

Fix arbitrary m,q,k >= 0. We must construct R_(r+1):

\[
Z_{2d}\left(P'F^ma^{2d+1+2q},\
 a^kD^{2M-1+m}c\,a^{2q+2}\right).
\]

Partition the 2d cells into two d-cell blocks.

### First d-cell block

In temporal succession apply:

1. Y_r: H -> P, changing 0^d to 1^d.
2. (B): b -> b, resetting 1^d to 0^d.
3. R_r(m,q+M,0).

The total input is the required \(HbPF^ma^{2d+1+2q}\), and the output is

\[
P bD^{M-1+m}c\,a^{d+2+2q}.
\]

Use the exact word identity

\[
bD^jca=F^{j+1}
\]

to rewrite this as

\[
P F^{M+m}a^{d+1+2q}. \tag{R-mid}
\]

The final tape of this block is 1^d.

### Second d-cell block

Apply R_r(M+m,q,k) to (R-mid). Its output is

\[
a^kD^{M-1+(M+m)}c\,a^{2q+2}
= a^kD^{2M-1+m}c\,a^{2q+2}.
\]

Its final tape is also 1^d. Spatial composition proves R_(r+1) for all m,q,k.

## 6. Induction step for the triangle

Fix m,q,k >= 0. The desired right boundary is

\[
aD^{2M-1+m}c\,a^{2w+n+1+2q}.
\]

Partition the w'=2w+n cells into blocks of widths

\[
\boxed{w\ \mid\ n\ \mid\ w.}
\]

### First w-cell block

Use

\[
T_r(M+m,\ n-M+q,\ n).
\]

Its input is exactly the required boundary because

\[
w+1+2(n-M+q)=2w+n+1+2q.
\]

Since M+m >= 1, its output is

\[
P a^nD^{M+m}E^{n-M+q}. \tag{T-mid1}
\]

It ends with tape 1^w.

### Middle n-cell block

First use Echo_r on the prefix Pa^n, emitting P and changing 0^n to 1^n. Then apply the odd wall (U) to

\[
D^{M+m}E^{n-M+q},
\]

with wall length n and k=1. Its parameter requirement holds because

\[
n-M+q-\frac{n-1}{2}=\frac{w+1}{2}+q\ge0.
\]

The total output of the middle block is

\[
P a^n b aD^{M+m-1}c\,a^{w+1+2q}. \tag{T-mid2}
\]

The exponent follows from

\[
2(n-M+q)-n+1=w+1+2q.
\]

This block ends with tape 1^n.

### Last w-cell block

Apply, in temporal succession:

1. X_r to Pa^n, emitting H and changing 0^w to 1^w.
2. (B) to b, emitting b and resetting the tape to 0^w.
3. T_r(m,q,k) to the remaining word
   \(aD^{M-1+m}c\,a^{w+1+2q}\).

Its output is

\[
H bP\Theta(m,k)E^q=P'\Theta(m,k)E^q,
\]

and it ends with tape 1^w. This proves T_(r+1).

The base rank and these two induction steps establish R_r and T_r, with finite internal witnesses, for **every rank r >= 1**. All subsidiary parameters in the construction are nonnegative. No rank-dependent return-count conjecture remains to be assumed.

## 7. The actual right-hand driver

We now connect these rectangles to the blank-tape computation, rather than to an arbitrary oracle.

Let u=042, and consider a right excursion starting on the leftmost displayed cell with blank tape farther right. Stop at its first step left of that region. For all j >= 0:

| Entry and tape | Left exit and resulting tape | Steps |
|---|---|---:|
| A, u^j | A, 2u^j | 6j+3 |
| B, 2u^j | B, 42u^j | 6j+5 |
| B, 42u^j | A, u^(j+1) | 6j+7 |

For the first rule, j=0 is A0, B0, A1. For j+1, cross the leading 042 rightward in three steps, changing it to 103; apply the induction hypothesis to the remaining u^j; then cross the leading 103 leftward in three steps, changing it to 204. The output is `204 2u^j = 2u^(j+1)`. The second rule is B2, then the first rule, then A3. The third is B4, then the second rule, then B0. This proves the rules and their nonhalting/first-left-exit conditions for all j.

Starting on the entirely blank tape at cell 0, the first visit to the nonpositive half-line is the letter a: A0 writes 1 and exits right in B. The B0 transition at cell 1 immediately returns in A, leaving the positive half-line blank. Thereafter the three right-excursion rules accept exits A,B,B and supply the next entries A,B,A respectively. Consequently the right side realizes the conditional input driver

\[
\boxed{aD^\omega=a(cab)^\omega}
\]

for the initially all-zero cells 0,-1,-2,... . Equivalently, after the first two ordinary steps, the first cell is 1 and the driver is D^omega, as in the earlier analysis.

This says that whenever the left side returns in the prescribed state, the next right excursion is a finite nonhalting computation supplying the next prescribed entry. It does not assume in advance that all left-side visits return.

## 8. Finite-prefix safety and nonhalting

### Finite-prefix safety lemma

Suppose a finite rectangle covers cells 0,-1,...,-(w-1), with their correct initial symbols. Suppose its right-input word agrees with the actual realizable right driver for its first L letters. Then the ordinary machine cannot halt before either:

- it first crosses left of the rectangle; or
- it starts a right-input visit beyond those L matching letters.

To prove the lemma, follow the actual individual TM steps. Keep, for each currently active visit, its place in the prescribed single-cell history. A leftward step into an internal neighbor suspends its caller; the next shared boundary letter supplies exactly the neighbor's entry and its prescribed return. The neighbor's actual cell symbol is the one obtained from its previous completed visits. Thus ordinary execution agrees with the certified local transitions for as long as it stays inside the stated domain. Every such transition is nonhalting. Right excursions between visits are nonhalting by the driver realization. The only unaccounted left-return state would be beyond the exposed left boundary, and the argument stops before using it.

This is a finite-step induction, not a fairness assumption about an infinite reordered computation.

### Apply the all-rank triangles

Take T_r(0,0,0). It is

\[
Z_w\left(aD^{M-1}c\,a^{w+1},\ P_r\right),
\qquad w=3^r-2^r,\quad M=2^{r-1}.
\]

Its right boundary agrees with \(aD^\omega\) for at least its first

\[
L=3M
\]

letters: these are \(aD^{M-1}ca\). Both w and L tend to infinity with r.

Suppose the actual machine halted after h ordinary steps. Choose r with w>h and L>h+1. The head, which starts at cell 0 and moves at most one cell per step, cannot yet have crossed left of the width-w rectangle. At most h+1 right-input visits can have started by that time, so the matching right prefix has not been exhausted either. Finite-prefix safety contradicts the alleged halt.

Therefore

\[
\boxed{\forall h\ge0,\ \text{the blank-tape computation has not halted at time }h.}
\]

In the supplied Lean semantics, all constructed local transitions avoid A4, so the absorbing H state is never reached.

## 9. Why this closes the earlier gap

The previous target asked for unbounded compatible strips but had no recurrence for their transient prefixes. The new recursion obtains H_r by cutting a finite echo, and then defines P_(r+1)=H_r b P_r. The reset supplies exactly the context needed to produce the echo; the triangle uses that echo twice with an odd all-ones wall between them. The two induction steps close simultaneously.

The construction starts directly from the blank tape. It does not use `orbitWord`, the unsatisfiable fixed-right-edge closure premise, or the admitted Lean theorem. It does not assume that a large sample of crossing histories continues forever. Only finite rectangles enter the final safety argument.

## 10. Executed checks and reproduction

`proof.py` contains a recursive construction, plus a direct single-cell interpreter of the original transition table. The construction does not read a simulated orbit or the earlier prefix records. Its only fixed prefix is P_1=ab; every later prefix is produced by the echo cut.

The executed tests in `verification.json` include:

- Echoes and triangles at every rank 1 through 7.
- 270 additional reset/triangle instances, spanning ranks 1 through 5 and independently varying m,q,k.
- Three deliberately corrupted histories, all rejected.

At rank 7, the constructed echo has width 2,187 and its cell histories contain 10,382,801 local TM transitions. The triangle has width 2,059 and contains 9,579,955 local TM transitions. These are conditional-execution counts, **not claims about the blank orbit's elapsed time**.

`audit.py` uses a separately coded whole-block TM interpreter. It ignores all intermediate boundary words and checks the starting tape, outer words, ending tape, and transition count. It passed 64 cases totaling 136,696 transitions, and all 303 finite right-engine checks (three phases for j=0,...,100). The six recursively obtained prefixes P_1,...,P_6 were separately compared with the earlier archive and agree exactly.

Run with Python 3.10 or later, using only its standard library:

```bash
python test_proof.py
python audit.py
python proof.py --rank 7 --kind triangle
python proof.py --rank 5 --kind reset --m 2 --q 3 --k 4
python proof.py --check rank7_triangle.json
```

The all-rank theorem follows from Sections 4-6 and the safety argument, not from the number of finite cases checked. The tests audit the explicit construction and its implementation. Kernel-checked translation remains unperformed; `FORMALIZATION.md` gives a concrete route into the supplied Lean project.
