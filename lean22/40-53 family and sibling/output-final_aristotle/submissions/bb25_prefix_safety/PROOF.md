# A prefix-safety proof for the 3RA and 2LA members

Date: 2026-09-16.

## Status and claim

This document gives a mathematical nonhalting argument for

```
1RB2LA0RB1LB---_1LA3RA1RA4LB3RA
1RB2LA0RB1LB---_1LA3RA1RA4LB2LA
```

It uses the transition rules and counter/transparent-pair results in the
supplied Aristotle development. The new invariant, return lemma, and final
nonhalting conclusions have **not been compiled or kernel-checked in Lean in
this session**. They should receive independent mathematical and formal
checking. The accompanying Python checks are finite consistency tests, not
the proof of an infinite run.

The argument is not a continuation of the scalar `rcost <= 1/2` invariant.
Instead it compares two values at **every prefix of the left stack**. The
comparison is preserved by borrowing, and the two selected B4 rules restore
it after the potentially dangerous F/G event.

## 1. Conventions and established machine facts

Use the supplied blocks, but write a left stack **bottom first**, omitting its
permanent bottom block `L = ^11`:

- Left `X = 11` is bit 0, `Z = 01` is bit 1, and `W = 03` is a pop/shift.
- Right `Y = 22`, `V = 21`, and `X = 11` are the three digit blocks used below.
- `R = $`, `R1 = 1$`, and `P2 = 2>`.
- `B` below denotes the archive's marker `<B1`, not merely a bare B head.

The counter value is the left-to-right fold

\[
v(\epsilon)=0,\quad v(sX)=2v(s),\quad
v(sZ)=2v(s)+1,\quad v(sW)=\lfloor v(s)/2\rfloor.
\]

A stack is *admissible* if every prefix has at least as many bit blocks
`X,Z` as pop blocks `W`. Match each `W` to the most recent unmatched bit.
Its unmatched bits, in order, are the binary expansion carrying `v(s)`;
leading zero bits are allowed.

Let `D(s)` be the result of a successful left counter excursion. On an
admissible stack with positive value it subtracts one from the unmatched
binary numeral, changes no matched bit, and leaves the shape unchanged.
This is the paired-block version of `cdec`, justified by the archive's
transparent-pair rules and counter decrement theorem.

Define a decoder `P(s)` in tape order as follows:

* Every bit block, whether `X` or `Z`, emits `Y`.
* A `W` matched to an `X` emits `X`.
* A `W` matched to a `Z` emits `V`.

Consequently `P(s)` is a colored Dyck prefix: `Y` opens, while `X,V` close.
For every prefix `u` of `s`, `P(u)` is the corresponding prefix of `P(s)`.

Two consequences of transparent pairing are important:

1. If `v(s)>0`, then `P(D(s))=P(s)`.
2. If `v(s)=0`, then a leftward excursion through `s` reaches the left end
   and deposits exactly `P(s)` on the right, without changing the suffix
   already to the right of the head.

For the second statement, all final unmatched bits are zero; matched groups
are transparent, and each unmatched zero deposits `Y`. This also gives a
direct proof by decomposing the stack into matched groups and unmatched bits.

Relevant existing source files are `Pairing.lean`, `Counter.lean`,
`Overflow.lean`, `Family.lean`, and `Blocks.lean`. In particular,
`transparent_nil`, `Transparent.wrapX`, `Transparent.wrapZ`,
`Transparent.append`, `brun_cdec`, and `brun_overflow_word` supply the
machine-level facts behind these descriptions.

## 2. Remove the pending-digit phase from reset arithmetic

Let the physical reset counter be `f`. Define its adjusted value by

\[
a=f\quad\text{with pending }2>,\qquad
a=f-1\quad\text{with pending }1>.
\]

The subtraction charges the pending decrement immediately. In this adjusted
coordinate the reset maps are

\[
Y:a\mapsto 2a+1,\qquad V:a\mapsto 2a,\qquad
X:a\mapsto\lfloor a/2\rfloor-1. \tag{1}
\]

These formulas follow directly from `resetStep` in `Counter.lean`. In
particular, the final subtraction after an `X` is essential.

Write `rho(w)` for the composition of (1) on a word `w`, starting at 0.
Use integer arithmetic here, so that a negative result records an unpaid
borrow rather than silently truncating subtraction. Say a word is *clean*
if the adjusted value is nonnegative after every prefix. All three maps
preserve the negative integers, so a nonnegative final value also implies
cleanliness for these three-letter words.

For a clean word define its *paid reset stack* `T(w)` by

\[
T(\epsilon)=\epsilon,\qquad
T(wY)=T(w)Z,\qquad T(wV)=T(w)X,\qquad
T(wX)=D(T(w)W). \tag{2}
\]

The last operation is legal because a clean `X` requires the preceding
adjusted counter to be at least 2. Its pop leaves a positive counter on which
the charged decrement can be paid. Also, a nonempty clean paid reset stack
has at least one unmatched bit: a legal `X` cannot pop the last unmatched bit,
since a one-bit counter has value at most 1.

Equation (2) describes the left-stack effect, not a claim that the physical
head has the same position after every charged prefix. Payment of a pending
1 is made during the next turning operation. At the endpoints used below:

- A clean reset of `wR` ends at a B boundary with stack `T(w)` and counter
  `rho(w)`; the last pending debt is paid by the right-end turn when needed.
- A clean reset of `wR1` with final letter `Y` ends with pending 2, then parses
  `P2 R1 = V R`. It therefore appends `W` to `T(w)` and arrives at `A> R`.

These statements are also obtainable by composing the archive's individual
reset rules. They do not assume the reset will survive a zero-value B event;
we explicitly require a positive value whenever we use the first endpoint.

## 3. The new prefix invariant

For an admissible stack set

\[
b(s)=\rho(P(s)).
\]

Call a stack *good* when

\[
\boxed{\quad b(u)\ge v(u)\quad\text{for every prefix }u\preceq s.\quad} \tag{G}
\]

Admissibility is part of the definition of good. This is not merely the
single inequality `b(s) >= v(s)` at the full stack.

### Lemma 1: borrowing preserves goodness

If `s` is good and `v(s)>0`, then `D(s)` is good.

**Proof.** A decrement changes only the final unmatched bits, hence preserves
all matched labels and every decoded prefix. For every fixed prefix `u`, its
counter value cannot increase. To see the latter explicitly, the leftmost
changed unmatched bit changes from 1 to 0; any subsequent changes in that
prefix turn a subset of lower zero bits into ones. The loss at the first bit
strictly dominates those lower gains. Prefixes preceding that bit are
unchanged. Thus every left side of (G) is unchanged and every right side
weakly decreases. QED.

Appending either bit `X` or `Z` also preserves goodness, since the new
comparison is respectively

\[
2b(s)+1\ge2v(s),\qquad 2b(s)+1\ge2v(s)+1.
\]

### Lemma 2: every clean paid reset creates a good stack

If `w` is clean, then `T(w)` is good and `v(T(w))=rho(w)`.

**Proof.** Induct using (2). The bit cases follow above. In the `X` case,
write `a=v(T(w))` and `b=b(T(w))`, so `b>=a>=2`.
After appending `W`, the new decoder letter is `X` if `a` is even and `V` if
`a` is odd. The decrement in (2) does not change that matched label.
The new full-stack comparisons are

\[
\lfloor b/2\rfloor-1\ge\lfloor a/2\rfloor-1
\quad(a\text{ even}),
\]

and

\[
2b\ge\lfloor a/2\rfloor-1
\quad(a\text{ odd}).
\]

All older prefix inequalities persist because the decrement cannot increase
any prefix counter. The value formula is exactly (1). QED.

A useful related consequence is: if `s` is good and `v(s)>=d>=2`, then

\[
D^d(s)W\quad\text{is good}. \tag{3}
\]

Indeed, at the new pop the counter is `a=v(s)-d`, while the decoder value is
still at least `v(s)>=a+2`. This pays the possible one-unit deficit from an
`X`-colored closing pop. Appending `Z` after any successful decrements is
always good as well.

## 4. A small structural lemma for the exceptional early reset

During a paid reset of `w`, the decoder of the new stack is a transduced word
`Q(w)`. Read `w` with adjusted counter `a`:

\[
Y\mapsto Y,\qquad V\mapsto Y,\qquad
X\mapsto\begin{cases}V,&a\text{ odd before the }X,\\X,&a\text{ even before the }X.\end{cases} \tag{4}
\]

For clean `w`, equations (2) and matching show

\[
P(T(w))=Q(w). \tag{5}
\]

### Lemma 3: a completed matched group increases the second counter

Let `d` be a nonempty colored Dyck word, with `Y` opening and `X,V` closing.
For the transduction (4), starting the second adjusted counter at any
`c>=0`, its output word is clean from that value and finishes at least at

\[
\boxed{4c+2.} \tag{6}
\]

The decisions in (4) may be made from any integer first-counter starting
value; the bound is independent of that value.

**Proof.** Induct on balanced forests and their trees. For a tree `Y e V`,
the opening sends the second counter to `2c+1`; the interior never decreases
it, and the final original `V` emits `Y`. The final value is at least
`4c+3`.

For a tree `Y e X`, if the first counter is odd at the final `X`, the output
letter is `V`, giving at least `2(2c+1)=4c+2`.

If that first counter is even, the interior `e` cannot be empty: immediately
after the initial `Y` the first counter is odd. The induction hypothesis for
a nonempty interior gives a second-counter value at least
`4(2c+1)+2=8c+6`. The emitted final `X` therefore leaves at least
`floor((8c+6)/2)-1=4c+2`, with no underflow. Concatenation of nonempty trees
preserves the bound and cleanliness. QED.

Every Dyck prefix decomposes into balanced forests separated by its unmatched
`Y` letters. Thus its transduced word is clean from 0, and if it contains any
completed pair, its transduced value is at least 2.

In particular, if `u` is a **nonempty** Dyck prefix, is clean, and
`rho(u)=0`, then

\[
\rho(Q(u))\ge2. \tag{7}
\]

There must be a completed pair, since otherwise `u=Y^n` with `n>0`, whose
value is `2^n-1>0`.

## 5. A protected right-end drain

Call an `A> R` configuration *strong* if its left stack `s` is good and

\[
\boxed{b(s)+2\ge4(v(s)+1).} \tag{S}
\]

### Lemma 4: a strong right-end configuration returns safely to a good B boundary

At `A> R`, the right end first supplies `V` and turns left. If `v(s)>0`,
the machine performs one decrement and then consumes that `V`, appending
`W`. Thus a drain round is

\[
s\longmapsto D(s)W,\qquad v' =\lfloor(v-1)/2\rfloor.
\]

Put `u=v+1`, `c=b+2`. If `u` is even, the popped bit of `D(s)` is zero,
so the new decoder letter is `X` and

\[
u'=u/2,\qquad c'=\lfloor c/2\rfloor.
\]

If `u` is odd (and `v>0`, hence `u>=3`), the popped bit is one, giving

\[
u'=\lfloor u/2\rfloor,\qquad c'=2c-2.
\]

In either case `c>=4u` implies `c'>=4u'`. All old prefix inequalities
survive borrowing, and the new final comparison follows from
`b'=c'-2>=4v'+2>=v'`. Thus goodness and (S) persist.

The natural number `v` strictly decreases, so eventually `v=0`. At that
point (S) gives `b>=2`. The next left excursion deposits

\[
P(s)V R.
\]

The word `P(s)` is clean by goodness, and its final appended `V` makes the
adjusted reset value `2b>=4`. Lemma 2 now gives a good B boundary with
positive counter. All the intermediate runs are finite and avoid F/G.
QED.

### Lemma 5: the pending-2 tail creates a strong configuration

Suppose `s` is good and the head is at

\[
s\ A>\ P2\,Y^r R1,\qquad r\ge1.
\]

The tail pushes `r` one bits and then uses `P2 R1 = V R`, popping the last
one bit. Before that last pop the values are

\[
a=2^r(v(s)+1)-1,\qquad B=2^r(b(s)+1)-1.
\]

The last popped bit is one, so the decoder appends `V`. At the resulting
`A> R`,

\[
v'=2^{r-1}(v(s)+1)-1,\qquad b'=2^{r+1}(b(s)+1)-2.
\]

Goodness is preserved and

\[
b'+2\ge 2^{r+1}(v(s)+1)=4(v'+1).
\]

Therefore Lemma 4 applies. More generally, a clean reset of an odd-terminal
word `wR1` ending in `Y` has the same property: its paid reset stack is good,
its last bit is one, and the final pop establishes (S).

## 6. The B-boundary return theorem

A *safe checkpoint* is

\[
L\,s\ <B1\ Y R1,
\qquad s\text{ good},\quad v(s)\ge1. \tag{B}
\]

### Theorem: for 3RA and 2LA, every safe checkpoint returns to another safe checkpoint or enters a nonhalting spinout

First let B strip `k` top zero bits. Each such step removes an `X` and
prepends a `Y` to the right. Truncation preserves goodness. Since the original
counter was positive, the first nonzero-bit/pop encountered is `Z` or `W`,
not the bottom. Put `r=k+1>=1`, and call the remaining stack below this
block `s`.

**Case Z.** The supplied block rule gives

\[
s\ <A\ X\,P2\,Y^r R1.
\]

Crossing that initial `X` uses two counter decrements and appends `W`.
If `v(s)>=2`, the resulting stack is good by (3), and the head reaches the
tail of Lemma 5. If `v(s)=0` or `1`, it instead overflows with residual digit
respectively `X` or `V`; these early overflows are treated below.

**Case W.** Before removing `W` the counter is positive, so its underlying
stack has value at least 2. The rule creates

\[
s\ <A\ F\,Y^r R1.
\]

Two successful decrements suffice to reach `A> G`. Thus no pending digit
can reach F or G. At that point the member-specific rule erases G:

\[
\begin{array}{c|c|c}
\text{member}&A>G\text{ becomes}&\text{total effect on underlying stack if completed}\\
\hline
3RA&<A\ X\,P2&D^4(s)W\\
2LA&<A\ Y\,P2&D^3(s)Z.
\end{array}
\]

These are exactly the archive's `3RA` and `2LA` G rules, including the
turning decrements before the emitted digit is consumed. When the indicated
decrements finish, the result is good by (3) or the bit-append lemma, and
Lemma 5 applies. Otherwise all F/G blocks have **already been erased** before
the early overflow.

The only early-overflow forms in either case are therefore

\[
s_0\ <A\ d\,P2\,Y^r R1,
\qquad v(s_0)=0,\quad s_0\text{ good},\quad
 d\in\{X,V,Y\},\ r\ge1. \tag{8}
\]

There are no additional low-counter cases: after a Z the residual digit is
X or V; after W in 3RA it is X or V after the first two successful
decrements; after W in 2LA it is Y after those two decrements.

### All early-overflow cases

Put `u=P(s_0)`, so `u` is a clean Dyck prefix and `B=rho(u)>=0`.
The overflow and the pure re-parsing `P2 Y^r R1 = Y^r V R` give the
canonical even-terminal reset word

\[
u\,d\,Y^r V R. \tag{9}
\]

If `d=Y` or `V`, or if `d=X` and `B>=2`, the whole reset word is clean.
Its last `Y^r V` makes its final adjusted value at least 2. Lemma 2 gives
a safe checkpoint.

Only `d=X` and `B` equal to 0 or 1 remain.

If `u` is empty, (9) starts `X Y`. This is a nonhalting left spinout.
Indeed, for every symbol suffix `t`, the base machine has the exact run

\[
([1,1],A,L,[1,1,2,2]+t)
\ \xrightarrow{9}\
([1,1],A,L,[1,1,2,2,2]+t). \tag{10}
\]

It repeats forever. It does not depend on B4. A Lean proof of this local
identity and its iteration is included in `PrefixSafetySeed.lean` (not
compiled here); the identity was also checked directly in the base simulator.

Now assume `u` is nonempty. Reset `u`, and write `t=T(u)` and `q=P(t)`.
The stack `t` is good, has value `B` equal to 0 or 1, and has an unmatched
bit. Consuming the next `X` first appends `W`, leaving value zero and pending
1. The attempted turn on the following `Y` therefore overflows.

If `B=1`, that added W closes a one bit, so `P(tW)=qV` and its reset value
is at least 2, since `rho(q)>=v(t)=1`.

If `B=0`, the added W closes a zero bit. Lemma 3, applied to the nonempty
Dyck prefix `u` of value zero, gives `rho(q)>=2`. Therefore

\[
\rho(P(tW))=\rho(qX)=\lfloor\rho(q)/2\rfloor-1\ge0.
\]

In both cases `tW` is good: all old prefix comparisons were good, and its
new full-stack counter value is zero with a nonnegative decoded value.

After this additional overflow the right-hand tape re-parses exactly as

\[
P(tW)\,Y^{r+1} R1. \tag{11}
\]

For clarity, before re-parsing its suffix is
`Y P2 Y^(r-1) V R`, whose raw symbols are precisely
`2^(2r+2) 1`; thus (11) is an identity of tape contents, not a guessed macro
rule. This is a clean odd-terminal reset word ending in Y. Lemma 5's
odd-terminal form creates a strong `A> R` configuration, and Lemma 4 returns
to a safe checkpoint.

This exhausts the early cases and proves the return theorem. Every return
has a positive number of base steps: in particular its first nontrivial B
transition already has positive cost. All individual counter excursions and
all drains used in the argument are finite. QED.

## 7. Reachability from blank tape and the nonhalting conclusion

The two members share the following finite prefix. After exactly 156 base
steps from blank tape, they reach

\[
L\ ZZZXXX\ <B1\ Y R1
\]

with the stack written bottom first. The decoder is `YYYYYY`. The six
prefix comparisons are

| Prefix length | Actual counter v | Decoded reset counter b |
|---|---:|---:|
| 1 | 1 | 1 |
| 2 | 3 | 3 |
| 3 | 7 | 7 |
| 4 | 14 | 15 |
| 5 | 28 | 31 |
| 6 | 56 | 63 |

Thus this is a safe checkpoint. No B4 transition is needed to reach it: the
156 steps were checked with B4 undefined. The proposed Lean seed lemma is
included in `PrefixSafetySeed.lean`.

Starting from this checkpoint, repeatedly apply the return theorem. Either a
spinout is reached, which is nonhalting by (10), or there are arbitrarily many
safe returns, each covering a positive number of base steps. A finite halting
time is incompatible with either alternative. Therefore

\[
\neg\operatorname{Halts}(M(b4_{3RA}),\operatorname{init}),\qquad
\neg\operatorname{Halts}(M(b4_{2LA}),\operatorname{init}).
\]

No assumption about the asymptotic growth of the counter, a bounded
congruence class, the cheapness of reset words, or a simulation cutoff is
used in this argument.

### A stronger initial-configuration corollary

For either of these two members, any finite word `w` over `Y,V,X` with
`rho(w)>0` gives a nonhalting configuration `L <A wR`. Nonnegativity of the
final adjusted value implies that the whole reset is clean; Lemma 2 brings
it to a safe checkpoint, and the return theorem applies. The initial word
itself need not be a Dyck prefix. Dyck structure is needed for the decoder
of a left stack in the exceptional-case lemma, where it is automatic.

## 8. Scope, validation, and formalization

The proof uses specifically the two G replacements `X P2` and `Y P2`.
It does not establish nonhalting for the other eleven members. In particular,
the pending-1 replacements do not preserve this same argument; one should
not silently extend the conclusion to all five bouncing members.

The accompanying checker independently implements the prefix invariant and
constructive return lemma, then compares each return with the supplied
reference block simulator. The recorded run checks all admissible stacks of
length at most 10 where relevant, including 31,259 safe initial stacks and
62,518 member-specific return comparisons, plus 400 random larger comparisons.
It also checks 41,492 decrements against the reference stride implementation,
the 156-step seed, and the 9-step spinout. All these finite checks passed.
Additional component tests compare 2,303 clean reset words of length at most
8 with the reference machine, and make 322,112 tests of the balanced-group
inequality through six pairs. These checks also passed; see
`component_results.json`.
Their role is to catch errors in the proposed proof's formulas and cases;
none of them supplies the quantification over arbitrary stack length.

`FORMALIZATION.md` describes a route to port the proof into the existing Lean
project. The final nonhalting theorems are not present as kernel-checked
results in this package. The substantive new proof obligations are the
prefix borrowing lemma, paid-reset goodness, the matched-group expansion
lemma, and the exhaustive B-boundary return construction above.
