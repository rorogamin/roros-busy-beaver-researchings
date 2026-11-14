# A two-epoch nonhalting proof

## Machine and verification status

The machine is

```
1RB3LA3LA0RB2LB_2LA4LA4RA2RA---
```

It starts in state A on an all-zero tape. The table is:

| State | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| A | 1RB | 3LA | 3LA | 0RB | 2LB |
| B | 2LA | 4LA | 4RA | 2RA | halt |

**Conclusion:** the argument below proves nonhalting mathematically. It uses the supplied project's exact carry, spill, rebuild and tail laws, and supplies the missing infinite invariant. It is not a claim that the new infinite proof has already been checked by Lean. The accompanying Python program was executed successfully; it checks the finite entry, the base certificates, and the agreement of the new epoch map with the existing token laws. `TwoEpochCertificate.lean` contains finite certificate statements but has not been compiled in this environment.

The change of viewpoint is important: do not try to propagate a one-epoch condition that merely asks for two conversions. Instead, use a **two-epoch contraction of inherited carry costs**, and a trailing binary-digit condition that forces enough conversions to bound newly introduced costs.

## 1. Conventions and the existing reduction

Token words use the project's convention: the head of a `List Tok` is the rightmost token. Write F for a fresh marker, C for a charged marker, and P for a block. Their capacities are

\[
\begin{aligned}
\operatorname{cap}([])&=0,\\
\operatorname{cap}(F::w)&=2\operatorname{cap}(w)+1,\\
\operatorname{cap}(C::w)&=2\operatorname{cap}(w),\\
\operatorname{cap}(P::w)&=\lfloor\operatorname{cap}(w)/2\rfloor.
\end{aligned}
\]

The supplied `cap_carry_iff` and `cap_carry` say that `carry d w` succeeds exactly when the capacity is at least \(2^d\), and then subtracts \(2^d\). A carry preserves length.

A normal overflow configuration is

\[
\langle L,X,[3,2]\rangle,\qquad \operatorname{cap}(X)=0.
\]

Its spill is the chunk word `ck X`, in **forward tape order, deepest end first**. The chunks have cell encodings

\[
M=33,\qquad S=32,\qquad B=22.
\]

Here B is a chunk name, not the machine state or the token P. The spill/reflection presents the cells

\[
3\;\operatorname{csyms}(\operatorname{ck}X)\;3\;2.
\]

`spill_ck`, `overflow_pass`, `capF_csyms` and `overflow_rebuild_run` already establish the corresponding machine reductions.

The capacity scan of a chunk word starts at \(R=0\) and uses

\[
M:R\mapsto2R+1,\qquad
S:R\mapsto2R,\qquad
B:R\mapsto\lfloor R/2\rfloor-1.
\tag{1}
\]

The B operation is defined only for \(R\ge2\). Write \(v(c)\) for the final value of this scan when it succeeds. **This is `ckFold 0 c`, not `ckRun 0 c`: the latter has one final doubling and returns \(2v(c)\).**

## 2. The hidden-bit decoration: an exact refinement of `pat`

The pattern `pat` in the supplied project records only whether a token is P. We need one more bit at each P. Define a decoration \(D(w)\), again in forward/deep-end order, by

\[
\begin{aligned}
D([])&=[],\\
D(F::w)=D(C::w)&=D(w)M,\\
D(P::w)&=D(w)\begin{cases}
S,&\operatorname{cap}(w)\text{ odd},\\
B,&\operatorname{cap}(w)\text{ even}.
\end{cases}
\end{aligned}
\tag{2}
\]

This records the bit discarded by the division by two at a P.

### Lemma 2.1. Carries preserve the decoration

If `carry d w = some w'`, then \(D(w')=D(w)\).

**Proof.** Induct through the defining recursion of `carry`.

* At a marker, both F and C have decoration M, so changing F to C or C to F does not change that position. Apply the induction hypothesis to a recursive carry, when there is one.
* At P, the recursive carry is `carry (d+1)` on the tail. It subtracts \(2^{d+1}\), an even integer, from that tail's capacity. The parity used in (2) therefore stays the same. The induction hypothesis preserves the rest of the decoration.

The successful-carry hypothesis guarantees that these subtractions do not truncate. This proves the claim for every word, without a balance assumption. QED.

### Lemma 2.2. At zero capacity, the decoration is exactly `ck`

If \(\operatorname{cap}(w)=0\), then

\[
\operatorname{ck}(w)=D(w).
\tag{3}
\]

**Proof.** Induct on word length. F at the head is impossible. At C, the tail has capacity zero and both recursions append M. At P, the tail has capacity zero or one. At zero, its carry fails and both recursions append B. At one, the carry succeeds, leaves capacity zero, and preserves the decoration by Lemma 2.1; both recursions append S. The carried tail has unchanged length, so the induction decreases the original word length by one. QED.

This is the precise additional information missing from a comparison based only on `pat`.

## 3. An exact overflow-to-overflow map

While scanning a successful chunk word \(c\) by (1), emit a word \(A(c)\) of the same length:

\[
\begin{array}{c|c}
\text{input}&\text{emitted chunk}\\\hline
M&M\\
S&M\\
B\text{ entered with }R\text{ odd}&S\\
B\text{ entered with }R\text{ even}&B
\end{array}
\tag{4}
\]

Let \(k(c)\) be the number of B-to-S conversions in this scan.

### Lemma 3.1. The rebuilt core has decoration \(A(c)\)

For a successful chunk scan, the complete rebuild ends immediately before tail creation with token word

\[
C::U,\qquad \operatorname{cap}(U)=v(c),\qquad D(U)=A(c).
\tag{5}
\]

**Proof.** Pairing the cells `3 (csyms c) 3 2` is offset by one. Each chunk first appends a token, then causes a carry unless it is M. Thus:

* M appends F: capacity \(2R+1\), decoration appends M.
* S appends F and carries once, leaving C: capacity \(2R\), decoration appends M.
* B appends P and carries once: capacity \(\lfloor R/2\rfloor-1\). The appended decoration is S or B according to the parity of the old \(R\), and the following carry does not alter it by Lemma 2.1.

After all chunks, the final pair appends F and the final lone 2 causes one carry, changing that F to C. Hence the whole word is C::U. QED.

### Lemma 3.2. The constant in the pass arithmetic is **+5**

Suppose \(v=v(c)\ge3\). Put

\[
N=v+5,\qquad t=\lfloor\log_2N\rfloor.
\tag{6}
\]

Then the machine reaches its next normal overflow without halting. Its word is

\[
X'=P^t++V,\qquad
\operatorname{cap}(V)=N-2^t,\qquad
D(V)=A(c).
\tag{7}
\]

**Proof.** Starting from (5), the tail is created in front of C::U. Apply the supplied `tail_pass`: one carry in U consumes one capacity unit and removes the leading C while eating the tail. The configuration becomes

\[
\langle L,U_1,[2,2,3,2,3,2]\rangle,
\qquad \operatorname{cap}(U_1)=v-1.
\]

The carry through the initial 22 costs two more units. It succeeds because \(v\ge3\). Re-parsing the two remaining 32 pairs, followed by the blank-end turn, produces a normal pass boundary

\[
\langle L,P^3++U_2,[3,2]\rangle,
\qquad \operatorname{cap}(U_2)=v-3.
\]

A subsequent ordinary pass, with j blocks already on top, subtracts \(2^j\) from the core and appends another P. Therefore, after t blocks have been appended in total, the core capacity is

\[
v-3-\sum_{j=3}^{t-1}2^j=v+5-2^t.
\]

The next pass fails exactly when this is less than \(2^t\), while all previous passes succeed exactly when the relevant subtractions are affordable. This gives the unique \(t\) in (6). All carries preserve the decoration of the core, by Lemma 2.1. Every machine segment used here is an existing successful macro law. QED.

Define \(\beta_t(N)\) to be the low t bits of N, **least significant bit first**, with 1 represented by S and 0 by B. The leading 1 of N is omitted.

### Corollary 3.3. Exact epoch map

Under the preceding hypotheses,

\[
\boxed{T(c)=A(c)\;\beta_t(v(c)+5).}
\tag{8}
\]

Indeed, \(\operatorname{cap}(X')=0\), so `ck X' = D(X')` by Lemma 2.2. The decoration of the t top blocks is the low-to-high binary expansion of \(\operatorname{cap}(V)=N-2^t\). This proves (8).

This derivation also proves the dynamical connection to the machine; (8) is not merely a guessed scalar recurrence.

## 4. A carry-price potential

For a chunk word \(c=c_1\cdots c_m\), set

\[
h_0=0,\quad
h_i-h_{i-1}=\begin{cases}+1,&c_i=M\text{ or }S,\\-1,&c_i=B.\end{cases}
\]

Write \(e(c)=h_m\), and define

\[
\rho(c)=\sum_{i:c_i\ne M}2^{-h_i},
\qquad
\boxed{\Phi(c)=\rho(c)+2^{-e(c)}}.
\tag{9}
\]

All these are exact dyadic rationals; the definition makes sense even for negative heights. The terminal term is intentional. It makes the final capacity large as well as preventing an intermediate failure.

### Lemma 4.1. Cheap words are safe

If \(\rho(c)<1/2\), its capacity scan succeeds. At every successful prefix,

\[
1-\rho(\text{prefix})
\ \le\ \frac{R+1}{2^{h}}\ \le\ 1.
\tag{10}
\]

In particular, if \(\Phi(c)\le1/8192\), then its scan succeeds and its final capacity is at least 3.

**Proof.** M leaves \((R+1)/2^h\) unchanged. S reduces it by exactly \(2^{-h_{\rm new}}\). A successful B reduces it by

\[
(1+(R\bmod2))\,2^{-h_{\rm old}},
\]

which lies between one-half and all of its charged price \(2^{-h_{\rm new}}\). This proves (10) until a possible first failure.

At a failed B, \(R\le1\), so the normalized capacity immediately before it is at most that B's price. It would therefore be less than \(1/2\). But (10) makes it greater than \(1/2\), a contradiction.

For the last assertion, the terminal term implies \(2^e\ge8192\), and (10) gives

\[
v+1\ge(1-1/8192)2^e\ge8191.
\]

Thus \(v\ge8190>3\). We will only need the weaker conclusion \(v\ge3\). QED.

## 5. Twelve terminal S's reproduce themselves

Fix

\[
r=12,\qquad \epsilon=2^{-13}=1/8192.
\tag{11}
\]

### Lemma 5.1. Stable terminal digits

Suppose

\[
\Phi(c)\le\epsilon,\qquad c\text{ ends in }S^{12}.
\tag{12}
\]

Then the map (8) is defined,

\[
t=e(c)-1\ge12,
\tag{13}
\]

and \(T(c)\) also ends in \(S^{12}\).

**Proof.** Let \(v=v(c)\), \(e=e(c)\). Lemma 4.1 gives success and \(v\ge3\). The terminal S's make \(v\) divisible by \(2^{12}\). The upper bound in (10) gives \(v\le2^e-1\). Since \(e\ge13\), divisibility strengthens this to

\[
v\le2^e-2^{12}.
\]

Consequently \(v+5<2^e\). The lower bound gives

\[
v+5\ge(1-2^{-13})2^e+4>2^{e-1}.
\]

Thus \(t=e-1\). Moreover, N=v+5 has at least thirteen leading binary 1's. After omitting its leading 1, its least-significant-bit-first expansion ends in twelve S's. QED.

This is why both a price bound and a terminal digit condition are kept. Without the divisibility condition, \(v+5\) could cross \(2^e\) and introduce a new leading bit.

## 6. The terminal digits force eight conversions

### Lemma 6.1. Conversion production

Under (12), if the scan of \(T(c)\) succeeds, then

\[
\boxed{k(T(c))\ge8.}
\tag{14}
\]

**Proof.** The last twelve S's of c become twelve M's at the end of A(c). Therefore the capacity a at the end of scanning A(c) satisfies

\[
a\equiv2^{12}-1\pmod{2^{12}},\qquad a\ge2^{12}-1.
\tag{15}
\]

The scan of A(c) succeeds: its chunks dominate c pointwise in the order B<S<M, and each operation is monotone.

Also \(v(c)\equiv0\pmod{2^{12}}\), so the first twelve chunks of the new binary suffix are

\[
S\;B\;S\;B^9.
\tag{16}
\]

Starting with capacity a, the first four symbols S B S B take it through

\[
a\longmapsto2a\longmapsto a-1
\longmapsto2a-2\longmapsto a-2.
\]

The first two B's encounter even capacities. At the remaining eight B's, the input capacities are

\[
\left\lfloor\frac a{2^j}\right\rfloor-2,
\qquad j=0,1,\ldots,7.
\tag{17}
\]

Every one is odd by (15); even the smallest is at least 29. Thus all eight B's become S in the emission scan of T(c). QED.

This is a deterministic lower bound, not an assertion inferred from the orbit's observed conversion counts.

## 7. The two-epoch contraction

### Lemma 7.1. One-step inherited cost does not increase

For a successful c,

\[
\rho(A(c))\le\rho(c).
\tag{18}
\]

Every M or S becomes M and pays nothing. A B either stays B or becomes S. A B-to-S conversion increases the height of that position and every later position by two. Thus the remaining paying positions are a subset of the old B positions, at no smaller height. QED.

### Lemma 7.2. Two-step inherited cost falls by a factor of four

Let d=T(c), with both scans successful. In A(d), restrict attention to the first \(|c|\) positions, inherited from c. Their total price is at most

\[
\boxed{\rho(c)/4.}
\tag{19}
\]

**Proof.** If c has no B, every inherited position is M after the first emission and pays nothing.

Otherwise consider its **first B**. Before that B, c contains only M and S. If the B converts on the first emission, then after two emissions it is M and has permanently raised the inherited height by two. If it does not convert on the first emission, then on the second emission it is preceded entirely by M's. Its input capacity is then \(2^j-1\), which is odd, so it converts on that second emission. There are at least two preceding chunks because its original B operation succeeded.

Thus, in either case, every inherited position at or after this first B has gained at least two height units by the second emission. Earlier positions, and positions originally S, are M and pay nothing. Every remaining inherited paying term is consequently at most one quarter of its corresponding old B term. Summing proves (19). QED.

No hypothesis about having two conversions per epoch is used in this contraction.

## 8. Bounding the cost of a newly appended suffix

Suppose c satisfies (12) and let \(k=k(c)\). The height at the end of A(c) is

\[
e_A=e(c)+2k.
\]

By Lemma 5.1, the new suffix has length \(t=e(c)-1\). After j suffix chunks, its height is at least \(e_A-j\). Therefore the cost of this suffix **together with the new terminal term** is at most

\[
\begin{aligned}
\sum_{j=1}^t2^{-(e_A-j)}+2^{-(e_A-t)}
&=(3\cdot2^t-2)2^{-e_A}\\
&<3\cdot2^{t-e_A}\\
&=\frac{3}{2\cdot4^k}.
\end{aligned}
\tag{20}
\]

For \(k\ge8\), use the uniform bound

\[
\boxed{\delta=\frac{3}{131072}=\frac{3}{16}\epsilon.}
\tag{21}
\]

This bound is independent of the word length and the number of passes.

### Lemma 8.1. Closed two-epoch price estimate

Suppose c,d=T(c) satisfy (12) and have at least eight conversions each. Then

\[
\boxed{\Phi(T(d))\le\frac14\Phi(c)+2\delta
\le\frac58\epsilon<\epsilon.}
\tag{22}
\]

**Proof.** Split A(d) into the part inherited from c and the part inherited from the suffix appended in d.

The first part costs at most \(\rho(c)/4\), by Lemma 7.2. The second part costs no more than that first suffix originally cost, by the pointwise argument of Lemma 7.1; it is at most \(\delta\). Finally the suffix newly appended to T(d), including its terminal term, costs at most \(\delta\), by (20).

Hence

\[
\Phi(T(d))\le\rho(c)/4+2\delta
\le\Phi(c)/4+2\delta.
\]

The constants close because

\[
\frac14\cdot\frac1{8192}
+2\cdot\frac3{131072}
=\frac5{65536}
=\frac58\cdot\frac1{8192}.
\]

QED.

Notice the role of two successive epochs. A one-step inequality would merely add the new suffix's cost and would not close an infinite induction.

## 9. Finite entry and exact base certificates

Direct evaluation of the raw transition table for **4011 steps** gives

\[
\operatorname{steps}(4011,\operatorname{init})
=\operatorname{ecfg}\langle L,X_5,[3,2]\rangle,
\]

where, in reverse token order,

```
X5 = PPPPPPFPCCCPPPCCCFFFC
```

This is precisely `ovfWord5` in the supplied `RunCert.lean`. Its capacity is zero and

```
c5 = ck X5 = MMMMMMMBBBMMMBMSBBSSS
```

The accompanying verifier checks all 4011 raw steps with the same finite-list tape convention as `Machine.lean`; this is not a run starting from an assumed macro seed.

Starting with c5, apply (8) seven and eight times, respectively:

\[
c_{12}=T^7(c_5),\qquad c_{13}=T^8(c_5).
\]

Each intervening scan succeeds and has final capacity at least three. The verifier independently reconstructs the token word by the pair-of-cells rebuild, tail-eating carries and ordinary passes, and checks that its `ck` is exactly the predicted T-image at every transition.

The base data are:

| Quantity | c12 | c13 |
|---|---:|---:|
| Length | 479 | 853 |
| Final height | 375 | 621 |
| Number of paying chunks | 239 | 426 |
| Minimum paying or terminal height | 50 | 171 |
| Trailing S's | 46 | 48 |
| Conversions k | 27 | 72 |

In particular,

\[
\Phi(c_{12})\le\frac{240}{2^{50}}<\frac1{8192},
\qquad
\Phi(c_{13})\le\frac{427}{2^{171}}<\frac1{8192}.
\tag{23}
\]

These coarse integer bounds suffice. No floating-point approximation is used. The complete chunk words, token words, capacities and exact rational prices are in `certificate.json`.

## 10. Infinite induction and nonhalting

Maintain a pair of consecutive actual overflow chunk words

\[
c,d=T(c)
\]

with

\[
\Phi(c),\Phi(d)\le\epsilon,\qquad
c,d\text{ end in }S^{12},\qquad
k(c),k(d)\ge8.
\tag{24}
\]

The pair c12,c13 satisfies (24) by the finite certificate.

For the induction step, put f=T(d).

1. Lemma 4.1 makes the scan of d successful with capacity at least three. The exact machine epoch law therefore reaches the next actual overflow, with chunk word f, in finitely many nonhalting steps.
2. Lemma 8.1 gives \(\Phi(f)\le5\epsilon/8\), so f is also safe and has positive capacity for the following epoch.
3. Lemma 5.1 makes f end in twelve S's.
4. Lemma 6.1, applied to d, gives \(k(f)\ge8\).

Thus the next pair d,f again satisfies (24). This is ordinary induction on the overflow number. There is no unproved orbit-wide conversion or affordability hypothesis left.

Finally, every epoch contains a genuine tail-creation transition, costing nine raw machine steps, and is a finite composition of successful macro rules. Consequently the concatenated epochs have unbounded total raw time. Since the blank computation reaches the base pair, it has a defined continuation past every finite raw time.

\[
\boxed{\forall n\in\mathbb N,\quad
\operatorname{steps}(n,\operatorname{init})\ne\operatorname{none}.}
\]

Equivalently, `BB25.Halts` is false. QED.

## 11. What has and has not been checked computationally

The executed verifier checked:

* the raw blank-to-X5 computation at step 4011;
* the exact epoch formula against independent token-word reconstruction through overflow 14;
* the base pair c12,c13 with exact integer and rational arithmetic;
* the one-step and two-step inherited-price inequalities and exact rebuild emission on all 6547 successful chunk words of length at most nine, as diagnostics;
* the hidden-bit decoration on all 29524 token words of length at most nine, including its preservation in 83653 successful carries (carry indices zero through nine).

The finite diagnostic is not the reason the infinite conclusion follows; Sections 2-10 are the mathematical argument. The new infinite theorem has not been Lean-kernel-checked here. `FORMALIZATION.md` explains how to port the new lemmas into the supplied project without changing its Turing-machine model.
