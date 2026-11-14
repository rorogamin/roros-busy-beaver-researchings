# Handoff for formalizing the two-epoch proof

## Status and scope

`NONHALTING_PROOF.md` supplies the complete proposed mathematical nonhalting
argument. The actual infinite theorem is **not yet Lean-kernel-checked**.
The exact finite Python verifier has been executed successfully. The supplied
`TwoEpochCertificate.lean` is an **uncompiled proposed finite-certificate
module**, not a formal proof of nonhalting.

Use the uploaded project's Lean 4.28.0 / Mathlib 4.28.0 environment. No changes
to `Machine.lean`, the transition table, the starting configuration, or the
meaning of `Halts` are required.

## The idea that closes the gap

The old one-epoch propagation conditions can be replaced by the invariant on
a pair of consecutive actual overflow words c,d=T(c):

    Phi(c), Phi(d) <= 1/8192
    c and d end in twelve S chunks
    k(c), k(d) >= 8

Here k counts B chunks entered at an odd capacity. All three conditions
propagate. The crucial estimate is

    Phi(T(d)) <= Phi(c)/4 + 2*(3/131072) <= (5/8)*(1/8192).

The quarter factor does NOT assume two conversions: over two emissions the
first old B necessarily converts at least once, so every remaining inherited
paying position has gained two units of height. The suffix condition forces
eight conversions for the next scan; it is not an orbit-wide assumption.

The mathematical proof establishes the exact map

    T(c) = A(c) ++ lowBitsLSBFirst(v(c)+5)

where the leading binary 1 is omitted and v is `ckFold 0 c`, not `ckRun 0 c`.

## Suggested module order

### 1. Decoration: the hidden bit at each P

Start from the `decoration` definition in `TwoEpochCertificate.lean`:

    D(F::w) = D(C::w) = D(w) ++ [M]
    D(P::w) = D(w) ++ [if cap(w) odd then S else B].

Prove:

* Every successful `carry d` preserves D.
* If `cap w = 0`, then `ck w = D w`.
* `D w` has length `w.length`.

For the carry lemma, induct on the token list, generalizing d and the result.
Use the same case split as `carry_pat` in `Passes.lean`. The only new issue is
the parity at P: the recursive carry subtracts `2^(d+1)` from the tail's
capacity. This is even. First derive affordability from `cap_carry_iff`;
then `cap_carry` and modular arithmetic preserve parity. Do not use a natural
subtraction identity without proving the corresponding lower bound.

For `ck = D`, induct strongly on list length, using `carry_length` for the P
case that recurses on the carried tail. At capacity zero, a P's tail has
capacity 0 or 1. The first case emits B; the second emits S and leaves a
zero-capacity tail. The carry-invariance lemma identifies its decoration.

This is a strictly stronger replacement for the information in `pat`.
It does not require a balance hypothesis.

### 2. Exact emission and exact machine epoch

`emitRun` in the finite module decorates the existing `ckStep` scan. Prove its
returned value agrees with `ckFold`; its emitted word is A(c).

Refine `capF_csyms` / `rebG_pat` to track D during the offset pair parsing of
`3 :: (csyms c ++ [3,2])`. With a successful scan ending at v, prove that
`rebG` returns a tail with word `C::U`, where

    cap U = v
    D U = A(c).

The induction step is especially simple when written as "append a token,
then carry if the chunk pays":

    M -> append F
    S -> append F, carry 0
    B -> append P, carry 0.

The carry-invariance lemma makes the output decoration local, even when the
carry travels arbitrarily far through U.

Use these already supplied dynamical laws:

* `overflow_pass` in `Spill.lean`;
* `spill_ck` in `Chunks.lean`;
* `rebG_reaches` and the scalar rebuild correspondence in `Capacity.lean`;
* the tail-creation rule `estep` with cost 9 in `TokenE.lean`;
* `tail_pass` in `Turn.lean`;
* `crossCarry`, `cascade_pass_tok`, `carry_replicate_P`, `cap_replicate_P`.

For v >= 3 the tail phase spends 1 and then 2, giving

    <L, P^3 ++ U2, [3,2]>,  cap U2 = v-3,  D U2 = A(c).

The ordinary passes spend `2^3, 2^4, ...`. Set

    N = v+5
    t = Nat.size N - 1.

Their last core has capacity `N - 2^t`, strictly less than `2^t`. This proves
that the next overflow is `P^t ++ V` with `D V = A(c)`. Apply `ck = D` at
capacity zero to read the new top blocks as the bits of `N - 2^t`.

IMPORTANT: existing `bitChunks` is a bounded greedy expansion, not a bitwise
modulo operation on arbitrary input. The correct call is

    bitChunks (N - 2^t) t,

NOT `bitChunks N t`. The Python verifier's shift/mask version directly reads
the low t bits, but the Lean function needs the leading 1 removed explicitly.

State the semantic epoch theorem with an existential strictly positive raw
time or a positive extended-macro trace. Positivity matters at the very end;
plain reflexive reachability by itself would not establish nonhalting.

### 3. Price and safety

Define on chunks, at initial height h, the rational sum of `2^(-height)` over
paying chunks. Define Phi with a FULL terminal term `2^(-finalHeight)`.
The existing `cprice` has only half this terminal term; account for that
factor rather than silently treating the definitions as identical.

A convenient direct proof tracks

    (R+1) * 2^(-h).

At any successful prefix it lies between `1-rho(prefix)` and 1. M leaves it
unchanged. S subtracts exactly its price. B subtracts between half and all
of its price. This gives:

    rho(c) < 1/2 -> ckFold 0 c succeeds
    Phi(c) <= 1/8192 -> v(c) >= 8190, e(c) >= 13.

Use rational integer powers so that intermediate negative heights are legal.
Alternatively prove a height lower bound first, then use natural powers, but
do not assume the whole path was already nonnegative in the safety proof.

### 4. Suffix stability and forced conversions

For a successful c with Phi <= 2^-13 and suffix S^12:

    v(c) is divisible by 4096
    (1-2^-13)*2^e + 4 <= v(c)+5 < 2^e
    t = e-1.

The low-bit suffix of `v(c)+5` ends with twelve S's, because its binary
expansion has thirteen leading 1's before removing the first one.

For conversion production, A(c) ends with M^12. Its ending capacity a obeys

    a >= 4095, a % 4096 = 4095.

The first twelve appended chunks are `S B S B^9`, since `(v+5)%4096 = 5`.
The first four send a to a-2. The next eight B's are entered at

    a / 2^j - 2, j = 0,...,7.

These are odd and at least 29. Thus, once the next scan is known successful,
it has at least eight conversions. Only fixed-size modular arithmetic is
needed here. This lemma can be stated with a successful-next-scan hypothesis;
the pair induction below supplies it from the new price bound.

### 5. Two emissions contract inherited price

It is useful to prove the inherited assertion for A(A(c)) first; scanning
A(c) is always safe when scanning c is safe, by chunk monotonicity.
The first `length(c)` chunks of A(T(c)) equal A(A(c)), since the scan is
left-to-right and the additional suffix is later.

One emission is pointwise nondecreasing in chunk order B<S<M and in height.
Every old S/M becomes M. Prove rho(A(c)) <= rho(c).

For two emissions split c before its first B. If there is no B, the emitted
word is all M. Otherwise the prefix consists only of M and S. The first B
is either converted immediately, or is preceded by all M on its second scan
and hence entered at the odd capacity `2^j-1`. So it converts by that point.
The prefix length j is at least 2 because the original B was affordable.

Therefore every remaining inherited paying term is evaluated at a height
at least two larger than the old height. Its price is at most one quarter
of the corresponding old B price. Earlier chunks are all M and pay nothing.
This proves the inherited quarter bound without assuming any lower bound
on the number of conversions in an individual epoch.

### 6. New-suffix cost and pair induction

A(c) ends at height `e+2*k(c)`. Under the suffix hypotheses its new suffix has
length t=e-1. At suffix position j its height is at least `e+2k-j`. The sum
of all suffix prices plus the new terminal price is bounded by

    (3*2^t-2)*2^(-e-2k) < 3/(2*4^k).

For k>=8 this is at most delta=3/131072.

For c,d=T(c), split A(d) into original-c positions and the first new suffix.
The former costs <=rho(c)/4, the latter <=delta by one-step domination.
The second new suffix including its terminal costs <=delta. Thus

    Phi(T(d)) <= Phi(c)/4 + 2*delta <= (5/8)*epsilon.

Prove closure of a PAIR invariant. Do not try to derive Phi(T(c)) <=epsilon
from a single cheap c using only this estimate: it is inherently two-step.

Given a good pair c,d, set f=T(d). First use the two-step inequality to prove
Phi(f)<=epsilon and hence that f's scan succeeds. Then apply the forced-
conversion lemma to d to obtain k(f)>=8. The terminal S condition follows
from the binary lemma applied to d. This order removes any circularity.

### 7. Finite seed and the final raw nonhalting theorem

The proposed finite module gives the exact blank-to-seed statement

    steps 4011 init = some (ecfg <L, ovfWord5, [3,2]>).

It also computes c12=T^7(c5), c13=T^8(c5) and checks that every intermediate
epoch map succeeds. Use the semantic epoch theorem to lift these finite
iterations to actual machine runs. Do not confuse a finite computation of
the chunk map with its as-yet-unformalized semantic connection to the TM.

The finite price certificates deliberately avoid huge rational evaluation:

    c12: at most 239 paying terms, all at height >=50; final height >=50
    c13: at most 426 paying terms, all at height >=171; final height >=171

Hence Phi(c12)<=240/2^50 and Phi(c13)<=427/2^171. Both are less than epsilon.
Both have at least twelve terminal S's and at least eight conversions.

Induct on the number of epochs using pair closure. Compose the successful
raw paths using `steps_add`. Each epoch contains the nine-step tail-creation
transition, so the raw times grow without bound. A purported halt at time n
contradicts an epoch path whose raw length exceeds n.

The final desired theorem remains exactly

    theorem not_halts : Not BB25.Halts := ...

No assumption about the whole infinite orbit should occur in its type.

## Reproducibility

Run the executed finite checks with:

```sh
python3 verify_certificate.py --exhaustive 9 --json certificate.json
```

The exhaustive option checks the one- and two-emission price inequalities and
the exact rebuild emission on 6547 successful chunk words of length at most
nine. It also checks the hidden-bit decoration on 29524 token words, including
83653 successful carries. These are diagnostics, not the infinite proof.

To try the uncompiled Lean finite certificate in the original project:

```sh
cp TwoEpochCertificate.lean /path/to/project/RequestProject/
cd /path/to/project
lake env lean RequestProject/TwoEpochCertificate.lean
```

Elaboration may need adjustment because that file could not be compiled here.
The original project should remain unchanged except for adding new modules.
