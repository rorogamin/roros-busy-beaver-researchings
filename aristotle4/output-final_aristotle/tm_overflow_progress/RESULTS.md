# Exact overflow normal forms and a productive family

Machine: `1RB---3RA2LA2RB_2LB3LA4LB4RA0RA`.

## Status

This continuation does not decide the blank-tape halting question. It obtains
an exact macro for the first event the previous mixed-radix accelerator could
not complete, two context-independent families of exceptional A-exits, and a
closed family of configurations that provably do not halt. Reachability of the
closed family from the blank start has not been established.

The statements below have mathematical proofs. Executable local tests and
independent Python/C++ calculations were also performed. The Lean extension
is an uncompiled draft, so these results must not be described as newly
kernel-checked Lean theorems.

## 1. Conventions and additional return rules

The transition table, with blank symbol 0, is:

| State | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| A | 1RB | halt | 3RA | 2LA | 2RB |
| B | 2LB | 3LA | 4LB | 4RA | 0RA |

A completed right return F enters a word in A and exits on its immediate left
neighbour in B. The left neighbour is not processed before the return ends.
The following identities are independent of the exterior tape, conditional on
the indicated child returns completing:

\[
\begin{aligned}
F(40x)&=42x, &\text{local cost }3,\\
F(42x)&=44x, &\text{local cost }3,\\
F(44x)&=42F(x), &\text{local cost }4,\\
F(43x)&=42F^2(x), &\text{local cost }5,\\
F(2x)&=2F^3(x), &\text{local cost }4.
\end{aligned}
\]

Local cost excludes the child-return costs. The new cases are 40 and 43.
For 43, the first two transitions leave 24 and enter the suffix in A. Its first
B-return reaches the 4 and uses B4 to start another suffix return, leaving 0.
The second B-return traverses that 0 and the preceding 2 in two steps. The
result is 42, and the local count is 2+1+2=5.

Use tokens D=2 and B_b with these encodings:

| b | -1 | 0 | 1 | 3 |
|---|---|---|---|---|
| B_b | 40 | 42 | 44 | 43 |

For k>0 virtual returns, a D passes 3k returns to its suffix and costs 4k
locally. A B_b passes

\[
q=\left\lfloor\frac{k+b}{2}\right\rfloor,
\qquad b'=(k+b)\bmod2,
\]

and becomes B_b', at local cost 3k+q. At k=0 the word is unchanged: do not apply
the arithmetic formula to normalize an untouched 43. In particular the
formula with k=0,b=3 would incorrectly request a child return.

A batch of returns here is *virtual*: it restarts in A at the word after each
B-exit, with no steps assigned to the restart. Section 4 supplies the actual
physical counter transitions that implement those restarts.

## 2. Exact return capacity

Fix a finite token prefix w and a cut immediately after it. Its suffix can be
arbitrary. Let C(w) be the maximum number of completed virtual returns before
the head first enters the suffix beyond this cut. Then:

\[
\boxed{
C(\epsilon)=0,\qquad
C(Dx)=\lfloor C(x)/3\rfloor,\qquad
C(B_bx)=\max(0,2C(x)+1-b).
}
\]

This is an exact boundary-avoidance capacity, not an assertion that the next
return cannot complete using cells beyond the boundary.

Proof: a D needs three child returns per completed outer return. For a positive
number k of returns through a bit token, the required child count is
floor((k+b)/2). This is at most c=C(x) exactly when k<=2c+1-b. If that right side
is negative, no positive k is allowed. Every such completed prefix computation
is accounted for by the local rules in Section 1; the next attempted return
must enter the child beyond its own capacity. Induction on the prefix proves
both sufficiency and maximality.

If k<=C(w) completed returns change w into w', then

\[
\boxed{C(w')=C(w)-k.}
\]

For D this is floor((c-3k)/3)=floor(c/3)-k. For a positive batch through B_b,
write k+b=2q+b'. Its new capacity is
2(c-q)+1-b'=2c+1-b-k. These identities also handle normalization of 40 and 43.
The k=0 case is the identity transformation.

Consequently, if a ternary counter to the left is incremented after every
return, N+C(w) is invariant *until this chosen cut is crossed*. This is not
claimed to be invariant through the ensuing exceptional event.

## 3. Exact exhaustion normal form

There is more information than the capacity. Run exactly C(w) completed virtual
returns, and then the beginning of the next return until the first A-entry to
the suffix. Stop before processing that suffix cell. Let H(w) be the final
contents of the prefix, and T(w) the transition count excluding outer restarts.
All three quantities are obtained by one right-to-left recursion.

Start with C(empty)=T(empty)=0 and H(empty)=empty. Put c=C(x).

For a D token, let c=3q+r with 0<=r<3:

\[
\boxed{
C(Dx)=q,\quad
H(Dx)=e(r)H(x),\quad
T(Dx)=T(x)+4q+1+r,
}
\]

where e(0)=3, e(1)=4, e(2)=0.

For a bit token, put h=max(0,2c+1-b):

\[
\boxed{
C(B_bx)=h,\quad
T(B_bx)=T(x)+3h+c+2.
}
\]

Its pending output is

\[
H(B_bx)=
\begin{cases}
24H(x),&b=3\text{ and }c=0,\\
20H(x),&\text{otherwise}.
\end{cases}
\]

### Proof of the pending symbols and times

For D, q completed outer returns consume 3q completed child returns and 4q
local transitions. The next outer entry writes 3 and starts the next child
return. Each of the r remaining child returns starts another child excursion,
changing the pending symbol 3 to 4 and then 4 to 0. This gives e(r) and
4q+1+r local transitions. In total the child undergoes exactly c completed
returns followed by its own first boundary entry, so its entire contribution
is precisely the inductive T(x), H(x).

For b=-1,0,1, completing h outer returns consumes c child returns and leaves a
44 at this node. The next attempted return traverses it to leave 20, in two
additional transitions. Thus its total local count is 3h+c+2.

For b=3 and c>=2 the same calculation applies. Two edge cases must be handled
separately rather than using the positive-batch formula at h=0. If c=0, the
very first A43 traversal leaves 24 in two steps. If c=1, the first child return
restarts through B4, leaving 20 in three local steps. Both cases agree with
the displayed time formula.

This proves the whole normal form by structural induction on the finite token
prefix. No statement about the later suffix computation is assumed. In
particular, a 43 node with child capacity zero necessarily leaves a 4 behind:
that gives a specific new source of the cascade shield used in the original
project.

## 4. A single physical TM event, including the left counter

Let a left counter of width m encode N using ternary digits 3=0,4=1,0=2, most
significant first. Assume 0<=N<3^m, a frontier 1 immediately to its left, and
blank tape beyond the frontier. The head is in A on a token prefix w, followed
by an arbitrary suffix x.

Set k=C(w), N'=N+k, and

\[
m'=\max(m,\ell_3(N')),
\]

where ell_3(0)=0. If s_3 is ternary digit sum, the total cost of the k physical
counter increments is

\[
\boxed{I(N,k,m)=2k+s_3(N)-s_3(N+k)+2(m'-m).}
\]

For a non-width-growing increment, if r trailing ternary digits are 2, its
cost is 2r+1 and the digit-sum change is 1-2r. When a width grows, the frontier
handling adds two further transitions. Summing over the k increments makes
the digit sums telescope. This also handles width zero and leading-zero
padding correctly.

Combining this with Section 3 gives the physical event theorem:

\[
\boxed{
0^\infty1\,\operatorname{enc}_m(N)\,[A:w]x
\ \longrightarrow\
0^\infty1\,\operatorname{enc}_{m'}(N+k)\,H(w)\,[A:x]
}
\]

in exactly T(w)+I(N,k,m) transitions. The head ends on the first suffix cell
without processing it; the suffix remains unchanged. The frontier may have
moved left, but the original token cells stay at their original positions.
The theorem is still valid with arbitrary tape left of the frontier if no
counter-width overflow occurs; then m'=m and that exterior tape is untouched.

Example: w=2 42 42 has C=1, H=3 20 20, and T=22. With N=1,m=1, the physical
counter increment costs one step. Therefore

\[
\cdots 1\,4\,[A:2\,42\,42]x
\longrightarrow
\cdots 1\,0\,3\,20\,20\,[A:x]
\]

in exactly 23 transitions.

This is the main advance over the preceding work: instead of rejecting an
overflowing return plan and immediately reverting to individual steps, the
new calculation gives the exact pending digits, counter value, and time at
the first unsupported boundary.

## 5. Two exact families of exceptional A-exits

Distinguish an A-exit from a completed B-return. The following formulas exit
one cell to the left in **state A**, with arbitrary unchanged outside context:

\[
\boxed{
(44)^m32x\ \longrightarrow_A\ 22(42)^mx,
\qquad\text{time }8m+1\quad(m\ge0),
}
\]

\[
\boxed{
(44)^m0000x\ \longrightarrow_A\ 22(42)^{m-1}4432x,
\qquad\text{time }8m+11\quad(m\ge1).
}
\]

The base cases are A32 -> left-A 22 in one step and
A440000 -> left-A 224432 in 19 steps. Both are direct transition calculations.
For the induction, if a suffix A-exits with output 2v in n steps, adding a
leading 44 leaves pending 20 before that suffix runs. The exiting A then
crosses these pending cells in six transitions, producing 224v and exiting
left in A. Including the two outward steps adds exactly eight transitions.
This proves both formulas by induction on m.

These equations expose the dangerous signal generated by binary overflow;
they do not misclassify it as a successful right return.

## 6. A proved nonhalting family

Let G denote the infinite blank-ended word 4320^infinity. A direct eleven-step
calculation gives

\[
\boxed{F(43200x)=44432x,\qquad F(G)=44G.}
\]

Consider every word P G, where P is any finite concatenation of tokens
2,40,42,44,43. Every such word makes a finite, positive-time B-return, and the
result again has this form.

Here is a well-founded proof, including the point that invalidates a naive
induction on word length. Define the grade of P to be the number of its 2 and
43 tokens. Use lexicographic induction on (grade, number of prefix tokens).
A return never increases grade.

* At G, use the eleven-step rule, which inserts one ordinary 44 token.
* A leading 40 or 42 returns immediately, becoming 42 or 44.
* A leading 44 uses one return of its shorter suffix, then becomes 42.
* A leading 2 uses three successive suffix returns. The suffix has strictly
  lower grade, and its first and second outputs do not increase that grade.
  Thus all three calls are covered by the induction, even if their binary
  tails have grown.
* A leading 43 similarly uses two calls on a strictly lower-grade suffix and
  becomes 42, reducing the overall grade.

This proves closure and finite return time for every member, not merely for
sample prefixes. `test_productive.py` gives the corresponding constructive
return function; `Overflow.lean` contains an uncompiled proof attempt using a
strong outer induction and a structural inner induction.

Now attach any finite ternary counter and frontier 1 to the left, with blank
tape beyond that frontier, and enter P G in A. A completed B-return is followed
by a finite safe counter increment, including its possible width growth. This
returns the machine in A to another member of the family. Repeating gives
arbitrarily many positive-time cycles, and therefore a nonhalting computation.

**Missing link:** this establishes nonhalting for the stated family, but no
blank-orbit configuration has been shown to enter it. A detector at the tested
event configurations did not find such an entry. This is not a claim that all
possible intermediate occurrences have been ruled out forever.

## 7. Finite execution checks

The exact computed blank-tape endpoint at 10^1000 transitions is:

| Quantity | Value |
|---|---:|
| State | B |
| Scanned symbol | 4 |
| Head position, initially 0 | -56 |
| Leftmost visited cell | -2150 |
| Rightmost visited cell | 6643 |
| Visited interval width | 8794 |

The full tape is saved in both `checkpoints/1e1000_cpp.json` and
`checkpoints/1e1000_python.json`. The C++ evaluator ran from blank. The Python
trajectory was executed in two chunks, from blank to `python_prefix.json` and
then from that exact snapshot to the endpoint. The prefix was independently
reproduced from blank in C++, at its exact integer transition count. All of
`t`, `p`, `q`, `lo`, `hi`, and the complete tape agree. Aggregate event counts
agree as well: 4987 drains, 1008 completed counter batches, 46651 individual
return macros, 7637 cascades, 31703 direct sweeps, and 51982 literal transitions.

Local testing covered every word of up to five tokens over all five token
types. With four different left counters this gives 15624 exact physical drain
comparisons, plus 1000 random longer-prefix/counter tests. These drain tests
executed 1447208 literal TM transitions. Another 14947 return-batch tests
checked success/failure thresholds, output tapes, times, and capacity decrease.

There were also 930 random-context checks of the terminal/collision formulas,
and 1000 constructive productive-family returns checked against 30094 literal
transitions. The event evaluator matched literal execution at all 378 of its
endpoints through 10^6 transitions. Separately, the C++ event evaluator matched
a literal C++ run at exactly 10^8 transitions. The earlier exact 10^100
checkpoint was reproduced as an additional regression check.

These checks test the formulas and implementations. They are not a Lean proof
of the evaluators' soundness, and no finite number of transitions proves
nonhalting of the blank computation.

## 8. Why the remaining invariant must retain more structure

Two concrete tests exclude tempting shortcuts. First, a generic configuration
with counter N=1 and right word 42 reaches A1 after 26 defined transitions.
The analogous words 24 and 422 reach A1 after 60 and 20 transitions. Thus an
arbitrary ternary counter plus a binary-looking word is not a nonhalting class.

Second, the observed leftmost A3 position is not a permanent spatial barrier.
It reaches -19 before 10^100, later -28 around 1.057e186, -38 around 1.151e285,
-48 around 8.432e454, and -53 around 1.243e982. These are positions where A is
actually scanning 3, not positions inferred from macro endpoints. The cascade
implementation records the internal A3 visits in a 2/Q crossing as well. This
refutes extrapolating the earlier fixed bound; it does not itself prove an
unbounded leftward drift.

The new event macro exposes a concrete remaining proof obligation: control
the residues C(x) mod 3, the counter digits of N+C(w), and the changes to the
token word and its cut during exceptional events, strongly enough to maintain
a cascade stopper before a 1 can be reached. The existing 4/00 stopping lemmas
can then discharge individual cascades. The local conservation N+C(w) is not
by itself that global invariant, since the exceptional rewrite changes the
prefix and the interpretation of the cut.

There is no assertion here that a near-4x scalar recurrence, a fixed-position
shield, or the newly found productive family already applies to the whole
blank orbit.

## 9. Formalization boundary

`RequestProject/Overflow.lean` is a 269-line draft importing the original
`RequestProject.Macro`. It contains local B-return and A-exit rules, the two
collision inductions, arithmetic capacity lemmas, and productive-return closure.
It contains no `sorry`, `admit`, or additional axioms. Nonetheless it has not
been compiled; elaboration or tactic repairs may be needed.

The full exhaustion-normal-form theorem and the telescoping physical-counter
cost are proved mathematically above and tested by the supplied code, but are
not yet connected to the original TM semantics by a compiled Lean proof. Nor
is the complete Python/C++ evaluator Lean-certified. Most importantly, the
blank-orbit global invariant/reachability argument remains absent. These are
separate gaps and should not be conflated.
