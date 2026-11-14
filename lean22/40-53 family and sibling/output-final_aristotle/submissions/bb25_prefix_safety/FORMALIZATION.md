# Porting the prefix-safety proof into the supplied Lean development

The mathematical argument is in PROOF.md. It is intended as a detailed input
for Aristotle or a human Lean formalizer, not as a request to rediscover an
invariant. Do not replace the prefix invariant with the old `rcost` bound.

## Conventions

The paper uses bottom-first stacks over X/Z/W and omits L. The project uses
nearest-first lists and includes L. A convenient approach is a separate small
inductive type for the bottom-first stack, with a conversion

```
toLB s = s.reverse.map ... ++ [LB.L]
```

Another is to use `List LB` with a predicate restricting its entries to X/Z/W,
and explicitly reverse it at the existing machine interface. Avoid switching
orientations implicitly.

The scalar reset coordinate is an INTEGER. Its three maps are

```
Y z = 2*z + 1
V z = 2*z
X z = z / 2 - 1
```

All uses of division in the proof have a positive denominator; negative
intermediate values are only used to detect an unclean reset. The actual
clean-stack counters are natural numbers.

## Suggested implementation order

1. Define admissible matching and `P`, the decoder of a stack. It maps bits to
   Y and a matched W to V or X according to the matched bit. Prove that P is a
   Dyck prefix and commutes with taking prefixes. The matched-tree formulation
   makes this nearly structural.

2. Establish the bridge to the existing cval/cdec/ofw functions:
   - admissible stacks decompose into transparent groups and unmatched bits;
   - cval is the binary value of the unmatched bits;
   - cdec changes only unmatched bits as a binary decrement;
   - P is unchanged by a successful cdec;
   - every prefix cval weakly decreases under cdec;
   - at cval zero, ofw is exactly P.
   Existing `Pairing.lean` and `Overflow.lean` contain the appropriate semantic
   ingredients. One can prove these first on an abstract matched stack and
   then transfer through its list encoding.

3. Define `Good s` by admissibility and
   `forall u, u is a bottom-prefix of s -> v(u) <= rho(P(u))`.
   Prove preservation by prefix truncation, cdec, appending either bit, and
   appending W after at least two decrements. The full-prefix quantifier is
   essential: an inequality only at s is not the invariant used by the proof.

4. Define the paid reset stack function T on clean words. Its clauses are
   append Z for Y, append X for V, and `D (append W s)` for X. Prove the
   machine correspondence by the existing reset rules; account explicitly
   for when the final pending-1 decrement is paid. Prove `Good (T w)`.

5. Define the parity transducer Q, prove `P(T w)=Q w`, then formalize the
   balanced-tree expansion lemma. For nonempty Dyck input, its output reset
   map takes any second input c >= 0 to at least 4*c+2. The key even-closing-X
   case necessarily has a nonempty interior. This yields the exceptional
   low-counter lemma for a nonempty Dyck prefix u with rho(u)=0.

6. Prove the strong-drain lemma, using `b+2 >= 4*(v+1)` at `A> R`.
   Work at `A> R`, not the archive's `A> V R` checkpoint, to preserve exactly
   the recurrences in the paper. With u=v+1 and c=b+2, the two updates are
   `(u/2, c/2)` for even u, and `(u/2, 2*c-2)` for odd u. Prove `Good` as well
   as the scalar inequality after each new W.

7. Prove the pending-2 tail lemma and then the B return theorem for
   `b4_3RA` and `b4_2LA`. Strip zero bits, split on Z/W, and use the exact
   body effects:
   - Z: D^2 then append W;
   - W with 3RA: D^4 then append W;
   - W with 2LA: D^3 then append Z.
   In the W cases the first two decrements erase F/G safely. Enumerate early
   exits after that erasure. They have the form (8) in PROOF.md.

8. Treat the exceptional early reset using the exact raw-symbol re-parsing
   (11), not an assumed closure of even-terminal words. One intermediate
   overflow really has terminal R1. Omitting this case is a genuine gap.

9. Finish with the 156-step seed and positive-progress return induction, or
   a minimal-halting-time argument. The spinout branch uses the new 9-step
   identity in PrefixSafetySeed.lean. Positive progress is explicit in the
   first B transition, so zero-cost re-parsings cannot invalidate the final
   nonhalting argument.

## Existing results to reuse

- Machine.lean: `steps_trans`, `not_halts_within`, `init_five`.
- Nonhalt.lean: `Halts.of_run` and the existing spinout proof pattern.
- Pairing.lean: `Transparent.wrapX`, `Transparent.wrapZ`,
  `Transparent.append`, `transparent_reaches_left_end`.
- Counter.lean: `cval_decrement`, `cval_overflow`, `brun_F_consumed`,
  the reset-step and reset-end theorems.
- Overflow.lean: `cdec`, `brun_cdec`, `cdec_cval`, `ofw`,
  `brun_overflow_word`.
- Family.lean / Blocks.lean: exact G rules and soundness of block runs.

## Endpoint to certify

The eventual theorem statements should be

```
not_halts_3RA : Not (Halts (M b4_3RA) init)
not_halts_2LA : Not (Halts (M b4_2LA) init)
```

The proof package does not assert that these Lean declarations have already
been constructed or checked. `PrefixSafetySeed.lean` contains only the small
seed and spinout lemmas; it contains no axiom or sorry standing in for the
main return theorem.
