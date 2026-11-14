# Result of the halting/nonhalting attempt

## 1. Outcome and evidential status

I did not obtain a proof of halting or of nonhalting from the blank tape.
The main result is an exact, context-independent mixed-radix recurrence for
right excursions. It supports acceleration without assuming the global
binary-tail shape conjectured in the supplied analysis.

Two separately coded implementations reached **exactly `10^100` transitions**
without halting and agreed on the entire resulting configuration. This is
finite computational evidence, not an infinite-run proof. The local identities
below have a direct mathematical proof, but the proposed Lean formalization
has **not been compiled**. Neither the code execution nor the long endpoint is
being represented as a Lean-checked theorem.

The original definitions used are in `RequestProject/Machine.lean`; the local
outward/return rules are in `Macro.lean`; the cascade stoppers and frontier
invariant are in `Shield.lean` and `Frontier.lean`. The source archive already
contains `not_halted_before_hundred_million`; I did not rebuild that project.

The transition table, copied exactly into both evaluators, is:

| State | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| A | 1RB | halt | 3RA | 2LA | 2RB |
| B | 2LB | 3LA | 4LB | 4RA | 0RA |

## 2. An important limitation of the proposed arithmetic approach

The near-fourfold growth chains in `ARISTOTLE_SUMMARY.md` are not an established
global recurrence. In the displayed list, the two-entry change from 1,636,521
to 141,693,346 has correction

\[
141693346 - 4(1636521) = 135147262.
\]

Thus a universally small correction cannot be inferred from the preceding
stretch of near-fourfold growth. The supplied list itself leaves that regime.
This does not refute the local counter lemmas or the cascade-crossing theorem.
It does rule out using that empirical small-correction pattern as an induction
hypothesis without a more precise, phase-dependent statement.

Also, the maximal prefix using symbols `3`, `4`, and `0` is a changing cut in
the tape. A symbol `4` can belong either to the counter encoding or to a binary
pair. An arithmetic recurrence must track the interface, rather than assuming
that every number extracted by this rule describes one fixed set of digit
positions.

## 3. Define a completed right excursion

Write `F(u) = v` when the machine, entering the first cell of `u` in state A,
returns to the cell immediately to its left in state B, leaving `v` in place
of `u`. The rules below hold for arbitrary surrounding tape and arbitrary
boundary symbol. In the draft Lean source this is expressed as:

```lean
def ReturnRule (u v : List Sym) (n : Nat) : Prop :=
  forall (a : Sym) (l r : List Sym),
    iter n (some (onFirst St.A (a :: l) (u ++ r))) =
      some (Cfg.mk St.B l a (v ++ r))
```

The identities are conditional: a recursive expression on the right must be
supported by completed returns. They do not assert that every right excursion
returns. This distinction is essential for using them safely in a simulator.

### First rule: binary zero

\[
F(42x)=44x, \qquad \text{cost}=3.
\]

The transitions are `A4 -> 2RB`, then `B2 -> 4LB`, then `B2 -> 4LB`.
The head is back at the left boundary in B; the suffix `x` was untouched.

### Second rule: binary carry

\[
F(44x)=42F(x), \qquad \text{cost}=4+\text{cost}(F,x).
\]

The first two transitions rewrite `44` to `20` and enter `x` in A. When the
recursive return arrives in B on the second cell, `B0 -> 2LB` followed by
`B2 -> 4LB` completes the return and leaves `42`.

### Third rule: ternary replication of the return

\[
\boxed{F(2x)=2F^3(x).}
\]

The cost is four plus the sum of the costs of the three returns on the suffix.
Initially `A2 -> 3RA`. After the first suffix return, `B3 -> 4RA` starts the
second; after the second, `B4 -> 0RA` starts the third; after the third,
`B0 -> 2LB` returns to the outer boundary. The leading cell is restored to `2`.

Here `F^3` means three successive applications of the word transformation,
with a virtual restart at its left edge. Those virtual restarts have zero
cost in the abstract batch. The four surrounding transitions just described
are the actual physical transitions needed to realize them in the TM.

All three rules preserve the arbitrary outside contexts. By induction, their
finite compositions cannot contain a hidden halt: each component is a finite
sequence of defined transitions with the stated endpoint.

## 4. Exact batched carry arithmetic

Tokenize a suitable finite prefix into

\[
D=2,\qquad B_0=42,\qquad B_1=44.
\]

No claim is made that the entire reachable tape always has this form.
Suppose `k` virtual calls to `F` arrive at a token. The exact update is:

| Token | Output token | Calls passed to the suffix | Local transition cost |
|---|---|---|---|
| `2` | `2` | `3k` | `4k` |
| `42` | `42` if `k` even, `44` if odd | `floor(k/2)` | `3k + floor(k/2)` |
| `44` | `44` if `k` even, `42` if odd | `floor((k+1)/2)` | `3k + floor((k+1)/2)` |

Equivalently, for a binary token with bit `b`, write

\[
b+k=2q+b',\qquad b'\in\{0,1\}.
\]

Then it becomes `B_b'`, passes `q` calls right, and contributes `3k+q` steps.
Every non-carry call costs three local transitions; every carry call costs
four local transitions plus its suffix return. There are exactly `q` carries,
which proves the formula. For `2`, every outer call makes three inner calls
and contributes four surrounding transitions, proving the other row.

This gives a finite recursive certificate, not a growth extrapolation. A
successful certificate ends when the carry is zero; everything further right
is unchanged.

For example,

\[
F(2\,42\,42)=2\,44\,44
\]

in exactly 17 transitions: four around the leading `2`, plus binary-increment
costs 3, 7, and 3.

### A rational-valued interpretation

For finite token words, put

\[
V(\epsilon)=0,\quad
V(2x)=V(x)/3,\quad
V(42x)=2V(x),\quad
V(44x)=2V(x)+1.
\]

A successful batch of `k` returns satisfies

\[
V(\text{output})=V(\text{input})+k.
\]

Proof is by induction on the carry certificate. At `2`, the suffix increases
by `3k`, so the value of the whole word increases by `k`. At a binary token,
the suffix increases by `q`; the equality `2q+b'=b+k` gives the result.
The untouched terminal suffix can equally be assigned an arbitrary value;
the same argument works with that common boundary value.

This is a local counter interpretation. It does not define an established
global monotone potential for all of the machine's fallback transitions.

### A closed-form time count for a uniform prefix

Let `bin_m(b)` denote `m` binary tokens encoding `b` least-significant bit
first. If `b + r*3^n < 2^m`, then `r` virtual returns give

\[
2^n\,\operatorname{bin}_m(b)
\longmapsto
2^n\,\operatorname{bin}_m(b+r3^n),
\]

where `2^n` in this word expression means `n` repetitions of the tape symbol
`2`, not the integer power of two. The exact cost is

\[
r(9\cdot3^n-2)
+4\bigl(\operatorname{popcount}(b)
       -\operatorname{popcount}(b+r3^n)\bigr).
\]

For the leading dividers, sum `4r(1+3+...+3^(n-1))`. In the binary section,
the carry into bit `j` equals
`floor((b+r*3^n)/2^j)-floor(b/2^j)`. Summing the local costs and using
`sum_{j>=1} floor(z/2^j) = z-popcount(z)` gives the formula. The formula was
also compared with the carry evaluator on 1,000 finite cases. No inference
about whether such configurations continue to be reached forever is made.

## 5. Safe use in an accelerator

On state A, try the carry scan with `k=1`. A `2` triples `k`; a binary token
halves it with the appropriate remainder. Accumulate the exact transition
count and the proposed changes to the binary bits.

If the carry reaches zero, apply the complete plan and return the head one
cell left in state B. If it reaches any unsupported symbol/pair first,
**discard the entire plan without changing the tape**, and perform exactly
one literal transition. The same fallback applies when a successful macro
would overshoot the requested exact time.

This avoids the need for a global shape invariant to justify individual
jumps. Each accepted jump has its own finite local derivation. The fallback
explicitly executes the parts of the dynamics containing cascade starts and
possible halting. The successful macros contain no left-moving A transition
and never create a symbol `1`.

All transition counts and carries use arbitrary-precision integers. The code
contains no floating-point approximation for the tape or transition count.

## 6. Executed checks and endpoint

The executed tests are recorded in `checkpoints/reproduction_test.log` and
`checkpoints/validation.json`:

- 775 successful random single-return plans were compared with literal
  execution, including full tape, state, position, and exact transition count.
- 46 successful random batched-return plans were similarly compared with
  literal returns and the specified virtual restarts.
- On the blank run, all 2,258 accelerated endpoints up to one million literal
  transitions were compared with a step-by-step Python evaluator.
- C++ acceleration and literal C++ execution agreed on the full configuration
  at exactly `10^8` transitions.
- Separately coded Python and C++ accelerators agreed on the full configuration
  at exactly `10^100` transitions and reproduced the saved checkpoint.

The sampled tests are not exhaustive. The two accelerators share the same
mathematical recurrence, so agreement is not an independent proof of that
recurrence. Their purpose is to reduce implementation and counting mistakes;
the recurrence is justified by the transition-by-transition argument above.

The `10^100` checkpoint is:

| Quantity | Value |
|---|---|
| Completed transitions | `10^100` |
| State | B |
| Scanned symbol | `2` |
| Head coordinate | -14 |
| Recorded visited interval | [-229, 675] |
| Width | 905 cells |
| Accepted return macros | 73,988 |
| Literal fallback transitions | 466,258 |

The full tape, not just this summary, is in both checkpoint JSON files.
SHA-256 of its 905-character ASCII tape string:

```text
949f1aa2fbb077c0ade1203decf036bc3c287fa840306e2e6053f801342e6ba4
```

The C++ checkpoint additionally includes diagnostic counts of left-A events
and intervening `4` symbols. These are finite-run diagnostics only, not an
invariant or a complete classification of cascade births.

## 7. Proposed Lean extension

`RequestProject/MixedRadix.lean` proposes:

- `ReturnRule` and the three exact local return rules;
- `ReturnBatch`, with composition and parity cases;
- `MRAdd`, a finite carry certificate over the three token types;
- `mrAdd_sound`, turning a certificate into a batch of exact returns;
- `mrAdd_single_sound`, turning a single-carry certificate into a TM macro;
- `mrAdd_value`, proving the rational increment interpretation.

The file contains proof attempts without `sorry`, `admit`, or new axiom
declarations. **It was not compiled.** Elaboration or tactic failures may
remain. The original project specifies Lean 4.28.0 and mathlib v4.28.0;
use those versions when checking the extension.

Even successful compilation would certify only the stated local lemmas, not
the supplied Python/C++ programs or the `10^100` checkpoint. A certified long
run would additionally need an executable macro evaluator connected to the
local soundness theorem and a checked trace or evaluator result.

## 8. What is still needed for an actual decision

The completed-return rules remove a simulation bottleneck, not the global
reachability obstacle. When a carry reaches an unsupported symbol, control
passes to the literal dynamics. Those events change the interface, create or
move markers, and can initiate the leftward cascades that matter for halting.

The supplied `Shield.lean` already proves that suitable `4` or `00` stopping
blocks prevent a cascade from reaching a `1`, subject to the stated no-`1`
conditions on the intervening cells. The missing step is to derive an
appropriate stopper for **every reachable dangerous cascade**, and to connect
that property through all the intervening return and fallback events. I have
not proved this preservation statement.

A productive formulation is therefore an invariant on marked token words
and their active carry/phase, not a recurrence on the extracted ternary
number alone. The carry rules above give an exact transition relation for
one substantial part of such an invariant. They do not yet close its
exceptional cases.

**Final status:** no halting witness and no nonhalting proof were obtained.
There is an exact mathematical acceleration, reproducible finite evidence
through `10^100`, and an explicitly uncompiled Lean extension for its local
soundness rules.
