# Bigfoot `#829`: `a >= 3` after macro step 9 — a proof attempt

Target statement. Let `(a_k, b_k, c_k) = next^k (2, 0, 0)` for the accelerated map of
`M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA` (Bigfoot). Claim: `a_k >= 3` for every `k >= 9`.

Why it matters. Halting requires `a = 0` together with `b = 1 (mod 6)`, and `a` is changed only by
the rules `r = 0, 3` (+1) and `r = 1` (-1). So `a >= 3` from step 9 on excludes the halt branch
outright. This note records what a paper proof can and cannot currently establish.

## 1. The rule table

With `b = 6q + r`:

    r = 0 : (a, b, c) -> (a+1, 8q + c,     1)
    r = 1 : a = 0 -> halt
            a > 0 -> (a-1, 8q + c + 4,     0)
    r = 2 : (a, b, c) -> (a,   8q + c + 2, 3)
    r = 3 : (a, b, c) -> (a+1, 8q + c + 4, 0)
    r = 4 : (a, b, c) -> (a,   8q + c + 6, 1)
    r = 5 : (a, b, c) -> (a,   8q + c + 8, 0)

Write `s_r = 0, 4, 2, 4, 6, 8` for the additive constant of each rule, so that always
`b' = 8q + c + s_r` and `c'` is as above.

## 2. Lemma (the counter `b` never decreases)

For every step `next s = some s'`, one has `b' >= b`; equality happens only from `b = 0`, `c = 0`,
`r = 0`.

Proof. `b' - b = (8q + c + s_r) - (6q + r) = 2q + c + (s_r - r)`, and

    r=0: 2q + c          >= 0
    r=1: 2q + c + 3      >  0
    r=2: 2q + c          >= 0
    r=3: 2q + c + 1      >  0
    r=4: 2q + c + 2      >  0
    r=5: 2q + c + 3      >  0

so the difference is nonnegative, and it is zero only when `q = 0`, `c = 0` and `r = 0`, i.e. from
`b = 0, c = 0`. (The only such state on the orbit is the start `A(2,0,0)`; the next state
`A(3,0,1)` has `b = 0` again but `c = 1`, and `b` is strictly increasing from then on.) Combining
with the existing geometric bound `b' >= (4/3) b - 20/3` gives `b_k -> infinity`.

## 3. Lemma (the `a`-walk)

`a_0 = 2` and for every step

    a_{k+1} = a_k + 1   if r_k in {0, 3}
    a_{k+1} = a_k - 1   if r_k = 1
    a_{k+1} = a_k       if r_k in {2, 4, 5}

so with `N_{0,3}(k) = #{j < k : r_j in {0,3}}` and `N_1(k) = #{j < k : r_j = 1}`,

    a_k = 2 + N_{0,3}(k) - N_1(k).

Consequently `a_k >= 3` for all `k >= 9` is exactly the ballot inequality

    N_1(k) <= N_{0,3}(k) - 1      for every k >= 9.

## 4. The two special states

Direct computation of the orbit from `(2,0,0)`:

    k : 0      1      2      3      4      5      6      7      8      9
    a : 2      3      4      3      3      3      3      3      2      3
    b : 0      0      1      5      8     10     17     25     36     48
    c : 0      1      1      0      0      3      1      0      0      1
    r : 0      0      1      5      2      4      5      1      0      0

The only `a = 2` states in this prefix are `k = 0` and `k = 8` (`A(2,36,0)`), and the only
`a = 3, r = 1` state is `k = 7` (`A(3,25,0)`). At `k = 9` the state is `A(3,48,1)` with `r = 0`, so
the induction has to start there.

## 5. What has to be proved, and why the obvious induction fails

Since `a` decreases only under `r = 1`, the claim is equivalent to:

    (I)  no reachable state with k >= 9 has a = 3 and r = 1.

Attempt to prove (I) by induction. The ways to be at `a = 3` are:

  * entry from `a = 4` by a decrement (`r = 1`);
  * persistence at `a = 3` under `r in {2,4,5}`;
  * entry from `a = 2` by `r in {0,3}` — impossible once `a = 2` is gone, i.e. for `k >= 9`.

So (I) follows if

    (A) at a = 4, r = 1:  8q + c + 4 != 1 (mod 6), i.e. 2q + c != 3 (mod 6);
    (B) at a = 3, r in {2,4,5}:  8q + c + s_r != 1 (mod 6).

Neither is a consequence of the rule table, and the attempt dies here: the state space contains
legal counterexamples to both. For (A), `A(4, 1, 3)` is a legal state (`a = 4`, `b = 1 = 6*0+1`,
`c = 3`), and

    next (4, 1, 3) = (3, 0 + 3 + 4, 0) = (3, 7, 0),

whose residue is `1`, so it would land exactly on `a = 3, r = 1`. For (B), `A(3, 1, 0)` is legal
with `r = 1` already. Neither state is reachable from `(2,0,0)`, but that is precisely the extra
hypothesis the induction would need: a characterisation of reachable states at level `a = 4`, which
in turn needs the same statement at `a = 5`, and so on. The hierarchy does not close: the guard at
level `a` is a condition on `q mod 3`, i.e. on `b mod 18`, and one step consumes one ternary digit
(because `b' = 8*(b/6) + s` and `6` is not invertible modulo 3), so no fixed level of `b`-precision
suffices.

## 6. The potential-function route also fails

The natural global statement is a comparison of the two counters. If `b <= C * 6^a` for a constant
`C`, then `a >= log_6 b - log_6 C`, and since `b -> infinity` this gives `a >= 3` once
`b >= 6^(3 + log_6 C)`; the remaining finite prefix is checkable. But:

  * the ratio `P = b / 6^a` is not bounded by 1: over 300 000 macro steps the maximum of
    `log_2 P` is 81.5 (at `k = 1238`), i.e. `P = 6^31.5`, so `C >= 2^81.5`;
  * it is not a one-step invariant: under `r = 1` the ratio multiplies by
    `6 (8q + s) / (6q + 1) ~ 8`, under `r in {0,3}` it multiplies by
    `(8q + s) / (6 (6q + r)) ~ 2/9`, and under `r in {2,4,5}` by `~ 4/3`. The walk has a slight
    negative drift in `log P` but no one-step bound, so a proof would need a maximal inequality
    for the multiplicative walk, not an invariant.

## 7. Measurements (300 000 macro steps)

    a = 0                     never
    a = 2                     exactly k = 0 and k = 8
    a = 3, r = 1              exactly k = 7
    min a for k >= 9          3 (at k = 9 and k = 19)
    last k with a <= 4        20
    last k with a <= 6        27
    max a                     49 811 (at k = 300 000)

So the claim survives every check available, and `a` in fact grows without bound on average
(`a ~ log_6 b`, measured `16 601` against `log_6 b ~ 16 055` at `k = 100 000`). What is missing is
a proof that the walk's running minimum stays at 3; that is a ballot problem for the digit sequence
`r_k = b_k mod 6`, and nothing in the rule table implies it.

## 8. The maximal inequality attempt: a parity lemma

The inequality wanted is `P_k = b_k / 6^{a_k} <= C` for a constant `C`: then
`a_k >= log_6 b_k - log_6 C`, and since `b_k -> infinity` this gives `a_k >= 3` from some point on,
with a finite prefix to check. This section records the one genuine invariant found in the attempt,
and why it is not enough.

### 8.1 Lemma (parity of `b` is 4-periodic in `k`)

For every transition `next s = some s'`:

    b' = 8q + c + s_r,   s_r even      =>  b' = c  (mod 2)
    c' = 1 if r in {0,4}, 3 if r = 2, 0 if r in {1,3,5}
                                       =>  c' odd  <=>  r even  <=>  b even.

Hence `b'' = c' = 1 - b (mod 2)`, and with `b_0 = b_1 = 0` the pair `(b mod 2, c mod 2)` cycles

    (0,0) -> (0,1) -> (1,1) -> (1,0) -> (0,0),

so for every `k`:

    b_k even  <=>  k = 0,1 (mod 4);      b_k odd  <=>  k = 2,3 (mod 4);
    c_k odd   <=>  k = 1,2 (mod 4).

Verified with zero violations over 300 000 macro steps. Kernel-checked in `bbwork/cryptids_a6/BusyBeaver/BB33/M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean`: the step lemma is `parity_step`, the orbit
theorem is `parity_orbit`, and its two projections are `b_parity_orbit` and
`c_parity_orbit`; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

### 8.2 What the lemma gives the walk

`a` decreases only when `r = 1`, and by 8.1 that can happen only at `k = 2,3 (mod 4)`. `r = 0` (an
increment) only at `k = 0,1 (mod 4)`, `r = 3` (an increment) only at `k = 2,3`. Grouping steps into
blocks of four, with

    E = #{r = 0 at the two even phases},  O = #{r = 3 at the two odd phases},
    D = #{r = 1 at the two odd phases},

the change over a block is `E + O - D`, hence `-2 <= Delta a <= 4` per block. This is a real
constraint -- decrements are confined to half the phases -- but it is two-sided and does not keep
`a` positive: a block with `E = O = 0`, `D = 2` loses 2. Kernel-checked in the Bigfoot module: `a_step` is the per-step balanced identity
`a' + [r = 1] = a + [r = 0] + [r = 3]`, `blockE`/`blockO`/`blockD` are the counts, and
`block4_delta` proves `a4 + D = a0 + E + O` for any four consecutive transitions, with
`block4_delta_int` the integer form `Delta a = E + O - D`. The numerical bound is kernel-checked
separately: `block4_bounds` proves `a4 <= a0 + 4` and `a0 <= a4 + 2`, and `block4_bounds_int`
proves `-2 <= Delta a <= 4`. The proof uses `parity_step` to show that any four consecutive
states have exactly two even-`b` and two odd-`b` values, so `E <= 2` and `O + D <= 2`;
`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound`.

Both endpoints are attained. The legal runs
`A(2,1,6) -> A(1,10,0) -> A(1,14,1) -> A(1,19,3) -> A(0,31,0)` and
`A(0,0,24) -> A(1,24,1) -> A(2,33,1) -> A(3,45,0) -> A(4,60,0)` have `Delta a = -2` and
`Delta a = 4`, respectively; kernel-checked as `block4_lower_attained` and
`block4_upper_attained`.

Summing the four-step bound over complete blocks gives the cumulative drift bound. If
`runMacro n s0 = some s`, then

    a_s <= a_s0 + n,          a_s0 <= a_s + 2 * (n / 4) + min (n % 4) 2.

This is kernel-checked as `runMacro_bounds`, with integer form `runMacro_bounds_int`:

    -(2 * (n / 4) + min (n % 4) 2) <= a_s - a_s0 <= n.

The proof uses `runMacro_add` to split off complete four-step blocks and `runMacro_four_bounds`
for each block. The remaining `n % 4` steps are handled by `runMacro_remainder_bounds`: in
particular `runMacro_three_bounds` uses the parity lemma to show that three consecutive states have
at most two odd-`b` phases, so a three-step remainder loses at most 2 rather than 3. Hence the
remainder loss is `min (n % 4) 2`. `#print axioms` reports `propext`, `Classical.choice`,
`Quot.sound`.

The three-step loss of 2 is attained: the legal run
`A(2,1,9) -> A(1,13,0) -> A(0,20,0) -> A(0,26,3)` has `a = 2 -> 1 -> 0 -> 0`, so the first
two steps decrement and the third leaves `a` unchanged. Kernel-checked as
`three_step_bound_attained`.

The cumulative bound is tight at `n = 3` for the same witness: `runMacro_bounds` gives the
lower bound, and `runMacro_bounds_three_tight` proves it is attained with equality, since
`2 * (3 / 4) + min (3 % 4) 2 = 2`.

The upper cumulative bound is tight at `n = 4`: the four-step +4 witness
`A(0,0,24) -> A(4,60,0)` has `a_4 = a_0 + 4`, so the upper bound from `runMacro_bounds` is
attained with equality. Kernel-checked as `runMacro_bounds_four_upper_tight`.

The lower cumulative bound is tight at `n = 4` as well: the four-step -2 witness
`A(2,1,6) -> A(0,31,0)` has `a_0 = a_4 + 2`, so the lower bound from `runMacro_bounds` is
attained with equality. Kernel-checked as `runMacro_bounds_four_lower_tight`.

The lower bound is also tight at `n = 2`: the two-step prefix
`A(2,1,9) -> A(0,20,0)` has `a_0 = a_2 + 2`, kernel-checked as
`runMacro_bounds_two_lower_tight`.

At `n = 5` the lower bound remains tight, and the witness shows why the parity improvement stops:
`A(3,7,1) -> A(2,13,0) -> A(1,20,0) -> A(1,26,3) -> A(1,37,3) -> A(0,55,0)` has
`a = 3 -> 2 -> 1 -> 1 -> 1 -> 0`, three decrements in five steps. Hence the remainder loss for
`n = 5` cannot be reduced from 3 to 2 by the same argument. Kernel-checked as
`runMacro_bounds_five_lower_tight`.

### 8.3 Why it does not bound `P`

The per-step multiplier of `P`, by phase:

    even phase: r = 0  ->  ~ 2/9      r = 2 or 4  ->  ~ 4/3
    odd  phase: r = 1  ->  ~ 8        r = 3        ->  ~ 2/9      r = 5  ->  ~ 4/3

so one block can multiply `P` by about `(4/3)^2 * 8 * (4/3) = 512/27 ~ 19`, and the measured block
factors (log10) range from `-2.613` to `+2.056` (that is, `0.0024` to `114`), with 34 508 of the
74 999 blocks greater than 1. There is no block-level contraction. The drift of `log P` is only
`~ -0.011` per step, so a maximal inequality needs to know how the residues are distributed inside
each phase class -- i.e. information about `b mod 3`, which is exactly the 3-adic quantity that no
finite modulus captures (section 5 of this note, and section 12.3 of the exclusion note).

### 8.4 Status

The parity lemma is new and rigorous; it is the only exact invariant the walk has yielded. It
constrains the phase pattern but not the height, and the maximal inequality `P_k <= C`, hence
`a >= 3`, is still unproved.

A search for linear congruences `alpha*a + beta*b + gamma*c = const (mod m)`, for
`2 <= m <= 15` over the first 20 000 orbit states, found none. The low-`a` block barrier is also
false: even with `c` restricted to the reachable set `{0,1,3}`,
`A(3,4,1) -> A(3,7,1) -> A(2,13,0) -> A(1,20,0) -> A(1,26,3)` has
`a = 3 -> 3 -> 2 -> 1 -> 1`, so a four-step block starting at `a = 3` can end at `a = 1`. Thus the
remaining gap is reachability, not a fixed modular invariant or a universal low-`a` block bound.
The five-step witness above shows that the same parity method cannot improve the cumulative
remainder at `n = 5` either.

## 9. Conclusion

The paper proof does not close. What is established rigorously here:

  1. `b` is non-decreasing, and strictly increasing after the second step (`b_k -> infinity`);
  2. `a_k = 2 + N_{0,3}(k) - N_1(k)`, so `a >= 3` is equivalent to `N_1 <= N_{0,3} - 1`;
  3. the exact prefix through `k = 9`, with the two `a = 2` states at `k = 0, 8` and the last
     `a = 3, r = 1` at `k = 7`;
  4. the first induction step fails at `A(4,1,3) -> A(3,7,0)`: a legal state that violates the
     needed congruence, so reachability — not arithmetic — is the missing hypothesis;
  5. the comparison potential `b <= C * 6^a` is false for `C = 1` (max ratio `6^31.5`) and is not
     one-step inductive.
  6. the parity lemma of section 8.1: `b_k` is even exactly for `k = 0,1 (mod 4)`, `c_k` is odd
     exactly for `k = 1,2 (mod 4)`, so every decrement of `a` happens in the odd phase pair.
  7. the four-step block identity `Delta a = E + O - D`, kernel-checked as `block4_delta`
     (balanced form `a4 + D = a0 + E + O`) with integer corollary `block4_delta_int`.
  8. the block bound `-2 <= Delta a <= 4`, kernel-checked as `block4_bounds` and
     `block4_bounds_int` from the parity lemma and the block identity; both endpoints are
     attained by explicit legal four-step runs, kernel-checked as `block4_lower_attained`
     and `block4_upper_attained`.
  9. the cumulative drift bound `a_n <= a_0 + n` and
     `a_0 <= a_n + 2 * (n / 4) + min (n % 4) 2`, kernel-checked as `runMacro_bounds`
     and `runMacro_bounds_int`; at `n = 3` the lower bound is tight for
     `A(2,1,9) -> A(0,26,3)`, kernel-checked as `runMacro_bounds_three_tight`;
     at `n = 4` the upper bound is tight for `A(0,0,24) -> A(4,60,0)`,
     kernel-checked as `runMacro_bounds_four_upper_tight`, and the lower bound is
     tight for `A(2,1,6) -> A(0,31,0)`, kernel-checked as
     `runMacro_bounds_four_lower_tight`; the lower bound is tight at `n = 2` for
     `A(2,1,9) -> A(0,20,0)` and at `n = 5` for `A(3,7,1) -> A(0,55,0)`, kernel-checked
     as `runMacro_bounds_two_lower_tight` and `runMacro_bounds_five_lower_tight`.
 10. sharpness of the three-step loss: the legal run `A(2,1,9) -> A(1,13,0) -> A(0,20,0) ->
     A(0,26,3)` decrements `a` twice and has `a_3 = a_0 - 2`, kernel-checked as
     `three_step_bound_attained`.

A complete proof needs either a characterisation of the reachable `b`-residues at every level of
`a` (an infinite, 3-adic hierarchy), or a maximal inequality for `b/6^a`. Both are exactly the open
content of the Bigfoot cryptid.
