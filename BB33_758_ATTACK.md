# BB(3,3) #758 — proof attack state (2026-11-16)

Machine: `1RB2LC1RC_2LC---2RB_2LA0LB0RA` (holdout #758, "mahhaltum").
Wiki: <https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA>

This note records what is actually established, what is computational, and the
single remaining arithmetic obligation. Nothing here is a completed halting
proof.

## 1. The accelerated map

`A(a,c) = 0^∞ 1 2^a <C (20)^c 0^∞`, entered at `A(0,1)` after 2 steps.  The
ten rules (a)–(j) are implemented in `delta.c` / `wall.py` and are the published
dyuan01/LegionMammal978 contraction.  A **chain** starts at `A(1,c)` and ends
when it halts or returns to `A(1,c')`.

Established computationally (previous rounds, unchanged):

* all 26 published halting values below 10^6 reproduced exactly;
* rule paths for 12, 14, 2331, 2333 match the wiki labels;
* direct TM simulation from `A(1,12)`/`A(1,14)` halts at 5,153/5,193
  executed steps vs. rule cost 5,154/5,194 (the final halting attempt is not
  executed);
* max increment for `c ≤ 2^30` is Δc = 433 at c = 831,343,756 (140 rules);
* max increment for `c ≤ 2^27` is Δc = 415 at c = 33,053,026 (132 rules).

The map is **not monotone** in c.  A scan of c ≤ 10^6 found 478,481 decreases of
the chain endpoint F(c), so there is no monotone-envelope shortcut.  The step is
strictly increasing, however: every completed chain has c' > c.

## 2. The halting value and the wall (new extension)

Let

```
H = (3^307 - 8282708212) / 13959275        (463 bits, ~2.67e139)
```

`A(1,H)` halts: the chain is `j^292 bcbbccbbjbcbbcd` (307 rules), final config
`Halt(H+633)`.

Previous state: every c from `H-8,000,001` through `H-18,000,000` reaches H
(`wallmemo.c`, exact 768-bit arithmetic, 10M values, 28 s, 16 threads).

**New result (this session):** `wallmemo.exe 1 34000000 16` verified every c
from `H-8,000,001` through `H-42,000,000` reaches H:

```
selftest ok (k=1: 7391 chains; k=2 merges after 4162 chains, path 4162, seen 11553)
OK start=1 end=34000000 count=34000000 threads=16 total_chains=34695076 elapsed=117s
```

So the verified wall is at least

```
[H - 42,000,000, H - 3,403,055]      (38,596,946 consecutive values)
```

Every one of those values reaches H.  This matches the 41M figure reported in
the 2026-05-06 Discord thread and independently extends the repo's old 18M
bound.  It is conditional on the published rules and on `wallmemo.c` being
correct; it is not kernel-checked.

## 3. The exact sufficient condition

Write `F(c)` for the endpoint of the chain from `A(1,c)` (`F(c)=⊥` if the chain
halts).  The forward orbit is `c_{n+1} = F(c_n)` from `c_0 = 1`.

**No-overshoot lemma.**  Suppose

1. `F` is total and strictly increasing on `[1,H)`: for every `c < H`,
   `F(c)` is defined and `c < F(c)`;
2. `F(c) ≤ H` for every `c < H`;
3. `F(H) = ⊥` (the H-chain halts).

Then the machine halts at or before H.

Proof: the orbit is strictly increasing and bounded by H, hence cannot be
infinite; the only way out is a halt.  Equivalently, if the orbit avoided
halting, it would be an infinite strictly increasing sequence in the finite set
`{1,...,H}`.  This is formalized in
`cryptids_a6/BusyBeaver/BB33/M_758_Crossing.lean` and
`rocq/BB33_758_Crossing.v` as `reaches_of_no_overshoot` (the orbit reaches H)
and `halts_of_no_overshoot` (the machine halts).  Both files compile; see §6
for the exact commands and axiom checks.

A stronger sufficient condition is the uniform increment bound

```
Δc(c) = F(c) - c < 42,000,000    for every c < H,
```

because then the orbit cannot jump over the 42M-wide halting wall: if `c_n` is
the last orbit value below `H-42,000,000`, then `c_{n+1}` lies in
`[H-42,000,000, H)` and the wall takes over.  The wiki's stronger statement is
`Δc < 42M`; the weaker pointwise statement `F(c) ≤ H` is enough.

## 4. Why the wall alone is not a proof

`F(H-1)` is not close to H in the sense of monotonicity: F is not monotone, and
a single exceptional c below the wall with `Δc > H-c` would jump over both the
wall and H.  The wall is forward-invariant once entered (for `c` in the wall,
`F(c)>c` and `F(c)≤H`), but entering it is exactly the unproved step.  The
current forward frontier is only `c ≈ 1.06e15` (LegionMammal978's direct run,
`10^27` TM steps), so the orbit cannot be simulated to the wall.

## 5. The remaining obligation, precisely

Prove one of:

```
(P)  ∀ c < H,  F(c) is defined and F(c) ≤ H
```

or the stronger

```
(B)  ∀ c < H,  F(c) - c < 42,000,000.
```

The chain rule table gives `t = a+2c` increasing by 3,5,9,8,5,8,4 per rule and
`Δc = (t'-t)/2` at a return, so (B) follows from a bound of about 9.3M rules
per chain.  The empirical maximum is 140 rules at `c ≤ 2^30`; chains at
`c ≈ 10^18` sampled 116 rules.  A bound of 10,000 log2(c) rules would give
≈4.6M rules at H, hence Δc ≈21M, inside the wall.

Candidate proof routes, in order of current promise:

1. **Base-3 digit transducer.**  The initial j-run from `A(1,c)` has length
   `k ≈ log_3 c` and leaves `c - 3^k + O(k)`, i.e. it strips the leading base-3
   digit.  Each subsequent b/c step multiplies c by 3/2 and each j-run strips a
   new leading digit.  If each cycle consumes at least one base-3 digit, the
   number of cycles is ≤ log_3 H ≈ 293 and the rule count is O((log c)^2) ≈
   86,000, far below 9.3M.  This is the most concrete route to (B).
2. **Expanding-map measure bound.**  In the `(u,d)` coordinates the b/c
   branches have slope 9/4 and the j branch slope 3; the h/reset interval is the
   middle third.  The survivor set is a cookie-cutter Cantor set.  A certified
   transfer-operator bound (finite Markov partition, rational interval
   arithmetic) with any contraction ρ<1 gives max chain length
   `≈ 139 ln10 / ln(1/ρ)`; ρ=0.9 already gives ≈3,000 rules.  Formalizing the
   partition is heavier than route 1.
3. **Forward-invariant wall plus a verified block map.**  The wall is verified
   to 42M.  If the block map on `[H-84M, H-42M]` can be shown to land in the
   wall by a symbolic interval computation, the wall extends; iterating this
   block argument cannot reach c=1 (it needs ~H/42M blocks), so this only helps
   near the wall, not for the whole range.

## 6. Formal artifacts

* `cryptids_a6/BusyBeaver/BB33/M_758_Crossing.lean` — Lean 4 proof of
  `no_infinite_strict_mono_bounded`, `reaches_of_no_overshoot`, and
  `halts_of_no_overshoot`, with a concrete `demo`.
* `rocq/BB33_758_Crossing.v` — Rocq 9.1 proof of the same three results and
  the same `demo`, using an explicit `iter` and classical choice.
* `delta.c`, `wall.py`, `wallfast.c`, `wallmemo.c` — the computational chain
  map and wall scanners (not proof-checked).
* `delta.exe` trace from the community frontier:
  `A(1,1059491543272883)` reaches `A(1,1059491543272961)` in 38 rules,
  Δc=78.

### Compiled and run (2026-11-16)

```
cd cryptids_a6 && lake env lean BusyBeaver/BB33/M_758_Crossing.lean
exit 0; #print axioms demo reports [propext, Classical.choice, Quot.sound],
with no sorryAx

cd rocq && rocq compile -Q . Top BB33_758_Crossing.v
exit 0; BB33_758_Crossing.vo written;
Print Assumptions halts_of_no_overshoot = Classical_Prop.classic

Eval compute in (iter demoNext 2 1)              = 3
Eval compute in (demoStep (iter demoNext 2 1))   = None
```

These files prove only the combinatorial crossing step.  They do **not** prove
(P) or (B), and therefore do not prove that the machine halts.

### Empirical chain scaling (`chain_scale.py`)

Random starts at increasing bit sizes give maximum chain lengths:

| bits | 32 | 64 | 96 | 128 | 192 | 256 | 320 | 400 | 463 | 600 | 1000 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| max rules | 86 | 101 | 125 | 143 | 202 | 239 | 254 | 301 | 356 | 422 | 687 |

The maximum tracks a small multiple of `log_3 c` (about 1.1-1.2 at large
sizes), which is why a logarithmic rule bound would comfortably give (B).
But the samples are not a proof, and the recursion test
(`chain_recursion.py`) gives no simple `L(c) ≤ L(c/3)+O(1)` law: the maximum
difference was already 66 at c=1,079,656.

## 7. Status against the literature (2026-11-16)

The BusyBeaverWiki page for this machine was last edited on 7 November 2026
and still labels it an **unsolved problem**.  Its own summary of the missing
step is:

> However, we cannot prove that the forward iteration reaches this long
> stretch instead of skipping past it. ... So if we want to fully prove that
> this machine halts at or before A(1,H), we must place an upper bound on Δc
> for every step leading up to it. But given the size of H, there is no known
> practical method to compute such an upper bound.

So the gap is a documented open problem, not a missing local tactic.  A
completed proof must contain a kernel-checked derivation of (P)/(B) and a
kernel-checked (or certificate-checked) wall verification.  Per the project
rules in `AGENTS.md`, a halting claim is only to be announced when both
compiled files exist and the numerical premises are discharged.

## 8. What would finish it

1. Prove a universal chain-length bound `L(c) ≤ K log_2 c` with `K` small
   enough that `(9/2) K log_2 H < 42,000,000`.  Empirically `K≈2` is ample;
   even `K=1000` would suffice (`≈2.1M`).
2. Formalize that bound in both Lean and Rocq, then instantiate
   `halts_of_no_overshoot` with the 10-rule chain map and `H`.
3. Replace the computational wall by a kernel-checked certificate, or verify
   the wall values inside the proof assistant.

A promising route for step 1 is the `(u,d)` expanding map in §5: every
`b/c` pair multiplies the distance to the exit interval by `9/4`, and every
`j` step multiplies the distance to the upper edge by `3`.  The missing piece
is a uniform bound on the number of alternations, not on the length of a
single run.

## 9. New angle (2026-11-16): 3-adic renormalization of the return map

This is the first structural lead found that is not in the wiki/community
analysis, and it has enough quantitative margin to close (B) if proved.

### Exact `j`-run alignment

For a chain start `A(1,c)`, the initial run of `j` steps has the closed form

```
a_i = 2*3^i - 1,      c_i = c - 3^i + 1 + 2i.
```

The run stops at the first `i` with `c_i < a_i`.  For `c = 3m`, the `j`-run is
one step longer, and comparing the two post-run states gives the exact
identity

```
S(3m) = (3*a + 2, 3*c - 4*k),      3*S(m) = (3*a, 3*c),
```

where `(a,c)` is the post-`j` state of `m` and `k` is its `j`-run length
(`k = O(log m)`).  Thus the two chains start from states differing only by
`(2, -4k)` in a common frame.  This is a renormalization identity, not a
statistical approximation.

### Measured defect (`scale3_exact.c`, exhaustive)

| N | max abs `L(3m)-L(m)` | max abs `L(3m+1)-L(m)` | max abs `L(3m+2)-L(m)` |
| --- | --- | --- | --- |
| 10^8 | 86 | 116 | 87 |
| 10^9 | 110 | 128 | 106 |
| 10^10 | 111 | 141 | 125 |

At the same time, for `r=0` and `r=2` the exact identity `L(3m+r) = L(m)+1`
held for **97.5% of m at 10^8** and **98.6% at 10^9**.  The maximum defect
tracks `6.2 * ln m` (116/18.4, 128/20.7, 141/23.0), so the natural conjecture is

```
(R)  |L(3m+r) - L(m)|  <=  C * ln m,      C ~ 6.2 observed.
```

Separately, the **return map** satisfies the same renormalization:
`F(3m) = 3*F(m) + O(log m)`; the measured error divided by bit length was
2.85 at 1000 bits (`return_scale.py`).

### Why this is enough

Iterating (R) down by factors of 3 gives

```
L(c) <= L(1) + C * (ln c)^2 / (2 ln 3).
```

At `c = H`, `(ln H)^2/(2 ln 3) ~= 46,900`, so `L(H) <= 46,900 C` and
`Δc <= (9/2)L(H) <= 211,000 C`.  Entering the verified wall needs
`Δc < 42,000,000 - 3,403,055 ~= 38.6M`, i.e. **C < 183**.  The observed
`C ~ 6.2` leaves a factor-30 margin; even `C=100` gives `Δc < 21.1M`.

So (R) is a sufficient replacement for the wiki's missing `Δc` bound, and it
is a much weaker statement than the logarithmic/Poisson heuristic.

### Proof target: shadowing under `(2, 4k)`

The perturbation `(2, 4k)` is `O(log m)` while the state is `~3^k`.  The
linearized maps expand it, so it only becomes comparable to the state when
the state has shrunk to `O(k)`.  The remaining chain from a state of size
`O(k)` can be bounded by a finite check over all states of size `<= Ck`
(a few thousand at `H`), giving `|L(3m)-L(m)| <= Ck`.  The technical work is
the mod-4 branch crossing: `c` and `3c` can be in different residue classes,
so the two chains may use `b` versus `c`; those two rules differ only by
constants and re-synchronize in the `(a,c)` plane.

An alternative is to prove `F(3m)=3F(m)+O(log m)` by induction on the chain
(the endpoint version of the same shadowing statement) and derive (R).

**Update 2026-11-16 (see §11):** (R) survives the stress test, but this
shadowing proof target is false as a route.  The worst defects are cases
where the two chains separate at step 1 and one exits after ~26 steps while
the other runs ~167; the defect can equal an entire chain length.  A common
prefix plus a finite tail check cannot prove (R); a global chain-length bound
is still required.

### Routes tested and ruled out

* `k`-automatic structure: the `k`-kernel of `L` and of the defect does not
  stabilize for `k=2,3,4,6` (`kernel_test.py`, `defect_kernel.py`).  Base 6
  merges partially but not finitely; naive automaticity is false.
* odd-scaling invariance: `L(ka,kc)=L(a,c)` for odd `k` is false exhaustively
  (`odd_scale.py`; e.g. `L(4,1)=1`, `L(12,3)=4`).  The renormalization is
  special to the chain-start `j`-run, not a general symmetry.
* simple `L(c) <= L(c/3)+O(1)`: false; the maximum difference was already 66
  at `c=1,079,656` (`chain_recursion.py`).  (R) is the correct weaker form.

### Other novel routes still open

1. **2-adic transfer operator.**  Every `b/c` step divides `c` by 2 and adds a
   constant; the chain map is a contraction in the 2-adic metric.  Bound the
   survivor set of the exit interval with a non-Archimedean potential/measure
   argument instead of the Archimedean Cantor-set one.
2. **Certified survivor-set computation.**  Represent the set of `c < H`
   surviving `n` steps as a BDD or a union of affine intervals.  If it is empty
   at depth `n ~ log H`, (P) follows.  Naive interval count doubles each step;
   the affine mod-4 structure may merge heavily.
3. **Merge-DAG certificate for the wall.**  `wallmemo.c` already builds a
   `seen` set of 38M values that merge to `H`.  Hash-cons that DAG and verify
   each edge by one chain step; this would make the wall kernel-checkable,
   which is the other missing premise.
4. **`42M ~ 3^16`.**  The verified wall width is suspiciously close to
   `3^16 = 43,046,721`.  If the halting basin contains a residue class modulo
   `3^16`, the orbit only has to hit that class, and the mod-`3^16` dynamics is
   a finite Markov chain with 43M states (feasible).
5. **Ranking-function synthesis.**  Search for a piecewise-linear
   `Φ(a,c) = α log a + β log c` (or a linear combination of bit lengths) that
   decreases along every `b/c` and `j` run.  Such a Φ would give `L=O(log c)`
   directly; the rule table is small enough to solve the resulting linear
   program.

## 10. Results of 2026-11-16 (second session): three routes measured

Three of the routes above were tested directly; two are dead and one is
sharpened.  Scripts: `shadow_sync.py`, `wall_residue.py`,
`identity_exceptions.py`, `wall_blocks.py`.

### (a) Route 4 (residue class mod 3^16) -- DEAD

120 random wall values have **120 distinct residues** modulo 3^16 (and
mod 3^15, 3^14).  `H mod 3^16 = 27,607,933`; the wall width 38,596,946 is
just under 3^16 = 43,046,721, which is why the coincidence looked real.
The wall is a genuine interval, not a residue class.

### (b) Block certificate for the wall -- DEAD in the naive form

For a random wall value the rule word has length 300-583, and the
**immediate neighbours c +/- 1 already have a different word**: max block
width found is 1.  Among 200 consecutive wall values there are 132 distinct
words.  A per-value certificate would need 38.6M distinct words, so interval
arithmetic on constant-rule blocks cannot certify the wall.

### (c) Shadowing for (R) -- sharpened, exact state merge false

`shadow_sync.py`, 4000 random 120-bit m, chains from m and 3m+r:

| r | max abs dL | p99 | mean | exact state merge |
| - | ---------- | --- | ---- | ----------------- |
| 0 | 1 | 1 | 1.00 | 0/4000 |
| 1 | 60 | 31 | 6.60 | 0/4000 |
| 2 | 1 | 1 | 1.00 | 0/4000 |

So for r = 0 and 2 at 120 bits the identity `L(3m+r) = L(m)+1` held **every
time**, and r = 1 is the entire source of the defect.  But the two orbits never
become the same state: the shadowing is at the level of the rule word, not the
state.  A proof of (R) therefore cannot be "the perturbation collapses to 0";
it must be "a bounded perturbation changes the rule count by O(log)".

Exhaustive small scan (`identity_exceptions.py`, m <= 60,000) shows the
identity is false for small m -- e.g. L(1)=3 but L(3)=7 -- with max defects
55 (r=0), 72 (r=1), 59 (r=2).  Exceptions are frequent at small m and rare at
120 bits (0/4000), so the defect is a boundary phenomenon: the natural lemma
is `L(3m+r) <= L(m) + 1 + C*log2(m)` with a small C, not an exact identity.

### Next

The (R) route stays the only live one.  The work item is now precise: bound
the rule-count difference of two chains whose *words* differ only where the
mod-4 branch (a/b/c) or the parity branch (h/i/j) chooses differently, over a
common prefix.  That is a finite automaton on the (a,c) difference, not a
measure-theoretic argument.

## 11. Stress test of (R), failure of the shadowing premise, and the conditional bound (2026-11-16, third session)

### Numerical stress (`stress_huge.py`)

The test covers random huge `m` (300 samples at 128-1000 bits, 50 at
2000/5000 bits, 20 at 10,000 bits, all three residues), the known worst
`m` scaled by `3^e`, and a 40-restart x 200-step bit-flip hill climb that
maximizes `|L(3m+r)-L(m)|/ln m`.

| test | worst `|defect|/ln m` | worst defect |
| --- | --- | --- |
| random 128 bits | 0.544 | 48 |
| random 463 bits | 0.115 | 37 |
| random 1000 bits | 0.052 | 36 |
| random 10,000 bits | 0.003 | 21 |
| hill climb 128 bits | 1.465 | 129 |
| hill climb 256 bits | 0.526 | 93 |
| hill climb 512 bits | 0.211 | 75 |
| hill climb 1024 bits | 0.137 | 97 |
| scaled known worst, `m*3^36` | 0.406 | 25 |

No test came within a factor of 28 of the bound 183.  The largest ratio seen
anywhere is still the small exhaustive maximum `141/ln(3814756888) = 6.39`.
Scaling the worst values by `3^e` makes the defect stabilize at 25 or 1,
while `ln m` grows, so the ratio falls.  Empirically (R) holds with a wide
margin.

### The shadowing premise is false

The defect is not a small perturbation effect.  The traces in
`worst_trace.py` show:

| m | r | L(m) | L(3m+r) | defect | common prefix |
| --- | --- | --- | --- | --- | --- |
| 3,814,756,888 | 1 | 26 | 167 | 141 | 0 |
| 3,814,756,887 | 2 | 42 | 167 | 125 | 20 |
| 460,381,866 | 0 | 50 | 160 | 110 | 18 |
| 831,343,756 | 0 | 140 | 63 | -77 | 16 |
| 33,053,026 | 0 | 132 | 49 | -83 | 0 |
| 546,567 | 0 | 91 | 28 | -63 | 12 |

For `m = 3,814,756,888`, the aligned states differ only by `(2,4k)`, yet the
chain from `m` exits after 26 steps and the chain from `3m+1` runs 167.  The
defect equals the **entire longer chain**, not a discrepancy between two
chains that shadow each other.  In the other direction, `m = 831,343,756`
has a 140-step chain while `3m` exits in 63.  The chains separate immediately;
there is no common-prefix-plus-small-tail structure to check.

Consequently the proof target in §9 cannot work as stated.  Bounding the
defect is equivalent in difficulty to bounding the longer of the two chains.
The numerical statement (R) is still the sharpest sufficient inequality, but
it is a **global chain-length bound in disguise**, not a shortcut around the
wiki's missing bound.

### What is actually proved

The conditional arithmetic is formalized and compiled:

* Lean: `cryptids_a6/BusyBeaver/BB33/M_758_Quadratic.lean`
  * `quadratic_chain_bound`: if
    `L(3m+r) <= L m + C*(t+1)` for all `m < 3^t`, `r < 3`, then
    `2*L c <= 2*L 1 + C*t*(t+1)` for all `1 <= c < 3^t`.
  * `at_292`: with `C = 100` and `t = 292`,
    `2*L c <= 2*L 1 + 8,555,600`, hence `L c <= 4,277,800 + L 1` and
    `Δc <= (9/2)*L c < 19.3M < 38.6M`.
  * `delta_window`: the `Δc` conversion.
  * Compiled with `LEAN_EXIT=0`; `#print axioms` shows only `propext`,
    `Classical.choice`, `Quot.sound`; no `sorryAx`.
* Rocq: `rocq/BB33_758_Quadratic.v`
  * Same three theorems (`delta_window_z` is the `Z` arithmetic form).
  * `rocq compile -Q . Top BB33_758_Quadratic.v` exit 0; all three
    `Print Assumptions` report "Closed under the global context".

The hypothesis of these theorems is exactly (R); it is **not proved**, and
the stress test does not prove it.

### Revised assessment

(R) remains the best sufficient target, but two things are now clear:

1. A proof must bound the longer chain globally.  A direct crude bound
   `L(c) <= K ln c` with `K < 26,700` would already give the wall window; the
   observed `K ~ 6.2` suggests a constant like `K = 1000` is enough, and that
   is much weaker than (R).  The measure/2-adic survivor-set routes in §9
   target this directly and do not require shadowing.
2. The exceptional cases are exactly where one chain exits early.  A hybrid
   route is possible: certify the short chain by its finite rule word, and
   bound the long chain by the global method.  The worst-case table above is
   the test set for such a split.

Do not formalize (R) as an axiom, and do not claim the wall is proved from
the conditional theorems above.

## 12. The increment invariant and the constant-defect target (2026-11-16, fourth session)

### Exact invariant

Define the **potential**

```
Q(a,c) = a/2 + c.
```

Every non-halting rule increases `Q` by a fixed positive constant:

| rule | `Q' - Q` |
| --- | --- |
| `j` | `2` |
| `i` | `4` |
| `a` (c even) | `3/2` |
| `b` | `5/2` |
| `c` | `9/2` |
| `e` | `4` |
| `h` | `5/2` |

At the final `h`, `F(c) = Q_final + 2`; at the start, `Q_initial = c + 1/2`.
Therefore

```
D(c) := F(c) - c = 3/2 + (sum of the rule weights).
```

This is exact.  `D(c)` is the **weighted length** of the chain word, not the
ordinary length.  It also explains why the chain-length defect and the
increment defect behave differently: the weights of `j` and `i` are 2 and 4,
but the `b/c` weights are larger (`c` costs 9/2), and different words can have
very different ordinary lengths with almost the same total weight.

### The increment defect is bounded (new data)

`increment_scale.c` scans `D(Bm+r)-D(m)` for all `m <= N`.

| base | N | max defect | min defect |
| --- | --- | --- | --- |
| 3 | `10^7` | +333 | -295 |
| 3 | `10^8` | +380 | -376 |
| 3 | `10^9` | +412 | -390 |
| 3 | `10^10` | not completed (scan stopped) | |
| 2 | `10^8` | +365 | -376 |
| 2 | `10^9` | +444 | -386 |

The defect is stable at a few hundred, while the **chain-length** defect at the
same scales is already 141 and the chain-length inequality needs the constant
183.  The increment defect is a much better object: it is bounded by a
constant, not by an entire chain length.

Random endpoint increments grow only logarithmically:

| bits | 128 | 256 | 463 | 1000 | 2000 | 5000 | 10000 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| max `D` | 296 | 446 | 700 | 1371 | 2607 | 6379 | 12696 |

That is about `1.27 * bits`, consistent with a constant defect per binary
digit.

### Base-2 pair identity

For `m >= 1`:

```
A(1, 2m+1) --j-->    A(5, 2m+1)
A(1, 2m)   --i,j-->  A(11, 2m+1)
```

Both chains land on the **same `c`**, with `a = 5` versus `a = 11`: a fixed
perturbation of size 6, not an `O(log m)` perturbation.  Measured endpoint
difference `G(11,c)-G(5,c)`:

* `c <= 200,000` (odd): max `+227`, min `-186`;
* random 64/128/256/463/1000-bit `c`: max `|difference|` about 180.

The two chains can have very different lengths (e.g. `c = 139,233`: 11 versus
82 rules), but their endpoints differ by only 227.  This is the **opposite**
of the failed length shadowing: the endpoint is stable, the word is not.

Moreover, the two rule words usually **re-synchronize**: among 49,999 odd
`c < 100,000`, 49,951 have a nonempty common rule suffix (maximum suffix
length 11).  The endpoint difference remains at most 186 even in the
non-synchronizing cases.  This supports a finite divergence-window proof of
the fixed-perturbation lemma, not a global shadowing proof.

### Formal reduction

The constant-defect target is now formalized in both systems:

* `cryptids_a6/BusyBeaver/BB33/M_758_Increment.lean`
* `rocq/BB33_758_Increment.v`

The theorem `increment_bound`:

```
if  D(2c) <= D(c) + K  and  D(2c+1) <= D(c) + K  for all c >= 1,
then  D(c) <= D(1) + K*t  for all  c < 2^t.
```

At `t = 463`, `K = 80,000`, this gives `D(c) <= D(1) + 37,040,000`, and
`D(1) = 7`, so `D(c) < 38.6M` for **every** `c < 2^463`, not only `H`.
Both files compile; Lean has no `sorryAx`, Rocq is closed under the global
context.

The remaining obligation is now the single constant-defect statement

```
(S2)  exists K <= 80,000,  forall m >= 1, r in {0,1},
        |D(2m+r) - D(m)| <= K.
```

A proof of (S2) proves (B) for the whole range below the wall.  The pair
identity is a stepping stone for the `2m`/`2m+1` half of (S2), but it does
not by itself relate `D(2m)` to `D(m)`; that scale relation is still the
missing lemma.

### Next attacks

1. Prove the fixed-perturbation endpoint lemma for `(5,c)` versus `(11,c)`.
   The perturbation is 6 at the same `c`; the observed endpoint error is
   bounded by ~230.  A finite-state/interval argument on the first divergence
   is the natural proof.
2. Prove (S2) directly from the `Q` weights: the base-2 scaling changes only
   the first few rules, and the weighted word difference is a finite
   automaton on the low bits of `m`.
3. Use the neutral 2-cycle at ratio `a/c = 3/2`: its derivative is `9/2`, so
   deviations expand, while the denominator grows; a Diophantine/denominator
   argument should bound the exit time by `O(log c)`.

## 13. The base-2 pair: proved `Q` core and the remaining gate

### What is now proved and formalized

The `Q` invariant is formalized in both systems:

* `cryptids_a6/BusyBeaver/BB33/M_758_QInvariant.lean`
* `rocq/BB33_758_QInvariant.v`

For `Q(a,c)=a+2c`, every valid rule has an exact increment:

```
j:4  i:8  a:3  b:5  c:9  e:8  h:5
```

The theorem `Q_apply` covers all seven rules with their branch side
conditions.  The base-2 start identities are also formalized:

```
A(1,2m+1) --j-->    A(5,2m+1)
A(1,2m)   --i,j-->  A(11,2m+1)
```

and the **same-word endpoint lemma**:

```
if both chains use the same rule word and end at pre-h states (x1,y1),
(x2,y2) with even x1,x2, then
    x2/2 + y2 + 2 = x1/2 + y1 + 5,
i.e. F(11,c) = F(5,c) + 3.
```

This is proved from the `Q` cross-invariant `Q(apply r p1)+Q p2 =
Q(apply r p2)+Q p1`; the proof is in `Q_run_cross` and
`pair_endpoint_same_word`.  Lean has no `sorryAx` (axioms `propext`,
`Quot.sound`); Rocq reports "Closed under the global context" for all five
printed results.

The pair-plus-scale reduction is also formalized:

```
pair defect  |D(2m)-D(2m+1)| <= Kp
scale defect |D(2m+1)-D(m)|  <= Ks
            =>  |D(2m+r)-D(m)| <= Kp+Ks.
```

This is `constant_defect_of_pair_and_scale` in both files.  It is the exact
logical use of the pair lemma in the constant-defect attack.

### What is not proved: the unconditional pair bound

The same-word lemma does not cover the actual `(5,c)`/`(11,c)` pair when the
rule words differ.  The measured endpoint differences are:

| range | max abs `F(11,c)-F(5,c)` |
| --- | --- |
| `c <= 200,000` odd | 227 |
| `c <= 10^8` | 377 |
| `c <= 10^9` | 391 |
| `c <= 10^10` | 421 |
| random 2,000–50,000-bit `c` | about 100 |

The difference grows slowly, consistent with `O(log c)`, not with a tiny
constant.  The `Q` argument gives the exact conditional bound

```
|F(11,c)-F(5,c)| <= 3 + (9/2) * W(c),
```

where `W(c)` is the total number of steps in the divergence window (the steps
outside the common rule prefix and suffix).  At the worst `10^10` point
`c=1,785,376,179`, the window is 137 for a 31-bit `c`; at `c=34,579` it is 65
for a 16-bit `c`.  Thus a proof of `W(c) <= 38 log_2 c` would give a pair
defect below `80,000` at 463 bits, and hence the wall.  That window bound is
the remaining open lemma.

The two rule words usually re-synchronize: among 49,999 odd `c < 100,000`,
49,951 have a nonempty common suffix (max suffix 11).  The hard cases are the
few non-synchronizing or long-window cases; they are not excluded by the
same-word theorem.

### Consequence for `(S2)`

The pair lemma, once extended to the actual common-suffix/differing-word case,
controls only the `2m` versus `2m+1` half.  The scale half
`D(2m+1)` versus `D(m)` is still needed.  Both halves must be proved before
the compiled constant-defect reduction can be instantiated.  No halting or
non-halting claim is made.

### Length-based endpoint bound (new, compiled)

The same-word lemma is now supplemented by a quantitative bound that covers
**all** word pairs, including non-synchronizing ones.  `Q_run_le` and
`Q_run_ge` give, for any valid word `w`,

```
Q p <= Q(run w p) <= Q p + 9*length(w).
```

Therefore, if the `(5,c)` word has length `L5` and the `(11,c)` word has
length `L11`, then for even endpoints

```
2*F(5,c)  <= 2*F(11,c) + 9*L5,
2*F(11,c) <= 2*F(5,c)  + 6 + 9*L11.
```

Equivalently,

```
|F(11,c)-F(5,c)| <= (9*max(L5,L11) + 6)/2.
```

This is `pair_endpoint_length_bound` in both formal files.  It is fully proved
from `Q_apply`; the only input left is a bound on the two rule-word lengths.

The empirical lengths are far below what is needed.  At 463 bits, 20 random
chains had lengths 291-312 (both starts), and the worst 463-bit samples in
`chain_scale.py` were 356.  The constant-defect reduction needs `K=80,000`;
the length bound gives that from

```
(9*L + 6)/2 <= 80,000   <=>   L <= 17,777.
```

So a universal bound `L(c) <= 17,000` for 463-bit `c` would discharge the
**pair half** of (S2).  This is much weaker than the earlier window bound and
is the sharpened target.  A cruder bound `L(c) <= 86,000` would also give
`D(c) <= 1.5 + 9*86,000 = 774,001.5`, already inside the 38.6M wall directly,
bypassing the constant-defect induction entirely.

The remaining unproved statement is therefore a universal chain-length bound
for the 10-rule map, not a constant bound on the endpoint difference.  Route 1
of §5 (each cycle consumes a base-3 digit, giving O((log c)^2)) is the
candidate; the recursion tests in `chain_recursion.py` show that a simple
`L(c) <= L(c/3)+O(1)` law is false, so the digit-consumption argument must be
made global rather than per-prefix.

### Segment-length attack at 463 bits

Every segment starts at `A(1,c)`.  The first run is almost always a pure `j`
run, and its state has the closed form

```
after k j-steps:  a_k = 2*3^k - 1,
                  c_k = c - 3^k + 1 + 2*k.
```

The run stops at the first `k` with `a_k >= c_k`.  At the preceding step
`a_{k-1} < c_{k-1}`, which gives `3^k < c + 2*k`; hence `k <= log_3(c+2k)`,
and at 463 bits this is at most 292 steps.  (The final-step inequality alone
only gives a lower bound, so the previous-step inequality is the one used.)  In 200 random 463-bit segments the
observed lengths were 291-320, with the first `j` run contributing 291-292 and
the entire remaining tail contributing at most about 28 steps.  The same
pattern persists at 1,000, 5,000, 20,000, 50,000 and 100,000 bits: the maximum
length is `0.6309*bits + 13..29`, not a growing multiple of `log_3 c`.

Exhaustive small ranges show the tail can be larger in absolute terms when
`c` is small: at `c < 2^24` the maximum segment length is 109 (at
`c = 2,715,403`), i.e. a tail of about 94 over `log_3 c`.  This is still far
below 17,000.  The structural target is therefore a **tail bound**, not a
second long `j` run.

A sufficient weakened target is

```
L(c) <= 50 * log_3 c,
```

which is about 14,600 at 463 bits.  The length-based endpoint theorem turns
any such bound into `K <= (9*14,600+6)/2 ~ 65,700`, inside the required
`80,000`.  Proving the tail bound uniformly is the remaining chain-length
lemma; the initial `j`-run formula above is the exact, formalizable part.

### Formal status of the prefix and tail (2026-11-17)

The prefix is now formalized in both `M_758_QInvariant.lean` and
`BB33_758_QInvariant.v`:

```
jIter k (1,c) = (2*3^k - 1, c - (3^k - 1 - 2*k))
```

with `JValid_prefix`, `JValid_last`, and `j_run_length_le_292` (from the
previous-step inequality `3^k < c + 2k` and `2^463`).  The tail is stated
precisely as `TailBounded B`, and the numerical corollary
`length_le_17000_of_tail_16708` proves

```
TailBounded 16708 -> k + length w <= 17000.
```

Both files compile; all Rocq `Print Assumptions` are closed.  `TailBounded
16708` is not proved.  The obstruction is structural: after the first `j` run
the map can alternate short `c`/`b` corrections with short `j` runs, and no
monotone potential on `(a,c)` has yet been found that limits the number of
alternations.  The empirical tail at 463 bits is at most about 28 steps, but
that measurement is not a proof.

### Reachable halving-time maximum (2026-11-17)

The unrestricted constant halving lemma is **false**.  For arbitrary `(a,c)`
with `c = 2`, the halving time is `Theta(log a)`: the minimal counterexample to
`10,000` steps is the `c = 2` threshold with `a` of 1763 digits, and the
asymptotic is `log_{3/2}(a/(4c)) + O(1)`.  No formal files were added for that
unrestricted statement.

Restricting to states reachable from `A(1,c0)` with `c0 < 2^463` changes the
answer completely.  The exact 512-bit scanner `halving_scan.c` sweeps every
state of a chain (not just endpoints).  Its maximum so far is

```
T = 844,
reached at  (a,c) = (2*3^289 - 1, 2047),
from        c0 = 3^289 - 2*289 + 2046  (459 bits),
at          chain index 289.
```

Direct trace from that state: 380 `c` steps, 443 `b` steps, 20 `j` steps,
then `h`; no halt, return, or `c`-halving occurs earlier.  The next best
families are the even-start `K = 288` endpoint (`842`, `c = 3075`) and the odd
`K = 288` endpoint (`830`, `c = 75723`).

Sweep coverage: initial `j`-run endpoints `a = 2*3^K - 1` (odd starts) and
`a = 4*3^K - 1` (even starts), with `c` up to `2,000,000` for `K = 280..292`,
up to `1,000,000` for `K = 260..279`, and up to `5,000` for `K < 260`; all
states of the extremal chains, plus random 463-bit chains.  No state exceeded
`844`.  This is a computational maximum, not yet a kernel-checked universal
tail theorem.

**Formal certificate (2026-11-17).**  The extremal trace itself is now
kernel-checked in both assistants:

```
lean:  cryptids_a6/BusyBeaver/BB33/M_758_Halving844.lean
       prefix_reaches        : run 289 (1, 3^289 + 1468) = some (aStar, 2047)
       halving_time_844      : ht 2047 2000 aStar 2047 = 844
       #print axioms         : both "does not depend on any axioms"

rocq:  rocq/BB33_758_Halving844.v
       prefix_reaches        : run 289 (1, 3^289 + 1468) = Some (aStar, 2047)
       halving_time_844      : ht 2047 2000 aStar 2047 = 844%N
       Print Assumptions     : both "Closed under the global context"
```

Both compile with exit 0.  `aStar = 2*3^289 - 1`.  This establishes that
`844` is *attained* on the chain from `A(1, 3^289 + 1468)`, not that it is the
maximum over all reachable states.  The universal upper bound (and therefore
`K = 10,000`) remains unproved.

**Reduction of the universal target (2026-11-17).**  Every segment starts at
`A(1,c)`.  Its initial pure `j` run has

```
k <= 292,   (a,c) = (2*3^k - 1, c0 - 3^k + 1 + 2k),
```

and the post-run parameter satisfies `c < 2*3^k`.  Every later state of the
segment has remaining halving time no larger than the post-run state, so a
uniform bound on the family

```
Fam(k,c) = A(2*3^k - 1, c),   0 <= k <= 292,   1 <= c < 2*3^k
```

is sufficient.  This is the exact universal target; it is still infinite in
`c`.

In `T(t,d)` coordinates (`t=a+2c`, `d=(c-1)/2`, `u=(t-1)/2`) the safe rules
are the expanding maps

```
J: (u,d) -> (u+2, 3d-u+1)                 (right region)
L: (u,d) -> (u+{5,7,9}, (9d+{20,26,29,35})/4)  (left region)
```

The middle interval is the return/halt region.  In the ratio variable
`z=(u-2d)/d`, these are approximately

```
J: z -> 6z/(2-z)          (z <= 2)
L: z -> (z-5)/(9/4)       (z >= 5/2)
```

with the terminal window `2 < z < 5/2`.  The first `L` phase from the extremal
post-`j` state has length 382; after it the ratio is moderate and the remaining
phases are short.  A proof of `T <= 10,000` therefore needs a uniform bound on
the number of alternations of this expanding map, not merely the one-phase
logarithmic estimate.  No monotone scalar potential on `(u,d)` has been found;
the candidate interval-expansion (cookie-cutter) proof remains open.

**Decision:** `844 < 10,000`, so the constant `K = 10,000` is retained as the
**direct-bound target** on the reachable set.  The logarithmic form is no longer
the target for reachable states; it remains only the correct statement for the
unrestricted state space.  The direct bound gives `L <= 10000*log_2 c` and
`D <= 9L + 1.5 < 42M` at 463 bits, inside the verified wall.  The remaining
formal obligation is the reachable-tail theorem that no state after the initial
`j` run exceeds the endpoint behavior measured here.

## 15. Formal post-`j` reduction and L-phase estimate (2026-11-17, compiled)

New paired formal modules:

```
lean: cryptids_a6/BusyBeaver/BB33/M_758_PostJ.lean
      j_formula              : jIterI n (1,c) =
                               (2*3^n-1, c-3^n+1+2n)
      post_j_family          : projections of the same formula
rocq: rocq/BB33_758_PostJ.v
      j_formula              : the same identity over Z
      Print Assumptions      : Closed under the global context

lean: cryptids_a6/BusyBeaver/BB33/M_758_LPhase.lean
      Lstep_ge_two           : 2*d <= Lstep d, Lstep d = (9d+20)/4
      LIter_ge               : 2^n*d <= LIter n d
      L_phase_length_le_465  : (1<=d) -> LIter n d <= 2^465 -> n <= 465
rocq: rocq/BB33_758_LPhase.v
      the same three theorems
      Print Assumptions      : Closed under the global context
```

All four compile with exit 0; there is no `sorry`, `Admitted`, custom axiom or
`Parameter`.  Lean's `#print axioms` reports only the standard core axioms
`propext` and `Quot.sound` on the integer/L-phase files (they enter through
core `Int`/`Nat` arithmetic lemmas), not `sorryAx` or any project axiom.

The L-phase estimate is the first-phase logarithmic bound.  It does **not**
prove the uniform alternation bound: the number of L/J phases, and therefore
`T <= 10,000`, remains open.  No maximality or halting claim is made here.

## 16. Alternation accounting: measured structure, one refuted shortcut, dead weight cut (2026-11-18)

### The extremal run is one `L` phase plus a short tail

Exact phase table for the maximum, `k = 289`, `c0 = 2052` (also `2047`), `T = 844`
(823 `L` steps, 21 `J` steps, 26 phases):

```
phase 0 (L, 764 steps):  c  2052 -> 7.03e140      a  1.55e141 -> 1.39e140
phases 1..25       :  J2, L4, J3, L10, J1, L6, ... total 80 steps
```

So the first `L` phase is 764 of the 844 steps, and *everything after it is 80
steps*.  `T = 844` is not "many moderate phases"; it is "one maximal `L` phase
(764 <= 791, i.e. `phase_le_791` is nearly tight) plus a short tail".  The
residual that remains after `phase_le_791` is therefore a **tail** obligation of
at most `10000 - 791 = 9209` steps, measured at 80 on the extremal.

### A tempting shortcut, and why it fails

Half-gain accounting would say `2*T*log(3/2) <= log(c_max/c_min) +
log(a_max/a_min)` (each `L` step grows `c` by `3/2`, each `J` step grows `a` by
`3`, and the two ranges are `O(3^k)`).  On the extremal this reads

```
2 * 844 * log(1.5) = 684.3   vs   log c-range + log a-range = 636.3   (fails by 48)
```

The gap is the additive constants of the rules: `c' = 3c/2 + {2,5,8}` and
`a' = 3a + {0,2}`, which contribute `sum log(1 + O(1/c_i))` — negligible unless
`c` is small, and they break the clean ratio identity.  Any formal proof needs
those per-step corrections, not just the two range logarithms.

### What does hold exactly (candidate bricks for the next session)

* per `L` step `2*c' >= 3*c`, so `N*log(3/2) <= sum over L phases of log(c_out/c_in)`
  (measured on the extremal: 333.7 <= 357.5, slack 24);
* per `J` step `a' >= 3*a`, so `M*log 3 <= sum over J phases of log(a_out/a_in)`;
* the ratio `rho = c/a` **decreases at every `J` step** (`c'/a' <= c/a` is
  equivalent to `0 <= 2ac + 2c + a^2 - a`) and **increases at every `L` step**
  (equivalent to `0 <= ac/2 + c^2 + alpha*c + beta*a`).  So `rho` is monotone
  inside each phase and oscillates across phases.

The obstruction is unchanged: `sum over L phases of log(c_out/c_in)` has no
a-priori bound without pairing each `L` phase's growth against the following `J`
phase's `c`-drop, and that pairing is where the additive constants and the
parity-driven `h` termination have to be handled.

### Dead weight cut

The six `J`-phase lemmas added in the previous session (`step_even_J`,
`step_odd_J`, `J_step`, `hrun_one`, `three_pow_dominates_9`, `phase_le_293`)
had no consumer: `phase_le_293` cannot bound a *tail* (the tail's first phase may
be `L`, and its `J` phases are entered from states far outside the family
hypotheses `c < 2*3^k`).  They were removed from **both** files
(`M_758_TBudget.lean`, `BB33_758_TBudget.v`) together with their
`#print axioms` / `Print Assumptions` lines, rather than left as dead weight.
Their content, if a future alternation proof needs it:
`phase_le_293 : k <= 292 -> 1 <= c -> c < 2*3^k -> survival from (2*3^k-1,c)
-> (a <= c on the orbit) -> (a odd on the orbit) -> n <= 293`.

Both files compile with exit 0 after the cut; Lean has no `sorryAx`, Rocq's
`Print Assumptions` are all `Closed under the global context`.

**Still open:** `ResidualHalving`, hence `T <= 10000`.  No halting/non-halting
conclusion; no required phrase applies.

## 17. Tail measurement and the coarse cycle bound that would close `T <= 10000` (2026-11-18)

### Measurement (`bbwork/_tail.py`, `_tail2.py`, `_tailtrace.py`; exact `step`/`ht`)

141,618 family members `F(k,c) = A(2*3^k-1, c)`, `1 <= k`, `1 <= c < 2*3^k`
(exhaustive `c` for `k <= 9`, `c < 4000` plus 400 scaled points for `10 <= k <= 24`,
`c < 300` plus 2047/2052/3075/75723/`top-1`/`top/j` and 30 uniform random `c`
for `k = 25..292`):

```
max T                = 844   (k=289, c=2047 and c=2052)
max first L phase p0 = 764   (same instances; 785 over all samples)
max tail   T - p0    = 80    (same instance; k=288,c=75723 gives 78)
max number of phases = 28
```

So `T = p0 + tail` with `p0 <= 791` **proved** (`phase_le_791`) and a tail
measured at `80`.  The target leaves `10000 - 791 = 9209` for the tail, i.e. the
remaining obligation needs a *coarse* bound, ~100x the measured tail.

### Tail mechanism (step trace, `k=289, c=2052`)

After the first `L` phase the state has `a <= c`.  The tail is a strict
alternation of `J` phases (rule `j`, `a` triples, `c` drops by `a`) and `L`
phases (rule `b`/`c`, `c` multiplies by `3/2`, `a` drops by `c`):

```
 1 J j  a/c=5.06  a*3   c*0.802
 2 J j  a/c=1.35  a*3   c*0.261
 3..6 L b,b,c,c   c*1.5 each step
 7..9 J j,j,j     a*3    c*0.924, 0.753, 0.018
10..19 L (ten steps)      c*1.5 each
20 J j                    c*0.098
...
```

One full cycle multiplies `c` by about `2/9` (measured 0.1 - 0.7).  Hence the
number of cycles is at most `log(c_tail / (c0/2)) / log(4.5)`, with
`c_tail <= 3*3^k`:

```
#cycles <= (k*log3 + log6) / log 4.5  <=  (292*1.0986 + 1.79)/1.504  <= 215
```

and a typical cycle costs 3-4 steps (measured mean 80/25 = 3.2).  Even the
pathological cycle (`a` tiny at a cycle start, so the `J` phase runs its full
`log_3 c <= 294` steps before `a > c`) is followed by cheap cycles, since it
leaves `a` comparable to `c`.  So a bound of the shape

```
tail <= 294 + 4 * 215 = 1154        (even 8*215 = 1720 would do)
```

closes `T <= 791 + 1720 = 2511 <= 10000` with a wide margin.

### The four lemmas that are still missing (all coarse, none tight)

1. **cycle start invariant**: at the start of each `J` phase in the tail,
   `a >= c/16` **or** the phase is the "long" one (`a <= c/16`, then the `J`
   phase ends with `a` comparable to `c`).  Measured `a/c` at `J` starts:
   1.0 - 13.2.
2. **per-cycle contraction**: `c` after a full cycle `<= (2/3) c` before it
   (measured 2/9; `2/3` leaves room for the additive constants).
3. **cycle count**: `#cycles <= 215` from (2) and `c_tail <= 3*3^k`
   (the `L`-invariant `3a + 2c <= 3a0 + 2c0 + 4T` is *not* usable directly
   because it mentions `T`; use instead `c <= 3*3^k` inside the first phase,
   then (2) greedily).
4. **per-cycle length**: `<= 8` steps in the normal case, and the "long" case
   costs `<= 294` once.

Each of 1-4 is a small arithmetic lemma about `step`; the earlier bricks
`L_step` (`a + c <= a'`... i.e. `a' + c <= a` and `3c <= 2c'`) and `J_step`
(`3a <= a'`, `c - a + 1 <= c'`) are exactly the per-step inputs they need.
This is the concrete next-session target; it is **not** the sharp `844`
argument, and it needs no cookie-cutter/Markov-partition machinery.

**Status: `ResidualHalving` and `T <= 10000` are still unproved.**  Both
`M_758_TBudget.lean` and `rocq/BB33_758_TBudget.v` remain at their post-cut
state: Lean exit 0, no `sorryAx`; Rocq exit 0, 45 `Print Assumptions`, all
`Closed under the global context`.  No halting/non-halting conclusion.

## 18. The per-cycle `c`-contraction is **false** (kernel-checked in both files)

### The statement that was to be proved

Let a *cycle* be one maximal `J` phase (rules `i`,`j`: `a` triples, `c` drops by `a`)
followed by one maximal `L` phase (rules `a`,`b`,`c`,`e`: `c` multiplies by `3/2`, `a`
drops by `c`).  Write `(a,c)` at the cycle start (there `a <= c`) and `c_end` at the
cycle end (there `a <= c` again).  The intended lemma, with the additive-constant
corrections of the rules, was

```
4*c_end <= 3*c_start + K          (K a small constant)
```

i.e. `c` falls by at least a factor `3/4` per cycle up to an additive slack.

### Refutation

```
(549,1196)  --i-->  (1647,651)  --c-->  (992,983)  --c-->  (5,1481)      a <= c at start and end
```

`c` **grows** from `1196` to `1481` (x1.238), so `4*c_end - 3*c_start = 5924 - 3588 = 2336`.
The `L` phase ends exactly where it must (`a = 5 <= 1481 = c`), so this is a genuine
`J`+`L` cycle of the same map the halving run uses.  Hence no inequality of the form
`4*c_end <= 3*c_start + K` holds for `K < 2336`, and — worse for the intended use — any
such inequality with *any* constant `K` has the fixed point `c ~ 4K/1`, so it cannot
bound the number of cycles on its own: cycles are stable at scale `c ~ K`.

Kernel-checked in both files (this session):

```
lean  M_758_TBudget.lean : cycle_contraction_false        (the 3-step chain)
                           cycle_contraction_false_arith  (3*1196 + 2000 < 4*1481)
                           #print axioms: "does not depend on any axioms"
rocq  BB33_758_TBudget.v : cycle_contraction_false, cycle_contraction_false_arith
                           Print Assumptions: Closed under the global context
```

Measured over 115,138 `(a,c)` pairs with `a <= c` the largest cycle growth of `c` was
x1.24 (the witness above); the *aggregate* behaviour is still downward (tail <= 80,
section 17), so a correct global argument exists — but it cannot be a per-cycle
monotone potential.  This is the same obstruction as section 14, now localised and
proved rather than conjectured.

### What exactly still blocks `T <= 10000`

1. **Window bound (missing).** Because per-cycle contraction fails, the only viable
   large-`c` argument is: *for every scale `tau`, at most `K` cycles have `c` in the
   window `[tau, 2*tau]`* — the cookie-cutter/alternation statement of section 14,
   expressed in `z = c/a` (the `L` map `z -> (4/9)(z-5)` contracts, the `J` map
   `z -> 6z/(2-z)` expands; a window bound is a statement about the composition of
   many cycles).  No such bound is proved, and it is not implied by any per-cycle
   potential, as the refutation above shows.
2. **Small-`c` regime (closable, not closed).** Once `c <= tau0` and `a <= c`, the
   state space is `tau0*(tau0+1)/2`, so the deterministic run visits at most that many
   states before stopping.  With `tau0 = 100` this is 5050 steps — inside the 9209
   slack — but it is only usable *after* (1) bounds the large-`c` part.
3. Termination itself can come from rule `h` (`a` even, `c` odd gives `a' = 1`), which
   is why `c` need not actually reach `c0/2`; any accounting must cover both exits
   (halving test and `a = 1`).

**Status: `ResidualHalving` and `T <= 10000` are not proved.**  Lean exit 0 (no
`sorryAx`, the two new theorems axiom-free); Rocq exit 0 with **47** `Print
Assumptions`, all `Closed under the global context`.

## 19. Why the window bound has no uniform `K` (measured), and what that does to the two-part plan (2026-11-18)

### The claim that was to be proved

*For every `tau` and every `K`-uniform constant, at most `K` cycles have `c` in
`[tau, 2*tau]`.*  Combined with the small-`c` pigeonhole bound (`a <= c <= 100` gives
5050 states) this was to close `T <= 10000`.

A uniform `K` needs a scale-independent gap: every cycle ratio `r = c_end/c_start` must
satisfy `|r - 1| >= delta` (or `r <= 1 - delta`) for all `c >= tau0`.  Otherwise `c` can
linger in a factor-2 window for `log 2 / log(1+eps)` cycles, which is unbounded as
`eps -> 0`.

### Measurement: the gap vanishes with scale (so no uniform `K` from this route)

Scanning `a/c` over 400 ratios at several scales (`_win.py`, exact `step`):

```
|r-1| = 1.6e-04   at c = 5.15e53    (a = 4.14e53, m=1, n=4,  c_end = 5.15297e53)
|r-1| = 1.0e-03   at c = 1002
r     = 1.00125   at c = 5.15e53    and at c = 1.91e140
```

So (i) cycle ratios arbitrarily close to 1 occur at every large scale, and (ii) at
`c ~ 1.9e140` a cycle can *increase* `c` by 0.1%.  A factor-2 window at `c = 5e53` is
crossable in ~555 such cycles; nothing in the coarse inequalities rules that out.  The
window bound with a uniform `K` is therefore **not derivable from a ratio gap**, and its
truth would need a genuine dynamical (cookie-cutter) argument — the same obstruction as
sections 14 and 18, now in the window form.

Empirically, on the family the longest stretch with `c` inside a factor 2 of its value at
the start of the stretch is 80 steps (the extremal run itself, `k=289, c=2047`), so a
small `K` *is* consistent with all tested runs — but that is measurement, not proof.

### Why the two-part plan does not compose anyway

Even granting a window bound with `K` cycles per window, the plan needs
`K_cycles_total * steps_per_cycle + 5050 <= 9209`.  With `|r-1|` as small as `1.6e-4`
the number of cycles a run could spend in one window is ~555, and with ~460 windows
(`log_2(3^292)`) the product is far above 9209.  A useful bound needs `K <= ~4` per
window, i.e. a *uniform* gap of at least ~0.2 in `|r-1|`, which the measurement above
refutes at every large scale.

The small-`c` pigeonhole half is also weaker than it looks: a run that stays inside
`a <= c <= B` and repeats a state *never stops* (the halving test is a function of the
state and the fixed `c0`), so pigeonhole gives "`T <= B(B+1)/2` **or** the run loops
forever".  Excluding loops in the box is a finite check over ~5000 states that has not
been formalised, and without it the brick cannot be composed with the rest.

**Conclusion of this session:** the window route is blocked by the absence of a uniform
ratio gap (measured, arbitrarily small at large scale), not by a missing estimate.  The
two-part plan (window bound + pigeonhole) therefore does not close `T <= 10000`.
`ResidualHalving` and `T <= 10000` remain unproved; the formal files are unchanged from
their verified state (Lean exit 0, no `sorryAx`; Rocq exit 0, 47 `Print Assumptions`,
all `Closed under the global context`).

## 20. A different coordinate system, and what it buys (2026-11-18)

### The change of variables

Put `u = (a + 2c - 1)/2`, `d = (c - 1)/2` (so `t = a + 2c = 2u+1`, `c = 2d+1`).  Then

```
a <= c        <=>   u <= 3d + 1        (J region)
a = 1         <=>   u = 2d + 1         (rule h terminal line)
2c' <= c0     <=>   d' <= (c0-2)/4     (halving test)
a > 2c        <=>   u > 4d + 1         ("deep L" cone: c is small against a)
```

and the two maps are **affine**, one coordinate linear and one geometric:

```
J:  (u,d) -> (u + 2,      3d - u + 1)
L:  (u,d) -> (u + {5,7,9}, (9d + {20,26,29,35})/4)
```

So the whole halving run is an affine iteration in the plane whose region conditions are
*linear inequalities*, with `u` increasing by at least 2 every step.  This is not a new
potential (those are refuted); it is a normal form: the run is "how long can an affine
orbit stay inside a wedge", and the wedge's width grows with `d`, i.e. with `c`.

### Measured consequence (family sweep, exact `step`)

Splitting each run at the deep cone `u > 4d+1` (`a > 2c`):

```
max length of a phase with a <= 2c   :  7 steps   (k=288, c=323, a J phase)
max length of a phase with a >  2c   : 784 steps  (k=292, c=1, the first L phase)
max number of phases in a run        : 37
max number of deep-cone phases       : 14
```

So **outside the deep cone every phase is at most 7 steps**, and the only long phases are
the deep-cone ones, of which the first is already bounded by `phase_le_791`.  This is the
structural reason the extremal run is `764 + 80`: the expensive part is a deep-cone `L`
phase, and everything afterwards lives in the shallow cone where phases are constant-length.

### What this does and does not fix

It fixes the *per-phase length* problem (constant case analysis instead of unbounded
phases), but **not** the counting problem: within the shallow cone the per-cycle `c`
multiplier can still be arbitrarily close to 1 (section 19), so a wedge-argument must count
cycles, not just bound each one.  Untried tools for that counting:

1. **Quadratic / piecewise Lyapunov functions.**  Section 18 killed *additive per-cycle*
   inequalities `4c' <= 3c + K`; it says nothing about a quadratic form
   `Phi = a^2 + lam*a*c + mu*c^2` or a *pair* of forms switched by region (control-theory
   Lyapunov with switching).  An ellipsoid norm contracted by both matrices on the wedge
   would bound the cycle count geometrically.
2. **Joint spectral radius of `{L,J}` on the wedge.**  The reduction length is the
   "cone-hitting time" of a matrix semigroup; a JSR argument (invariant ellipsoid) is the
   standard tool and has not been attempted.
3. **Rotation / three-distance structure.**  In `(u,d)` the crossing `u = 3d+1` is a linear
   inequality with `u` moving by +2 per step, so crossing times are Beatty/Sturmian-like.
   If the induced map on the ratio is conjugate to a rotation, the three-gap theorem gives
   explicit return-time bounds in terms of the continued fraction of the rotation number —
   a mechanism entirely different from a potential, and testable numerically in one probe.

**Status unchanged formally:** `ResidualHalving` and `T <= 10000` are not proved.  Both
files remain at their verified state (Lean exit 0, no `sorryAx`; Rocq exit 0, 47 `Print
Assumptions`, all `Closed under the global context`).

## 21. Quadratic Lyapunov search on the shallow cone: no such form exists (measured minimax) (2026-11-18)

### What was searched

`Phi(a,c) = a^2 + beta*a*c + gamma*c^2`, required positive on the shallow cone
(`x = a/c in [0,2]`: `gamma > 0` and, when `beta < 0`, `gamma > beta^2/4`), and required to
satisfy `Phi(cycle end) <= lambda * Phi(cycle start)` on every shallow-cone cycle
(one maximal `J` phase then one maximal `L` phase, `a <= 2c` at the cycle start).

Grid minimax (`_lyap3.py`, 1995 shallow-cone cycles from the family, `beta` over
`[-3,1]` in 200 steps, `gamma` over a 130-point log grid, cone positivity enforced):

```
min over (beta,gamma) of  max over cycles of  Phi(end)/Phi(start)  =  2.097   at (beta,gamma) = (0.88, 4.07)
```

So the *best possible* worst-case growth of any form in this family is about **2.1 > 1**:
no positive quadratic form contracts on the shallow cone.  (Single-form families in
`(u,d)` and log-linear forms `a^p c^q` behave the same way: the `a`-growth and `c`-growth
cycles pull the two weights in opposite directions.)

### The two witnesses that make the obstruction visible

```
W1:  (9,2291) -j-> (29,2283) -j-> (89,2255) -j-> (269,2167) -j-> (809,1899)
             -j-> (2429,1091) -c-> (1334,1643)      a x148 , c x0.717     (then rule h)
W2:  (23,29)  -j-> (71,7)     -c-> (60,17)    -b-> (41,29)  -b-> (10,47)
                                                    a x0.43, c x1.62
```

Both start in the shallow cone (`a <= 2c`).  W1 needs a form dominated by `c^2` (so the
`a` explosion is discounted), W2 needs a form dominated by `a^2` (so the `c` growth is
discounted).  Concretely, W1-contraction forces
`2549232*gamma >= 1779475 + 2171143*beta`, W2-contraction forces
`1368*gamma <= 429 + 197*beta`, and together these force `beta <= -0.5433` and pin
`(beta,gamma)` into a sliver near `(-0.5433, 0.2352)`; the *other* 1993 cycles then break
that sliver (the grid minimax above).  So the two-witness argument alone is not enough, but
the full cycle set leaves no admissible form.

### Consequence for the plan of section 20

Route (1) — a single quadratic Lyapunov function on the shallow cone — is **dead**, as is
the log-linear family.  What survives is only the *region-switched* (multiple-Lyapunov)
variant, and it must use genuinely different forms in the `J` and `L` cones with
cross-contraction at the switches; the two witnesses above show why one form cannot serve
both, i.e. the switching structure is essential and is exactly where the alternation
content sits.

No formal changes: the object being sought does not exist, so there is nothing to prove
about it in Lean or Rocq.  Files remain at their verified state (Lean exit 0, no
`sorryAx`; Rocq exit 0, 47 `Print Assumptions`, all `Closed under the global context`).
`ResidualHalving` and `T <= 10000` remain unproved.

## 22. The shallow-cone phase brick: sharpened, and the literal form refuted (2026-11-18)

### The brick as stated is false

"In the shallow cone `a <= 2c` every phase has at most 7 steps" is **false**, and the
reason is structural rather than a matter of the case analysis being wide: `(a,c) = (1,c)`
is shallow for every `c`, and the `J` phase from `(1, 3^n)` has `n` steps, because each
rule `j` triples `a` while `c` barely moves.  The smallest concrete witness is

```
(1,6561) -j-> (5,6561) -j-> (17,6557) -j-> (53,6541) -j-> (161,6489) -j-> (485,6329)
         -j-> (1457,5845) -j-> (4373,4389) -j-> (13121,17)      (8 steps, then the L region)
```

so `(1,6561)` — shallow, since `1 <= 2*6561` — has an **8-step** `J` phase.  The measured
"max 7" over the family (`_ph.py`: 141k runs, max `J` phase = 6, max `L` phase = 785) is
therefore an artefact of *reachability*, not of the cone.

### What is true, and now proved in both files

* `L_shallow_step` — in the shallow cone `c < a <= 2c`, a non-halting `L` step ends the
  phase (`a' <= c'`) **unless** it is rule `e` (`a = c+2`), which sends `(c+2, c)` to
  `(3c+8, 1)`, i.e. into the deep cone.
* `jrun_odd_step` — in the `J` region with `a` odd, every step is `i` or `j`; `a` stays
  odd, at least triples, and `c` rises by at most `3`.  (Rule `h` can fire at most once per
  `J` phase, at its first step, because `h` needs `a` even and `i`,`j` preserve oddness.)
* `jrun_odd` — a `J` phase of length `n+1` from an odd `a` satisfies `3^n * a <= c + 3n`.
* (proved, then **removed**) `jrun_eight` — a `J` phase of length `8` forces `c >= 355`;
  `J_phase_le_seven` — in the `J` region with `c < 355` every phase has length at most `7`;
  and `shallow_phase_eight` — the eight-step chain above.  These three, plus the Rocq
  helpers `eight_arith_h` / `eight_arith_o` that existed only for them, were cut from
  section 8d in both files: the hypothesis `c < 355` is not available, and even granted it
  buys nothing toward `T <= 10000` (next subsection).  The counterexample survives here,
  kernel-checked in the git history of this session's files, and in `_ph.py`'s measurement.

### Which case blocks the literal brick

Exactly one: a `J` phase that starts with rule `h` (`a` even, `c` odd).  Then `a` becomes
`1` while `c` becomes `a/2 + c + 2`, so the phase length is `1 + log_3(c)` and nothing in
the shallow cone bounds `c`.  All other cases are closed by the lemmas above (odd `a`:
`3^n a <= c + 3n`; shallow `L`: length 1 unless rule `e`).  The missing hypothesis is
`c < 355` (or any reachability invariant bounding `c` at phase starts); with it the brick
is true, without it the counterexample stands.

### Does the brick feed `T <= 10000`?  No

Two independent reasons, each fatal on its own.

**1. It needs a reachability invariant on `c`, and it does not apply to the real orbit.**
The sharpened form is `J_phase_le_seven : JRun 8 a c -> c < 355 -> False`.  Nothing in the
shallow cone bounds `c` — `(1,6561)` is the counterexample — so the hypothesis can only come
from reachability.  Worse than unproved: it is *false almost everywhere on the orbit*.  Over
the same 141k family runs, of **12252 `J`-phase starts only 571 have `c < 355`** (`_cj.py`);
95% have `c >= 355`, `c` reaches 2280 inside the small-`c` sample (`(298,2129) -h-> (1,2280)`
at `k=7, c0=7`), and at `k=292` the `J`-phase start is `O(c0) ~ 6e76`.  So the lemma cannot
be applied to the phase starts the run actually produces: any reachability invariant on `c`
at phase starts is `c`-large, which contradicts `c < 355` instead of supplying it.  What a
usable phase-length bound would need is a bound in terms of `c` (the `1 + log_3 c` of the
blocking `h` case), not a constant cone condition.

**2. Even granted, it does not bear on the target.**  `ResidualHalving` bounds
`m + t <= 10000` for a residual run, so it needs (a) a bound on the *number* of phases and
(b) a bound on each phase's length.  The brick is type (b) for one region only, and weakly
so: the measured `L` phase reaches 785 steps, and the rule counts over 141k runs are
`a:6533, b:748511, c:710456, j:8113, h:6580` — the length lives in rules `b` and `c`, so
capping `J` phases at 7 moves the total by at most a few thousand steps while no phase count
exists to multiply anything by.  A per-phase number with no phase count gives no `m + t`
bound.

So the brick is dead weight for the halving bound, not a step toward it.  Section 8d keeps
only the unconditional lemmas — `L_shallow_step`, `jrun_odd_step`, `jrun_odd` and their
arithmetic support — which are exactly the handles on the missing invariant on `c`
(`jrun_odd` gives `3^n * a <= c + 3n`; `L_shallow_step` sends a shallow `L` step either out
of the region or to `c' = 1`).  Work returns to `ResidualHalving`.

### Status

`ResidualHalving` and `T <= 10000` remain unproved: this section is a *phase-shape* brick,
not a counting or halving bound, and it gives no information about the number of phases.
After the cut, Lean compiles exit 0 with `#print axioms` clean on the kept lemmas (no
`sorryAx`); Rocq compiles exit 0 with every `Print Assumptions` closed (see `AGENTS.md`).

## 23. Phase counting: the true bound, and why a count cannot close `ResidualHalving` (2026-11-18)

### What is true

`flips n a c` (both files) counts region changes along the next `n` steps: a *phase boundary*
is a step whose result lies in the other region (`J`: `a <= c`, `L`: `c < a`).  The lemmas
`flips_le : flips n a c <= n` and `phases_le : flips n a c + 1 <= n + 1` are kernel-checked.
This is the only unconditional phase-count bound there is, and it is sharp: one-step phases
occur (the `k = 289` trace below is full of them), so a count can never replace a length bound.

### Why it is not a route

`ResidualHalving` must fit the residual in `10000 - 791 = 9209` steps.  The proved per-phase
budgets are `878` for a post-`j` `L` phase (`L_phase_le_878`) and `293` for a `j` phase
(`J_phase_le_293`), so a residual with `NL` `L` phases and `NJ` `j` phases carries only the
budget `878*NL + 293*NJ`.

Measured worst residual (`_pc.py`, same 141k family runs; run `k = 289, c0 = 2047`, halving
time 844): 26 phases, **18 of them after step 791** -- 9 `L` and 9 `J`, totalling `39 + 14 = 53`
steps.  Hence `878*9 + 293*9 = 10539 > 9209`: even exact knowledge of the counts does not fit
(`counting_budget_le`).  In the other direction, nine `L` phases leave room for at most four
`j` phases (`counting_budget_forces`), so a usable count bound would have to look like `(9,4)`,
while the measured residual is `(9,9)`.

The slack is not in the count: it is in the per-phase budgets, which are about 100x the actual
phase lengths (`878` versus at most 10 here; `293` versus at most 3).  Tightening them is the
phase-length brick of section 22, which is false unconditionally.

### Exact blocker

To close by counting one would need a proved composition `t <= 878*NL + 293*NJ` together with
counts satisfying `878*NL + 293*NJ <= 9209`, i.e. roughly `NL <= 10` and `NJ <= 4` for the
`L`-phase count that occurs.  The counts that actually occur violate this at `(9,9)`, so **no
bound on the number of phases can close `ResidualHalving` while the per-phase budgets stay at
878/293**.  What is missing is a per-phase bound in terms of the phase's own `c` (the closed
budget of `L_phase_le_878` applied with `2*3^292` replaced by the current value), which is a
halving-time statement about `c`, not a count.

### Status

`ResidualHalving` and `T <= 10000` remain unproved.  New in both files: `flips`, `flips_le`,
`phases_le`, `counting_budget_le`, `counting_budget_forces`.  Lean exit 0, `#print axioms`
clean (no `sorryAx`); Rocq exit 0, `Print Assumptions` closed.  Probes: `_ph.py`, `_cj.py`,
`_pc.py`, `_pt.py` (measurement only, not proofs).  No halting/non-halting conclusion; no
required phrase applies.

## 24. The phase-composition lemma, and the phase that breaks it (2026-11-18)

### What is now proved

Section 23 left the composition open: it compared `t` with `878*NL + 293*NJ` but never derived
one from the other.  Both files now carry it.

* `phase_composition` (Lean and Rocq): for a sequence of `N` phases with lengths `len i` and
tags `tag i` (`1` = `L`, `0` = `j`), if every `L` phase is `<= 878` and every `j` phase
`<= 293`, then `ssum len N <= 878 * sL tag N + 293 * sJ tag N`, i.e. `t <= 878*NL + 293*NJ`.
This is a genuine induction on the phase sequence (both counts are sums over the same index),
not a restatement.
* `residual_counting_forces`: if the *charge* fits, `878*NL + 293*NJ <= 9209`, and `NL >= 9`,
then `t <= 9209` and `NJ <= 4`.  At the measured residual `(NL, NJ) = (9,9)` the charge is
`10539`, so the hypothesis fails -- the route is dead for the stated reason, now as a theorem.
* `L_phase_le_878_gen`: the `L` charge at an *arbitrary* phase start (`a0 <= 2*3^292`,
`1 <= c0`, closed budget), with `L_phase_le_878` as its corollary.  `J_phase_le_293` was
already general in `a0`; its hypotheses are `1 <= a0` and `a0 + 2*c0 <= 6*3^292`.

### Carrying the post-`j` hypothesis through: it reaches exactly one phase

`postJ_charge` discharges all three caps from `k <= 292`, `1 <= c`, `c < 2*3^k` alone:
`1 <= 2*3^k - 1`, `2*3^k - 1 <= 2*3^292`, `(2*3^k - 1) + 2*c <= 6*3^292`.  So the phase that
starts at the post-`j` state is charged with no further input, for either tag.

It reaches no further.  `postJ_charge_extremal` records that the extremal post-`j` state
`(2*3^292 - 1, 2*3^292 - 1)` is exactly chargeable (`Q_0 = 6*3^292 - 3`), and
`phase_two_breaks` records that one rule-`j` step gives `(2*3^293 - 1, 1)`, where
`2*3^292 < 2*3^293 - 1` and `6*3^292 < (2*3^293 - 1) + 2`.  **Both** caps fail at that second
phase start.  The mechanism is structural, not accidental: `Q` rises by at least `3` per step
(`hrun_Q`) and a rule-`j` step triples `a + 1`, while both charges are fixed-constant
statements about the post-`j` family.

### Answer to "which phase breaks it"

The **second** one -- the first phase whose start is not the post-`j` state.  `ResidualHalving`
starts `791` steps in, so the composition cannot be discharged on the residual at all: it
charges at most one phase.  The inequality `t <= 878*NL + 293*NJ` is true on every measured run
(844 steps, `(9,9)`, charge `10539`); what is false is its derivability from the two proved
per-phase budgets plus the post-`j` hypothesis.  Closing the residual still needs the
`c`-dependent per-phase budget of section 23's "exact blocker".

### Status

`ResidualHalving`, hence `T <= 10000`, remains unproved; `halvingTimeBound_of_residual` is still
conditional.  New in both files: `ssum`, `sL`, `sJ` (+ `_succ` unfolding lemmas),
`phase_composition`, `residual_counting_forces`, `postJ_charge`, `postJ_charge_extremal`,
`phase_two_breaks`, `L_phase_le_878_gen` (with `L_phase_le_878` now its corollary).  Rocq also
carries the symbolic helpers `pow3_succ`, `pow3_293`, `two_mul_pred_odd` and
`phase_two_breaks_gen` (the crossing proved for an abstract `u >= 1`, instantiated at
`u = 3^292`): `vm_compute` on the 465-bit numeral exhausts memory and `lia` on it fails with
'Cannot find witness', so every step is symbolic.  Lean exit 0, `#print axioms` clean on all
of them (`propext`, `Quot.sound` only, no `sorryAx`); Rocq exit 0 with all 76
`Print Assumptions` closed.  No halting/non-halting conclusion; no required
phrase applies.

## 25. The phase list built from the run, and the per-start budgets

Section 24 proved the composition for an abstract phase sequence.  It is now built from the
run, in both files:

* `cutLen b i = b (i+1) - b i` is the length of phase `i` of a cut sequence `b`, and
  `ssum_cutLen` proves `ssum (cutLen b) N = b N - b 0`; with `b 0 = 0` and `b N = n` the
  phase lengths really do sum to the run length.
* `phaseTag c0 a c b i` is the region (`reg a c = 1` for `J`, `0` for `L`) of the state the
  run is in at index `b i` -- a real state, since `st` is the run on every surviving prefix
  (`st_hrun`).  The charges are therefore attached to actual phase starts.
* `hrun_phase_composition`: for a surviving halving run `hrun c0 n a c = some (a',c')` cut
  into `N` phases with per-phase charges, `n <= 878*NL + 293*NJ` and
  `st c0 n a c = (a',c')`.
* `hrun_phase_counting` is the residual-window consequence at run level (`n <= 9209` and
  `NJ <= 4` when the charge fits and `NL >= 9`).

`residual_counting_forces` was **cut** from both files: it was exactly `phase_composition`
and `counting_budget_forces` glued by `omega`, with no content of its own.  Its only role --
keeping `counting_budget_forces` consumed -- is taken over by `hrun_phase_counting`.

### Per-phase budgets in terms of each phase's own `a0, c0`

* `L_phase_len_c0`: an `L` phase of length `n` from `(a0,c0)` with `c0 >= 1` obeys
  `n * c0 <= a0 + 2*c0`, i.e. `n <= (a0 + 2*c0)/c0`.  `n * 2^n <= 2*3^n`
  (`n_mul_pow2_le`) turns the budget `2*c0*3^n <= 2^n*(a0+2*c0)` into the linear bound;
  then `2^n` cancels.
* `J_phase_len_own`: a `j` run of length `m >= 1` from `(a0,c0)` with `a0 >= 1` obeys
  `2*(m*a0) <= a0 + 2*c0 + 2*m`.  `1 + 2*m <= 3^m` (`three_pow_ge_lin`) is inserted into
  `J_phase_budget`'s `3^m*(a0+1) <= a0+2*c0+4*m`.

Unlike `878` and `293` these hold at **every** phase start, not only at the post-`j` family --
which is what section 24 identified as the composition's missing input.  They do not close
`ResidualHalving`, for a precise reason: both are *linear* in `Q0` (`n <= a0/c0 + 2`,
`m <= (a0+2*c0)/(2*a0)`), while the constant caps are *logarithmic* in it.  Summed over the
phases, `Sigma n_i*c_i <= Sigma Q_i` bounds the residual by about `N*Q_end/2`, far above
`9209`.  The sharp form is the product bound `(3/2)^{Sigma n_i} <= Pi (Q_i/(2*c_i))`, i.e. an
alternation bound on the number of phases in the residual, and that is still missing.

### Status

`ResidualHalving`, hence `T <= 10000`, remains unproved.  Lean exit 0, `#print axioms` clean
on all nine new lemmas (`propext`, `Quot.sound` only); Rocq exit 0 with all 85
`Print Assumptions` closed (76 - 1 cut + 10 new).  No halting/non-halting conclusion; no
required phrase applies.

## 26. What `T <= 10000` is, and why its content is parity, not size

`HalvingTimeBound` is `HalvingTimeLe 10000`:

    forall k c n, k <= 292 -> 1 <= c -> c < 2*3^k ->
      HSurvives c n (2*3^k - 1) c -> n <= 10000

i.e. from every post-`j` state `(2*3^k - 1, c)` the halving run stops -- on a true halt, on
`a' = 1`, or on `2*c' <= c` -- within `10000` accelerated steps.  `HSurvives c n` means the
halving time exceeds `n`, so this is the uniform halving-time bound, and it is the single
remaining obligation behind `halvingTimeBound_of_residual`.

### The statement is true with 12x slack

* `_ht_scan.py`, exhaustive over `k <= 8` and every `c < 2*3^k`: max halving time **41**.
* `_ht_scan.py`, sampled `k = 30 ... 292`: 81, 168, 268, 411, 556, 675, **790** -- growth
  about `2.75*k`, worst found `804` (`k = 292`, `c = 471656`); the certified `844` trace is
  the known record.  `10000` is not the obstacle.

### The decomposition: one long phase plus a short tail

Every extremal run has the same shape (`_ht_tail.py`, best case per `k`):

    T = (first phase) + (tail),   first phase <= 791 (proved: L_phase_le_791),  tail 5..36.

    k=100: 268 = 252 + 16      k=200: 556 = 534 + 22      k=292: 790 = 784 + 6

The first phase is `L` and its length is `log_{3/2}(a_0/c_0)`.  The tail is ~13 phases and
`<= 36` steps in every sample; over 1200 runs the exits are `a' = 1` (935), true halt (174),
`2c' <= c` (91), and never the step cap.

### Why the tail is not a size statement

In the tail `c` is already `1.5^t1 * c_0` (about `10^133` times `c_0` in the extremal case),
so `2c' <= c` is **dead**: the tail can only stop on `a' = 1` or on a halt, and both are
parity events:

* if `a <= c` and `a` is even the run stops at once: rule `g` halts when `c` is even, rule `h`
  gives `a' = 1` when `c` is odd.  So **every surviving `J` state has odd `a`**;
* in the `J` region with `a` odd, rules `i` and `j` keep **both** `a` and `c` odd
  (`3a+2`, `c-a+1`, `c-a+4` are odd);
* in the `L` region with `c` odd, rule `a` cannot fire (`c % 4 = 0,2` is excluded), rules `b`
  and `c` keep `c` odd and **flip the parity of `a`** (`a' = a - c - r`, `r` even), and rule
  `e` lands on the odd value `3c+8`.

So a surviving tail is an odd/odd walk in which every `L` step flips `a`'s parity, and the run
stops at the **first `L` phase whose closing `a` is even** (rule `h` fires on the next step),
or at a halt (`a = c+1`, `a = c+3`), or when `c` halves.  Tail length is therefore a
parity-coincidence time, not a size, which is exactly why the `Q`-budget, the per-phase
budgets and the counting route all stall; it is also why `HBudget 30000` is provably *harder*,
since `hbudget_of_length` needs `T <= 3333`.

### The routes, and the one that can work

1. `Q`-budget (`HBudget 30000`): needs `T <= 3333`.  Strictly harder.  Dead.
2. Per-phase budgets plus a phase count: at the measured tail counts (7 `L`, 6 `j` phases)
   the charge is `7*878 + 6*293 = 7904 <= 9209`, so a phase-count bound would close the
   residual -- but nothing proved bounds the count, and bounding it is route 3.
3. **The parity bound**: show that within `9209` steps every surviving tail reaches an
   even-`a` `L`-phase close or a halt.  The opening bricks are unconditional and cheap:
   `hrun_odd_of_le` (a surviving state with `a <= c` has odd `a`), `tail_odd` (both parities
   odd at every `J` state; `c` odd at every `L` state), `exit_parity` (an `L` phase closing on
   even `a` stops the run on the next step).  What remains is bounding the number of `L`
   phases whose closing parity is wrong -- the Collatz-like core of this machine.

### Status

`HalvingTimeBound` remains unproved; nothing `Admitted`, no new axiom.  The measurements say
the bound is true with 12x slack and that its content is the parity-coincidence time of the
tail.  No halting/non-halting conclusion; no required phrase applies.
## 27. The parity invariants, proved, and the sharp bound on wrong-parity closes

Every brick §26 listed is now a theorem in both files, with the audit closed: Lean `§8h`
of `M_758_TBudget.lean` (18 new `#print axioms`, all `[propext, Quot.sound]`), Rocq `§8h`
of `BB33_758_TBudget.v` (22 new `Print Assumptions`, no `Axioms:`).

| claim | Lean | Rocq |
|---|---|---|
| a surviving state with `a <= c` has odd `a` | `hrun_odd_of_le` | same |
| rules `i`/`j` keep both `a` and `c` odd | `J_step_odd` | same |
| `L` steps keep `c` odd and differ `a`'s parity | `L_step_odd` | same |
| an `L` close on even `a` stops the run | `hrun_stop_of_L_close` | same |
| the same facts on the run's own orbit `st` | `tail_step_odd` | same |
| the `L`-phase budget is downward closed | `L_budget_down` | same |
| no wrong-parity close before the last step | `survives_forbids_wrong_close` | same |

The `L` statement is `c' % 2 = 1 ∧ (c' = 1 ∨ (a' + a) % 2 = 1)`: it says the parities
*differ*, not `a' % 2 = 1 - a % 2`.  The subtraction form, and the bare `by omega` on the
compound branch goals, drag `omega` into `Classical.choice` (the file's older `L_step` still
carries it); the difference statement and the factored arithmetic do not.  Rule `e` is the
single exception and lands on `c' = 1` with odd `a'`.

The modulo arithmetic is factored into `mod_two_of_mod_four_{even,one,three}`,
`mod_four_three`, `half_mod_two_of_mod_four_{one,three}`, `three_mul_add_{five,eight}_odd`,
`flip_two`, `flip_four`, so the step case analysis only rewrites.  `flip_four` needs
`a ≠ c+1, c+2, c+3`: at `a = c+3` rule `c`'s drop is `0`, and `0 + a` is even.

### The bound on wrong-parity `L` phases is zero

`survives_forbids_wrong_close`: if `hrun c0 L a c = some (a', c')`, then no state
`st c0 k a c` with `k < L` is an `L` close on even `a`.  A wrong-parity close is therefore
*terminal* -- the run cannot take another step from it -- so a run has at most one, and it is
the last state of the run's life.  The count §26 flagged as the Collatz-like core is not open:
it is `0` before the end of a run and `1` at most.  In particular the wrong-parity phases
contribute at most one phase length to `T`.

### What blocks `T <= 10000` is the phase count, not the parity

With wrong-parity closes terminal, every surviving tail step belongs to a phase alternation
`L, j, L, j, ...` whose closes all have odd `a`.  `T = first L phase + tail` with the first
phase `<= 791` (`L_phase_le_791`), so `T <= 10000` needs `tail <= 9209`; the composition
charge `878*NL + 293*NJ` closes at the measured `NL <= 7`, `NJ <= 6`
(`7*878 + 6*293 = 7904`).  What is missing is exactly a bound on `NL`, `NJ`.

Neither budget can supply it, and `L_budget_down` is the reason made precise.  Both budgets
have the form "this phase's length is at most `log_{3/2}(Q/(2c))`" (resp. `log_3(Q/(a+1))`),
read off the phase's *own* start, and both are downward closed in the length: a phase of
length `n` admitted by the budget does not stop a phase of length `n-1` from being admitted,
so no budget sees the **parity** of a phase length -- which is exactly what decides the closing
parity of `a` -- and no budget counts phases.  Every new phase restarts the logarithm at a
state whose `Q` is only known to satisfy `Q >= Q_start + 3*steps` (`run_Q`), a bound at the
phase's own scale, so the logarithms do not telescope over an unbounded number of phases.

Concretely the missing inequality is a *lower* bound on `Q`'s growth per phase strong enough
to make the level decrease -- `Q(next phase start) >= Q(this phase start) + f(phase index)`
with `f` growing, or a per-phase decrease of `log_2(c)` / `log_3(a)`.  `Q_step` gives only
`+3` per step and the phase budgets give only upper bounds on lengths, so neither implies it.
Equivalently the residual is `HBudget 30000` (§26, route 1), and `hbudget_of_length` needs
`T <= 3333`, so that is not a way around the count either.

### Status

Both files green; no `sorry`, no `Admitted`, no `Parameter`, no custom axiom, no
`Classical.choice` in §8h.  `HalvingTimeBound` / `ResidualHalving` / `T <= 10000` remain
unproved; the open obligation is the phase-count bound `NL <= 7`, `NJ <= 6`, not any parity
statement.  No halting/non-halting conclusion; no required phrase applies.


## 28. `L_step` audit-clean, and the phase-count bound is *false* (2026-11-18)

This pass has two items: the `L_step` restatement, which is a fix, and the phase count, which
is a refutation.

### `L_step` no longer carries `Classical.choice`

`L_step` used to prove both inequalities of each branch with a single `omega` on the
conjunction.  `omega` on an `And` goal decides the split before proving the halves, and that
decision drags `Classical.choice` in even when both halves are linear.  The probe is exact:
`a - c - 1 + c <= a` alone and `3*c <= 2*(3*(c/2)+2)` alone are `[propext, Quot.sound]`,
while the conjunction of the two is `[propext, Classical.choice, Quot.sound]`.

Both files now state the per-rule arithmetic separately and let `L_step` only dispatch:

| lemma | files | content |
|---|---|---|
| `L_drop` | Lean, Rocq | `a - c - r + c <= a` for every `r`, when `c < a` |
| `L_grow_a` | Lean, Rocq | `3*c <= 2*(3*(c/2)+2)`, `c` even |
| `L_grow_b` | Lean, Rocq | `3*c <= 2*(3*((c-1)/2)+5)`, `c` odd |
| `L_grow_c` | Lean, Rocq | `3*c <= 2*(3*((c-1)/2)+8)`, `c` odd |

The residue facts `mod_two_of_mod_four_{even,one,three}` and `mod_four_three` moved from
section 8h-a to section 2b so that `L_step` (section 3) can use them.  Each branch is now
`exact <L_drop ..., L_grow_...>`: no `omega` sees a conjunction, and none sees a `mod` it
has to derive.  Result: `L_step` is `[propext, Quot.sound]`, and `phase_le_791` -- which
inherited the axiom through `L_step` -- is clean as well.  Rocq's `L_step` was already
axiom-free (it has no mod-aware automation) and is restated in the same shape so the two
proofs read alike.

### The phase-count bound is false, not merely unproved

Section 27 read the measured tail counts as `NL <= 7`, `NJ <= 6`.  That is wrong: the
post-`j` state `(2*3^7 - 1, 24) = (4373, 24)` has a halving run of `40` surviving steps with
**8 `L` phases and 8 `J` phases** (16 phases), and stops on the next step.  Both files prove
this with a computable counter:

* `pcnt c0 n a c` (Lean and Rocq) walks `step` from `(a, c)` for at most `n` steps under
  `hrun`'s stopping rule (true halt, `a' = 1`, `2*c' <= c0`) and counts the phases of the
  states visited: the first state starts a phase, and every step landing in the other region
  starts another.  `fst` is `NL`, `snd` is `NJ`.
* `witness_phase_counts : pcnt 24 41 (2*3^7 - 1) 24 = (8, 8)` -- kernel `decide` in Lean,
  `vm_compute` in Rocq; both print no axioms at all.
* `witness_run_stops : hrun 24 40 (2*3^7 - 1) 24 = some (782, 1937) /\ hrun 24 41 ... = none`.
* `phase_count_bound_false`: the existential form -- `k = 7 <= 292`, `1 <= c = 24 < 2*3^7`,
  `7 < NL`, `6 < NJ`.

Measured maxima for context (`_cyc.py`): over `k <= 8` exhaustively the maximum is `(8, 8)`;
the certified `844`-step trace at `k = 289, c0 = 2047` has `(13, 13)` and 26 phases, and its
tail segment after step `791` has `(9, 9)` in 53 steps (`_pc.py`).  So `(7, 6)` was a sampling
artefact, and the counts grow with the run.

### Why no count can close the residual

The proved per-phase budgets (`L_phase_le_878`, `J_phase_le_293`) charge `878` per `L` phase
and `293` per `J` phase, so a residual fits the `9209`-step window only if
`878*NL + 293*NJ <= 9209`.  The witness charges `878*8 + 293*8 = 9368 > 9209`
(`counting_budget_le_8`, `witness_charge_exceeds`).  That is stronger than section 23's
`(9,9)` arithmetic in two ways: it is kernel-checked at a family member rather than measured,
and it happens at `k = 7`, i.e. the counting route fails already at the smallest non-trivial
family states and not only on the extremal trace.

Hence `ResidualHalving` cannot be closed by bounding `NL`, `NJ` while the per-phase budgets
stay at `878`/`293`.  What remains is the length statement: a per-phase bound in terms of the
phase's *own* start (`L_phase_len_c0`, `J_phase_len_own` give the shape; the hardness is
`phase_two_breaks`, since the fixed-constant caps fail from phase 2 on).  The residual is a
halving-time statement about `c`, exactly as sections 23-27 said -- and the counting route is
now closed off by proof rather than by experiment.

### Status

Lean: `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` exit 0, 0 errors; `L_step` and
`phase_le_791` are `[propext, Quot.sound]`, as are `L_drop`/`L_grow_*` and the four moved
`mod_*` facts; `regB`, `pcnt` and the four witness theorems print "does not depend on any
axioms".  Rocq: `rocq compile -Q . Top BB33_758_TBudget.v` exit 0, every `Print Assumptions`
closed, no `Axioms:`.  `HalvingTimeBound` / `ResidualHalving` / `T <= 10000` remain unproved.
No halting/non-halting conclusion; no required phrase applies.

## 29. The retargeted residual: per-phase length at each phase's own start (2026-11-18)

Section 28 closed the counting route by proof.  This pass retargets the residual onto the
statement that route was standing in for, and proves the composition.

### The charge

Each phase is charged its own start.  The two budgets already have exactly that form:

| phase | budget at its own `(a_0,c_0)` | sharp charge |
|---|---|---|
| `L`, length `n` | `2*c_0*3^n <= 2^n*(a_0+2*c_0)` | `lLen a_0 c_0` = largest admissible `n` |
| `j`, length `m` | `3^m*(a_0+1) <= a_0+2*c_0+4*m` | `jLen a_0 c_0` = largest admissible `m` |

`lLen`/`jLen` are those ratios read as integers (`lScan`/`jScan` with fuel `a_0+2*c_0+2`):
`log_{3/2}((a_0+2*c_0)/(2*c_0))` and `log_3` of the `j` budget, with no logarithm in the
statement.  Both are computable and both are axiom-free definitions.  Downward closure is
`lAdm_down` (`L_budget_down` iterated) and `jAdm_down`; the `j` side is not a monotonicity of
its left-hand side alone, because the `j` budget's right-hand side grows with `m` -- one step
down costs `2` and `3^k*(a_0+1) >= 4` (`jAdm_step_down`).

### The per-phase bound is a theorem, at every start

`L_phase_len_c0`/`J_phase_len_own` linearised the budgets; this pass states and proves the
bound for *real phases of a halving run*, at whatever start the run has:

* `LPhaseAt C n a0 c0` -- the run survives `n` steps from `(a_0,c_0)`, the orbit is in `L`
  throughout (`c < a`) and rule `e` never fires; then `n <= lLen a_0 c_0`
  (`l_phase_len_at`);
* `JPhaseAt C m a0 c0` -- the run survives `m` steps and every step is rule `j`; then
  `m <= jLen a_0 c_0` (`j_phase_len_at`).

Both are `L_phase_budget`/`J_phase_budget` on the orbit `st` through `st_next`, then the scan
lemma.  No `878`, no `293`, no `phase_two_breaks`: the charge is evaluated at the phase's own
start, so it cannot fail from phase 2 on.

### The composition

`PhaseLedger` is the retargeted residual: for every post-`j` family member the run admits a
phase-aligned cut `b 0 = 0 < ... < b N = n`, every interval an `LPhaseAt` or a `JPhaseAt` at
its own start, with

    ssum (fun i => phaseCharge (run state at b i)) N <= 10000.

`halvingTimeBound_of_phase_ledger : PhaseLedger -> HalvingTimeBound` is the composition, and
it uses no phase count: `ssum_cutLen` says the cut's phase lengths add up to `n`
(`ssum_mono` then compares them with the charges), each interval is at most its own start's
charge, and the charges fit in `10000`.

### Exactly which hypothesis is the gap

Two components, now separated:

1. **The cut exists.**  Bookkeeping: `pcnt` (section 9) already walks the phases, so this is a
   decomposition lemma about `st`, not mathematics.
2. **The sum fits.**  `sum_i phaseCharge(a_i,c_i) <= 10000` over the run's phase starts.  This
   is section 27's alternation bound in additive form, and it is the whole gap.

It does not follow from the per-phase bounds, and `L_budget_down` is why: they are downward
closed, so they bound a phase's length without constraining how many phases there are.  Note
what the ledger is and is not: since every charge is at least the length it bounds, it is
*stronger* than the target -- a sufficient route, not a restatement of `T <= 10000`, and not
implied by it.  The ledger is *true* on everything measured -- `_ledger.py` computes the sum over the runs the
protocol already uses:

    exhaustive k <= 8:          19673 runs, max ledger 42   (k=7, c=24: T=41, 16 phases)
    + large-k samples:          19952 runs, max ledger 844  (k=289, c=2047: T=844, 26 phases)
    record trace k=289 c=2047:  ledger 844 = T   (charges 764,2,4,3,10,1,6,1,...,4,2,7,1)
    witness k=7 c=24:           ledger 42 vs T=41 (charges 11,1,2,2,2,1,2,2,4,1,...,2,1,5,1)

so the ledger is `<= 10000` with 11.8x slack, and it is tight at the record trace: there the
charge sum equals `T` (`844`), the first phase charged `764` -- its own `log_{3/2}` charge, and
its actual length.  What is missing is a proof that the sum of those logarithms telescopes --
section 27's level-decrease statement, now with the fixed caps out of the way.

### Status

Lean `lake env lean BusyBeaver/BB33/M_758_TBudget.lean` exit 0, 0 errors.  24 new
`#print axioms`: `lAdm`, `jAdm`, `lScan`, `jScan`, `lLen`, `jLen`, `lScan_ge`, `jScan_ge`,
`LPhaseAt`, `JPhaseAt`, `phaseCharge`, `PhaseLedger` print "does not depend on any axioms";
`lAdm_down`, `jAdm_step_down`, `jAdm_down`, `lScan_reaches`, `jScan_reaches`, `lLen_spec`,
`four_m_le`, `jLen_spec`, `l_phase_len_at`, `j_phase_len_at`, `ssum_mono` and
`halvingTimeBound_of_phase_ledger` are `[propext, Quot.sound]`; no `Classical.choice`, no
`sorry`.  Rocq `rocq compile -Q . Top BB33_758_TBudget.v` exit 0, 26 new `Print Assumptions`,
all `Closed under the global context`, no `Axioms:`.  `ResidualHalving` (`T <= 10000`) remains
unproved and the gap is named exactly: `PhaseLedger`.  No halting/non-halting conclusion; no
required phrase applies.
## 30. What the ledger sum actually is: the phase-start ratio walk (2026-11-18)

Section 29 left `PhaseLedger` as the gap.  This section records what that sum *is*, measured
with `_inv.py`, because it changes what a proof has to show.

### The charge is the logarithm of the phase start's own ratio

For a phase from `(a,c)` the two charges are

    L: log_{3/2}((a+2c)/(2c)) = log_{3/2}(1 + a/(2c))
    j: log_3((a+2c)/(a+1))   ~  log_3(1 + 2c/a)

so a phase is charged the logarithm of its start's ratio, and a phase *ends* exactly when the
ratio crosses 1 (`a <= c` ends an `L` phase, `a > c` ends a `j` phase).  The ledger is
therefore the total log-ratio travelled by the walk `a/c`, not a count of anything.

### The tail is scale-free; only the ratio matters

At `k = 289, c = 2047` the first `L` phase is `764` steps and ends with `a ~ 2^456`,
`c ~ 2^458`; the remaining 25 phases run at *that* scale, and the ratios at the phase starts
oscillate in a fixed window:

    k=289: a/c at L starts  2.9 .. 755     at j starts 0.045 .. 0.98
    k=292: a/c at L starts  2.2 .. 723     at j starts 0.039 .. 0.996
    k=7:   a/c at L starts  2.9 .. 182     at j starts 0.15  .. 0.85

`log_2(a)` stays in `454..460` for the whole tail and `log_2(c)` in `452..459`: the leading
terms of the rules (`(a,c) -> (a-c, 1.5c)` and `(3a, c-a)`) are homogeneous, so after the
first phase the orbit is the ratio walk of `a/c` alone, with the `+1/+2/+4` constants as
lower-order terms.  That is why the tail length is `~O(log c_0)` and not `O(c_0)`.

### Where that leaves the bound

`T = first phase + sum of log-ratios of the ratio walk`.  The first phase is `<= 791`
(proved), so `T <= 10000` needs the *sum of the log-ratios* of the tail to be `<= 9209`.
Measured it is `80` at the record trace and `<= 53` for every other trace in `_ledger.py`'s
19952 runs, so the bound is true with two orders of magnitude of slack.  What is missing is
still a statement about the walk: the log-ratio sum is the sum of the continued-fraction-like
digits of `a/c`, and no invariant proved so far bounds that digit sum.  The `878`/`293` caps
do not (section 28), the per-phase own-start charges do not (section 29), and the ratio window
above is measured, not proved.

Concretely, the next brick is a *lower* bound on the ratio at every phase start after the
first: `a >= c/K` with `K` explicit.  The mechanism that would give it is that a near state
(`c < a <= c+4`) stops the run in at most two steps (rule `e` when `a = c+2`, rule `c`
landing on `a = 0` when `a = c+4`, halts at `a = c+1, c+3`), so the ratio can only collapse
through a precisely-tuned drop -- a Diophantine condition, not a size condition.  That is the
same Collatz-like core sections 26-27 identified, now located exactly at the phase-start ratio.

### Proved this pass: a near state dies in two steps (section 11 of both files)

`hrun_near`, in `M_758_TBudget.lean` and `BB33_758_TBudget.v`:

    c0 >= 2  ->  c < a  ->  a <= c + 3  ->  hrun c0 2 a c = none

so no state with `c < a <= c + 3` survives two halving steps.  The case analysis is by `a - c`
and `c mod 4`: rules `f`, `halt1`, `halt3` halt; rule `a` lands on `a' = 0` or `a' = 1`; rule
`b` lands on `a' = 0` or `a' = 1`; rule `e` lands on `c' = 1`, and `2*1 <= c0` is exactly the
hypothesis `2 <= c0`.  The `a' = 0` and `a' = 2` cases are closed by `hrun_stops_of_even_le`.

Consequence for the ratio: a drop lands below `c` only through `a' = a - c - r` with
`a - c <= 4`.  The offsets `a - c in {1,2,3}` are now proved terminal, so a phase start with
`a` far below `c` can only come from `a = c + 4` with `c mod 4 in {0,2}`, and that case lands
on `a' = 3`.  That is the exact Diophantine bottleneck the ratio bound has to pass: the walk
can enter a collapsed ratio through one residue class of one offset, and never through a small
`a - c`.

Audits: Lean `hrun_near` and the three `hrun_two_*` helpers carry `[propext]` only (no
`Classical.choice`, no `sorry`); Rocq `hrun_near`, `hrun_two_*`, `orb_mod4_*` are all
"Closed under the global context".

### Status

Section 11 is new in both files this pass: Lean is green with it (exit 0, no `sorry`,
`hrun_near` `[propext]`-only) and Rocq compiles its `Print Assumptions` closed.
`HalvingTimeBound` / `T <= 10000` remain unproved; the gap is `PhaseLedger`, whose content is
the log-ratio (digit) sum of the scale-free ratio walk, and section 11 removes one of the two
ways the ratio can collapse.  No halting/non-halting conclusion; no required phrase applies.
## 31. The phase-start gap: `hrun_near` pins the collapse to `a = c + 4` (2026-11-18)

Section 30 asked for a lower bound `a >= c/K` at every phase start.  That form is **false at
`j` starts**: a `j` start only has `a <= c`, and the record trace itself reaches
`(3, 1.5*c+2)`-shaped states after a collapse, i.e. `a/c ~ 1/c`, with no positive `K` working.
What the ledger actually needs is the *gap* `a - c` at `L` starts, because an `L` step sends
`(a,c)` to `a' = a - c - r`: the `j` start's `a'` is the previous `L` start's gap minus `r`.
So the right object is the `L`-start gap, and section 12 of both files proves it.

### The new facts (Lean section 12 / Rocq section 12)

    hrun_two_gap_four_odd :  c % 4 = 1 \/ c % 4 = 3  ->  hrun c0 2 (c+4) c = none
    L_gap_ge_four         :  2 <= c0 -> c < a -> HSurvives c0 2 a c -> c + 4 <= a
    L_gap_four_shape      :  c < a -> a = c+4 -> HSurvives c0 2 a c ->
                                (c % 4 = 0 \/ c % 4 = 2) /\ st c0 1 a c = (3, 3*(c/2)+2)
    lLen_gap_four         :  3 <= c -> lLen (c+4) c = 1
    phaseCharge_gap_four  :  3 <= c -> phaseCharge (c+4) c = 1
    L_gap_four_ledger     :  3 <= c -> HSurvives c0 2 (c+4) c ->
                                (c % 4 = 0 \/ c % 4 = 2) /\ st c0 1 (c+4) c = (3, 3*(c/2)+2)
                                /\ phaseCharge (c+4) c = 1

`L_gap_four_shape` carries no bound on `c0`: the odd residues are killed by
`hrun_two_gap_four_odd`, which needs nothing about `c0`, so the earlier `2 <= c0` was
redundant and has been dropped.  `L_gap_four_ledger` is the formal ledger link: it
conjoins the collapse shape with `phaseCharge (c+4) c = 1` in one statement, so the
charge of a collapse is a theorem about the run, not a remark.

`L_gap_ge_four` is exactly `hrun_near` contrapositive: a surviving `L` state cannot have
`c < a <= c + 3`, so its gap is at least four.  `L_gap_four_shape` is the reduction section 30
asked for: at gap exactly four the two odd residues are dead within two steps
(`hrun_two_gap_four_odd`: rule `b` lands on `a' = 2`, rule `c` on `a' = 0`, both even in the
`J` region and killed by `hrun_stops_of_even_le`), so a surviving gap-4 state has `c` even and
its first step is rule `a` onto `(3, 3*(c/2)+2)` -- the unique small-`a` entrance to the tail.

### Why this is a ledger statement

`lLen_gap_four` and its `phaseCharge` form make the collapse cost explicit: the `L` phase
that starts at a surviving gap-4 state is charged exactly `1`.  So every collapse in a
halving run decomposes as

    one `L` step of charge 1   ->   a `j` phase from `(3, 3*(c/2)+2)`,

and the second piece is the only place where the walk can be expensive: `jLen 3 c0` is
`~ log_3(c0/2)`, i.e. up to `~458` steps at the record scale.  That is the residue of
`PhaseLedger` after this section: not "some phase may be huge", but "each collapse costs 1
plus the length of a `j` run from `(3, .)`, and there can only be as many collapses as the
run has gap-4 `L` starts".

The `lScan_stop` / `lScan_step` pair is the scan machinery used for the charge value: the
bounded search stops exactly when the next length is inadmissible, and takes a step exactly
when it is admissible (both axiom-free on the Lean side).

### Status

Lean exit 0 with section 12 (`hrun_two_gap_four_odd`, `L_gap_four_shape`, `lLen_gap_four`,
`phaseCharge_gap_four` all `[propext, Quot.sound]`; `lScan_stop`, `lScan_step` axiom-free; no
`sorry`).  Rocq compiles the same section with every `Print Assumptions` closed and no
`Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open.  No halting or
non-halting conclusion; no required phrase applies.

## 32. How many collapses can a run have? At most half its states (2026-11-18)

Section 31 pinned the collapse to `a = c + 4`; this section counts them.

### Measurement (`_g4.py`)

Exhaustive over the whole `k <= 8` family (19673 runs) plus 400 large-`k` samples: at most
**one** gap-4 `L` state per run, and 34 runs have one.  Split by parity: 2 hits with odd
`c < 3` (e.g. `k = 0, c0 = 1` at `(5,1)`, which `hrun_two_gap_four_odd` kills two steps
later), 29 with odd `c >= 3` (also killed by `hrun_two_gap_four_odd`), and 3 with even
`c >= 3` -- the genuine surviving collapse candidates that `L_gap_four_ledger` charges one.
No run has two, and no large-`k` sample has any.

### The theorems (Lean section 13 / Rocq section 13)

    g4 a c            := c < a /\ a = c + 4                 (a gap-4 candidate)
    g4cnt c0 n a c    := count of g4 states among the first n states of the run
    g4_step_le_three  : g4 a c -> step a c = Next a' c' -> a' <= 3
    g4_succ_not       : g4 a c -> step a c = Next a' c' -> ~ g4 a' c'
    g4cnt_le          : 2 * g4cnt c0 n a c <= n + 1  and  (~ g4 a c -> 2 * g4cnt ... <= n)
    g4cnt_le_half     : 2 * g4cnt c0 n a c <= n + 1
    g4_charge         : g4 a c -> 3 <= c -> HSurvives c0 2 a c ->
                          st c0 1 a c = (3, 3*(c/2)+2) /\ phaseCharge a c = 1

`g4_step_le_three` is the engine: a gap-4 state steps by rule `a` to `a' = 3` (even `c`), rule
`b` to `2`, rule `c` to `0`, and the halting branches are impossible because `a = c + 4` is
neither `c + 1` nor `c + 3`.  So no gap-4 state is followed by another and no halting state is
gap-4, which gives the count bound `2 * count <= n + 1` (written division-free).  `g4_charge`
is `L_gap_four_ledger` read at a run state, so the states being counted are exactly the ones
charged one.

### What it gives and what it does not

It gives at most `(n+1)/2` collapses in a run of length `n`: with `T <= 10000`, at most 5000,
each contributing one charged step.  It does **not** close `PhaseLedger`: each collapse is
followed by a `j` phase from `(3, 3*(c/2)+2)` whose charge is `jLen 3 (3*(c/2)+2)`, and this
count does not bound those.  The measured truth is `<= 1` collapse per family run, so the
proved `n/2` is far from sharp; it is the scale-free statement that needs no hypothesis on
`c0`.

### Status

Lean exit 0 (`g4_step_le_three`, `g4_succ_not`, `g4cnt_le`, `g4cnt_le_half`, `g4_charge` all
`[propext, Quot.sound]`, no `sorry`); Rocq exit 0, 166 `Print Assumptions` closed, no
`Axioms:`.  `PhaseLedger`, `HalvingTimeBound`, `T <= 10000` remain open.  No halting or
non-halting conclusion; no required phrase applies.

## 33. Odd-`c` gap sharpening: gaps 4 and 6 die, gap 5 pinned to `c % 4 = 1` (2026-11-27)

Section 14 in both `M_758_TBudget.lean` and `BB33_758_TBudget.v` sharpens the Diophantine
bottleneck on odd-`c` orbits (all reachable post-`j` states have `c` odd since rules `a` and
`g` are unreachable):

    hrun_two_gap_five_mod3     : c % 4 = 3 -> hrun c0 2 (c + 5) c = none
    hrun_two_gap_six_odd       : c % 4 = 1 \/ c % 4 = 3 -> hrun c0 2 (c + 6) c = none
    L_gap_ge_five_odd          : 2 <= c0 -> c < a -> (c % 4 = 1 \/ c % 4 = 3) ->
                                 HSurvives c0 2 a c -> c + 5 <= a
    L_gap_five_or_ge_seven_odd : 2 <= c0 -> c < a -> (c % 4 = 1 \/ c % 4 = 3) ->
                                 HSurvives c0 2 a c ->
                                 (a = c + 5 /\ c % 4 = 1 /\ st c0 1 a c = (3, 3*((c-1)/2)+5))
                                 \/ c + 7 <= a

In parallel, we tested two non-local angles:
1. **Exact affine cycle-skipping forward acceleration** from `c = 1,059,491,543,272,883`:
   skips `254,074,710,616` chains (`bcjjch`, `dc = 80`) in `0.01s` to `1,079,817,520,122,241`,
   then hits the `bcjjj...` L-phase chaotic zone (`n_L ~ 60`, `2^{n_L} > c`, no short period).
2. **Expanding-map periodic-ray analysis** in `s = 2c/(a+2c)`: exact drift `s* * dQ / 2` is
   non-integral for all short surviving cycles (`bbj..bbbbjj`), and adversarial shadowing at
   `k = 292` around `s* = 8/23` and `32/227` dies by `T = 558` and `623`.

Audits: Lean exit 0 (`[propext, Quot.sound]`, no `sorry`, no `Classical.choice`); Rocq exit 0
(all `Print Assumptions` `Closed under the global context`).  `PhaseLedger`, `HalvingTimeBound`,
and `T <= 10000` remain open; no halting or non-halting conclusion; no required phrase applies.

