# Absorbing Tag System (ATS / Tagy Tag)

**Absorbing Tag System (ATS)**, also called **Tagy Tag**, is a local
Busy-Beaver-style variant in the Tiny Tag / cyclic-tag family.  It keeps a
single FIFO tape but replaces a static external rule table with **function
tokens whose arguments absorb adjacent bits and change their own priority**.
The model was developed in the bbchallenge Discord discussion summarised in
the task notes; this directory is the reference implementation used for the
local experiments.

This is an informal Busy-Beaver-style model, not an FGH-level machine.  No
general termination or complexity theorem is claimed here; the individual
Loom proof below is explicitly marked as a theorem.

## Tape and length

A tape is a finite ordered sequence `S = (t1, ..., tm)`.  A token is one of:

- a primitive bit `0` or `1`;
- a function token `fn(alpha)`, where `alpha` is a non-empty binary string
  (`alpha in {0,1}+`).

`fn(0)` and `fn(1)` are still function tokens during absorption even though
their head behavior is the same as a primitive `0` or `1`.

The **length** of a tape uses the convention requested in the source thread:

```text
length(0) = length(1) = 1
length(fn(alpha)) = length(alpha)
```

The `fn(...)` wrapper itself is not counted.  Thus `fn(0)` and `fn(1)` each
have length 1, `fn(10)` has length 2, and so on.  For a tape, length is the
sum of the token lengths.

## One step

A step has two phases, in this order.  A step is counted once per head
execution, even if the absorption phase did nothing.

### 1. Internal absorption

Scan the tape from left to right.  For a function `tj = fn(alpha)` at an
**internal** position (neither the first nor the last token), if the token
immediately to its right is a primitive bit `d`:

```text
fn(alpha)  ->  fn(d ++ alpha)
```

and the primitive token `tj+1` is removed.  The scan continues at the same
function, so it absorbs the whole run of primitive bits to its right until it
hits another function or reaches the end of the tape.  A function that was
internal when it started absorbing may become the last token while absorbing;
that is allowed.  Functions at the head or tail do not absorb.

### 2. Head execution

Pop the first token `t1`; let `S'` be the remaining tape.

- If `t1 = 0`: do nothing (append nothing).
- If `t1 = 1`: append **copies of** the next two tokens of `S'` to the tail,
  in order — the two tokens **stay** at the front, so a `1` head grows the tape
  by one token instead of shortening it.  If fewer than two tokens remain,
  append that many copies.
- If `t1 = fn(alpha)`:
  - If `alpha` contains no `1` (pure zeros): behave as a lone `0`; append
    nothing.
  - If `alpha = "1"`: behave as a primitive `1`; append copies of the next
    two tokens.
  - Otherwise (`alpha` is composite):
    - Let `c0 = count(alpha, "0")` and `c1 = count(alpha, "1")`.
    - The **one-rule** is:
      - find the first `1` in `alpha`;
      - if `len(alpha) > 3`, let `rest` be `alpha` with that first `1`
        removed;
      - otherwise let `rest = alpha[1:]` (drop the first character);
      - append `fn(1)`, and append `fn(rest)` if `rest` is non-empty.
    - The **zero-rule** is: if the tape is non-empty, delete its last token.
      **The zero-rule only exists when `alpha` contains at least one `0`.**
    - Fire the rules in this order:
      - `c0 = 0`: only the one-rule (no zero-rule);
      - `c1 > c0`: one-rule, then zero-rule;
      - `c0 > c1`: zero-rule, then one-rule;
      - `c1 = c0`: if `alpha[0] = "1"`, one-rule then zero-rule; otherwise
        zero-rule then one-rule.

The machine **halts when the tape becomes empty**.  There is no separate
HALT token.  The empty tape has no outgoing transition.

## Reference implementation

`ats.py` is a readable list-based reference simulator.  It also supports
exact state-repetition detection and a rigorous zero-free decider.

```powershell
cd bbwork/bb-variants/ATS

# One-step / short trace
py -3 ats.py sim "1 1 1 0 fn(1) fn(1) fn(1) fn(0)" --trace 24 --trace-every 1

# Longer run; no cycle table, sample the shape
py -3 ats.py sim "1 1 1 0 fn(1) fn(1) fn(1) fn(0)" --max-steps 30000 --sample-every 1000 --no-cycles

# Exhaustive-by-length search (slow; cutoffs are unclassified, not proofs)
py -3 ats.py search --max-n 5 --step-limit 100000

# C exhaustive search (recommended for n=6..8)
gcc -O3 -std=c11 -o ats_search.exe ats_search.c
./ats_search.exe --n 8 --max-steps 100000 --max-tokens 200000

# The same sweep split across processes:
./ats_search.exe --n 8 --max-steps 100000 --max-tokens 200000 --shard 0 --shards 8
```

Deciders in `simulate`:

- **exact cycle detection**: if the full token tuple repeats, the orbit is
  periodic and non-halting;
- **zero-free decider**: if a non-empty tape has no zeros and at least two
  tokens, it can never halt.  Absorption preserves the zero count, neither
  rule generates a zero when none exists, and a zero-free head either
  reproduces at least one token or is `fn(1^k)`, which expands.  The
  `len(tape) >= 2` condition is needed because a one-token zero-free tape
  does halt.

The simulator's `--max-steps` and `--max-tape-len` exits are **not**
non-halting proofs.

## Probe: `1 1 1 0 fn(1) fn(1) fn(1) fn(0)`

This is the requested length-8 extension of the reported length-7 champion.
Its initial length is `3 + 1 + 1 + 1 + 1 = 8`.

The general simulator does not halt within 30,000 steps.  More usefully, the
orbit quickly becomes a **two-reservoir rotation around a fixed core**:

```text
S(a, b) = fn(1)^a ++ C ++ fn(1)^b
```

where `C` is a fixed 74-token word: 47 zero-bearing function tokens separated
by 27 `fn(1)` tokens.  `C` has 141 zeros and length 193.  The orbit first
takes this form at step 884 (621 tokens: 547 `fn(1)` on the left, the core,
and no right reservoir).  Once it is in this form, the absorption phase is
vacuous (every token is a function), and all motion is in the two counts
`a` and `b`.

Observed with `probe.py`:

```text
step       tokens    length   zeros   non-fn1   left a   right b
1000          737       856     141        47      431       232
10000        9429      9548     141        47
101000     100198    100317     141        47    39146     60978
1001000    999967   1000086     141        47   114225    885668
```

The core is exactly unchanged after 1,000,000 fast steps.  The token count
grows at an average rate just below one per step, and the length/token gap
stays constant at 119 (the core contributes 193 length but only 74 tokens).
The left reservoir is repeatedly consumed and regenerated at the tail; when
the head reaches a core composite, that composite fires and is returned to
the core.

The core's zero-heavy composites form a visible carry chain.  With a tail
`fn(1)` available, the four shapes behave as follows when they reach the
head:

```text
fn(001110)  ->  fn(1), fn(00110)   (zero-rule pops one tail fn(1))
fn(00110)   ->  fn(1), fn(0010)
fn(0010)    ->  fn(1), fn(000)
fn(000)     ->  (pure zeros; the token simply disappears)
```

So a core pass consumes tail fuel, emits a fresh `fn(1)`, and advances to a
shorter zero-heavy shape.  While the head is in the left `fn(1)` reservoir,
one `fn(1)` is popped and two are appended, giving the near-one-token-per-step
growth.  This is the sense in which the orbit looks like a small finite-state
transducer or relay rather than a chaotic tag system.

This is an empirical probe, not a proof of non-halting.  The one-token
`zero-free` decider does not apply because the core retains 141 zeros.  The
observed fixed core suggests a finite-state rotor with two unbounded
reservoirs, which is a plausible route to a rigorous linear-growth proof, but
that proof has not been formalised here.

### Neighbor anomaly

The probe is also a sharp non-monotonicity in the length parameter.  Removing
one or two of the `fn(1)` tokens gives exactly the reported length-7 and
length-6 champions:

| Length | Tape | Result |
|---:|---|---|
| 6 | `[1, 1, 1, 0, fn(1), fn(0)]` | halts in 108 steps (verified for this tape) |
| 7 | `[1, 1, 1, 0, fn(1), fn(1), fn(0)]` | halts in 253 steps (verified for this tape) |
| 8 | `[1, 1, 1, 0, fn(1), fn(1), fn(1), fn(0)]` | no halt through 1,001,000 steps; fixed-core regime |

Adding one length-1 `fn(1)` token turns a near-collapse into the long-lived
fixed-core orbit.  The shape at sampled steps shows the divergence clearly:

```text
step   n=6 tokens/zeros    n=7 tokens/zeros    n=8 tokens/zeros
50          20 / 39             27 / 45             33 / 36
100          8 / 24             42 / 75             69 / 54
200       halted (108)         31 / 66            127 / 93
250           -                  3 / 9             163 / 96
253           -              0 / 0 (halt)         166 / 96
```

The length-7 orbit reaches three all-zero function tokens at step 250 and is
empty three steps later.  The length-8 orbit has already locked its zeros
into the 47-composite core and is still growing at that point.  This is a
one-token phase change, not a monotone runtime curve; it is also a warning
that small-length lower bounds cannot be extrapolated by adding neutral
`fn(1)` padding.

The endgame shows the mechanism: by step 250 the length-7 tape is exactly
`fn(000), fn(000), fn(000)`, so it has no `fn(1)` fuel left and the pure-zero
heads erase the remaining tokens one per step.  The length-8 tape still has
a large `fn(1)` reservoir at that point, so its zero-rule always has a tail
token available to consume; the extra `fn(1)` is fuel that protects the
zero-bearing core from the terminal cascade.

Reproduce the probe:

```powershell
py -3 probe.py                       # 1,000,000 fast steps
py -3 probe.py --steps 100000 --show-core
```

`probe.py` starts from the general simulator for 1,000 warmup steps, asserts
that all tokens are functions, and then uses a deque fast path.  That fast
path is observationally identical to `ats.py` on the no-primitive states it
accepts.

## Search results

`ats_search.c` enumerates every tape of a chosen ATS length.  The candidate
counts are 14,912 for length 6, 78,080 for length 7, and 408,832 for length 8.
The local sweeps used a C simulator with exact-state cycle detection, a
zero-free decider, a step cap, and a token cap.

| Length | Search cap | Best halter found | Notes |
|---:|---:|---|---|
| 6 | 1,000,000 steps / 200k tokens | 108, `[1, 1, 1, 0, fn(1), fn(0)]` | no improvement; 2,324 tape-cap holdouts |
| 7 | 1,000,000 steps / 200k tokens | 253, `[1, 1, 1, 0, fn(1), fn(1), fn(0)]` | no improvement; 16,472 tape-cap holdouts |
| 8 | 100,000 steps / 200k tokens | **307**, `[fn(11), 1, 1, 0, 1, 1, 0]` | 105,755 halters; 110,988 step-limit holdouts |

The length-8 tape is a genuine 8-symbol halter: `fn(11)` contributes two
length units and the six primitive tokens contribute six more.  It was also
checked independently in the Python simulator and halts in exactly 307
steps.  It is the new best length-8 candidate found here, but it is not
proven to be the class maximum: the 110,988 candidates still running at the
100,000-step cap were not resolved.

The length-6 and length-7 sweeps are exhaustive over all initial tapes, but
their tape-cap holdouts are also unresolved.  In particular, no new length-6
or length-7 halter above 108 or 253 was found in those sweeps.

## BMO machine: Loom

The tape of ATS length 9

```text
[1, fn(1), 0, 1, fn(1), fn(01), 1, 0]
```

is a certified non-halting machine with a BMO-style proof.  It is not
a cryptid in the strict sense: the invariant below is itself a decider.
After 2,000 ordinary
steps it has entered a phase in which every token is a function and every
token belongs to the finite set

```text
T = {fn(1), fn(01), fn(0101), fn(001)}.
```

`T` is **closed under head execution**.  The four cases are:

```text
fn(1)    -> copies the next two tokens (no new type)
fn(01)   -> zero-rule, then fn(1), fn(1)
fn(0101) -> zero-rule, then fn(1), fn(001)
fn(001)  -> zero-rule, then fn(1), fn(01)
```

Absorption is vacuous because there are no primitives.  Consequently, once
the tape is in `T`, it remains in `T`.  Every head is either `fn(1)`, which
increases the token count by one, or a zero-bearing composite, which appends
two tokens and deletes one tail token, leaving the token count unchanged.
Thus the token count is nondecreasing.

### Why Loom never halts

Let `M` be the number of tokens.  At step 2,000, `M = 1,804`.  In `T`, every
head is either `fn(1)` or one of the three zero-bearing composites.  An
`fn(1)` head appends two tokens and pops one, so `M` increases by one (the tape
is far longer than two tokens).  A composite head pops one token, the
zero-rule removes one tail token, and the one-rule appends two tokens, so `M`
is unchanged.  Hence `M` is nondecreasing and stays at least 1,804 forever.

Suppose `M` were bounded.  Then it would eventually be constant.  In that
suffix no `fn(1)` head can occur: there are at least 1,804 tokens, so an
`fn(1)` head has at least two tokens left after the pop and increases `M`.
So every head in the suffix is a composite.

Let `C` be the number of composite tokens.  A `fn(01)` head pops a composite
and appends only `fn(1)`, so `C` strictly decreases.  A `fn(0101)` or
`fn(001)` head pops one composite and appends one new composite, but it leaves
that composite at the tail.  On the next composite head the zero-rule deletes
that tail composite, so `C` decreases by at least one over at most two
composite steps.  Thus `C` would decrease indefinitely, which is impossible
for a nonnegative integer.  Therefore `M` is unbounded.

An unbounded nondecreasing `M` rules out both halting and a repeated state.
So Loom is a proved non-halting, non-cycling machine.  This is a finite
invariant proof, not a cryptid in the “resists every decider” sense.

Observed after 10,000,000 fast steps following the warmup:

```text
tokens      10,001,038
zeros               95
token decreases       0
outside T          none
```

The core is not fixed; it has the form `fn(01)^a` together with two
`fn(0101)` tokens and four `fn(001)` tokens, and `a` increases slowly.  The
orbit therefore does not reduce to the fixed-core rotation of the length-8
probe.

Reproduce the finite check:

```powershell
py -3 cryptid.py --steps 1000000
py -3 cryptid.py --steps 10000000
```

On Turing completeness: no proof is claimed here.  A structural limitation is
that after the primitive phase the arguments of function tokens can only
shorten (no absorption remains), so the reachable argument alphabet is finite.
That does not settle whether the resulting finite-alphabet queue rewrite is
Turing complete; no reduction or non-Turing-completeness invariant is known
to this directory.

## Cryptid candidate: Rattle

The all-function tape of ATS length 14

```text
[fn(11111), fn(1), fn(0011), fn(1), fn(01), fn(0)]
```

is one of the cryptid candidates found by the all-function random search.  It is not
a fixed-core rotor and it is not captured by the zero-free or cycle deciders.
Its observed type set after 10,000,000 steps is

```text
{0, 001, 0011, 01, 1, 11, 111, 1111, 11111}
```

and its core keeps changing.  The `fn(11)` count moved from 148 to 388 and
the `fn(01)` count from 22 to 42 between the 10,000-step and 10,000,000-step
checkpoints; the zero count rose from 26 to 46.  The token count is almost
monotone but has one recorded decrease, so the simple Loom-style monotone
argument does not apply.

At 10,000,000 fast steps:

```text
tokens       9,999,526
zeros               46
token decreases      1
core types         001: 2, 01: 42, 11: 388, 111: 9, 1111: 3
```

This is a candidate, not a theorem.  In particular, the finite type set means
a type-count analysis is still conceivable; I have not found a measure that
closes it, and I am not claiming that none exists.  The open question is
whether the core counts eventually lock or whether this orbit needs a genuinely
new invariant.

Reproduce:

```powershell
py -3 rattle.py --steps 10000000
```

## Cryptid candidate: Grove

The all-function tape of ATS length 32

```text
[fn(010), fn(011), fn(00011000), fn(111), fn(1111111),
 fn(10), fn(10), fn(0001)]
```

is the strongest cryptid candidate in this directory.  It starts with no
primitives, survives 10,000,000 fast steps, and its core keeps producing new
counts of existing types rather than settling into the fixed-core pattern.
Its observed type set is

```text
{000000, 0001, 0001000, 00011000, 010, 011, 1, 10, 11,
 111, 1111, 11111, 111111, 1111111},
```

and, after a short transient, the zero count remains fixed at 54 while the
`fn(11)` and `fn(111)` populations grow.  At 1,000,000 steps the core had
6,490 non-`fn(1)` tokens;
at 10,000,000 it had 10,240, with counts

```text
11: 9461, 111: 725, 1111: 33, 11111: 9,
111111: 3, 000000: 7, 0001000: 2
```

The token count at 10,000,000 steps was 9,999,716, with 120 decreases.  The
orbit is not classified by zero-free, cycle, or fixed-core detection.  This is
a candidate, not a theorem: the finite type set still admits a possible
type-count analysis, and I have not found a measure that closes it.  The open
question is whether the growing `fn(11)`/`fn(111)` populations lock, cycle, or
continue forever.

Reproduce:

```powershell
py -3 grove.py --steps 10000000
```

## Reported small cases

The source Discord thread reports these champions (the listed step counts
are lower bounds unless the corresponding class was exhaustively closed):

| Length | Steps | Tape |
|---:|---:|---|
| 1 | 1 | `[0]` |
| 2 | 3 | `[1, 0]` |
| 3 | 11 | `[1, 1, 0]` |
| 4 | 21 | `[fn(11), 1, fn(0)]` |
| 5 | 48 | `[1, 1, fn(1), fn(00)]` |
| 6 | 108 | `[1, 1, 1, 0, fn(1), fn(0)]` |
| 7 | 253 | `[1, 1, 1, 0, fn(1), fn(1), fn(0)]` |
| 8 | 307 | `[fn(11), 1, 1, 0, 1, 1, 0]` |

These are recorded for orientation, not independently verified by this
directory.  In particular, `length 4: 21` differs from the earlier pure-bit
value 20, and the length-8 probe above is not the same tape as the 307-step
candidate below.  The `n=1`,
`n=2`, and `n=3` rows are independently reproduced here by exhaustive
generation: every non-halting case is discharged by the zero-free or cycle
decider, so those three values are exact; the higher rows remain reported
lower bounds.

The length-8 row is the local 100,000-step sweep result from this directory,
not a reported value from the source thread.  It is a lower bound until the
remaining holdouts are resolved.

## 2-tag compilation status

`tag2ats.py` contains the exact reference check for realsheepthe's size-11
Post tag cryptid `11111_20_1` (`0->11111`, `1->20`, `2->1`, start `00`). The
tag recurrence is reproduced:

```text
00 -> S(5) -> S(14) -> S(7) -> S(19) -> S(49) -> S(124) -> ...
```

### Positive result: the length-five production as an ATS orbit

The production `0 -> 11111` is realizable in ATS. The gadget

```text
[fn(11), fn(11)]
```

has ATS length 4 and reaches five `fn(1)` tokens in exactly three steps:

```text
step 0  len= 4  [fn(11), fn(11)]
step 1  len= 4  [fn(11), fn(1), fn(1)]
step 2  len= 4  [fn(1), fn(1), fn(1), fn(1)]
step 3  len= 5  [fn(1), fn(1), fn(1), fn(1), fn(1)]
```

This handles the length-five production itself: two length-2 tokens for tag
symbol 0 become five length-1 tokens for tag symbol 1. It does not by itself
simulate the following tag steps.

### No-go theorem for uniform one-token encodings

The code now proves, rather than hard-codes, that no uniform one-token
encoding can simulate this tag system. Each tag symbol is one ATS token, and a
word is the concatenation of its images; the number of ATS steps per tag step
may depend on the word.

Let `V` be the image of tag symbol 1. The first transition `00 -> 11111`
forces the orbit from two copies of `E(0)` to become exactly `V,V,V,V,V`.
Starting from one token type, ATS stays in a single family: if `E(0)` is a
primitive, only primitives occur; if it is a function token, only function
tokens occur (the one-rule appends `fn(1)` and `fn(rest)`, the zero-rule
deletes, and no rule creates a primitive). Absorption is vacuous in the
function-only case because it needs an internal function followed by a
primitive.

To create the fifth copy, the last growing step can only copy a token or
append `fn(1)`. A composite `V` cannot be the sole appended type, because the
one-rule always appends `fn(1)` as one of its two outputs. Hence
`V` is primitive `1` or `fn(1)`. Five such tokens can only copy more
primitive-1/`fn(1)` tokens; no zero-bearing or composite token can ever
appear. But the second tag step is `11111 -> 11120`, whose image needs the
images of symbols 2 and 0. Those cannot be zero-bearing, and there are only
two closed token types for three tag symbols, so no injective one-token
encoding exists. This is a structural proof for the one-token class, not a
simulation cutoff.

### Bounded block search

`tag2ats.py compile` also runs a real exhaustive search over fixed-length
block encodings. A candidate must reach the `00 -> 11111` image and then
match every tested tag word exactly, with a schedule depending on the head
symbol. The default run tests:

- every uniform one-token encoding over primitives and `fn(alpha)` with
  `|alpha| <= 2`, schedules 1..8, words up to length 4 (512 encodings);
- every two-token block over `{0, 1, fn(0), fn(1), fn(00), fn(11)}` with
  per-symbol schedules 1..8 and words up to length 4 (46,656 encodings).

No full encoding was found (8 and 108 mappings respectively reached
`00 -> 11111`, but none matched the following tag words). The search is explicitly bounded: it does not
cover longer blocks, larger token alphabets, or arbitrary stateful encodings,
and therefore does not prove universal impossibility outside the one-token
class. No ATS tape for the complete tag orbit is emitted, and no new ATS
cryptid is claimed.

Reproduce:

```powershell
py -3 tag2ats.py tag --steps 120
py -3 tag2ats.py compile
py -3 tag2ats.py search --block-length 2
```

## Files

- `tag2ats.py` — 2-tag recurrence, verified length-five ATS gadget, one-token no-go theorem, and bounded block-encoding search.
- `ats.py` — reference simulator, deciders, exhaustive-by-length search, CLI.
- `probe.py` — fixed-core probe for the requested length-8 string.
- `ats_search.c` — C exhaustive search engine used for the length 6-8 sweeps.
- `cryptid.py` — reproducible probe for the ATS-length-9 Loom candidate.
- `rattle.py` — reproducible probe for the ATS-length-14 Rattle cryptid candidate.
- `grove.py` — reproducible probe for the ATS-length-32 Grove cryptid candidate.
