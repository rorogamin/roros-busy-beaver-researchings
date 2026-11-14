# BB(3,3) halt exclusions: Wily Coyote ends `22`, #397 ends `1`

**Status banner.** Every lemma named here is kernel-checked in the repository. The exclusion lemmas
are *halt-exclusion certificates*: they rule out halting for an infinite class of words. They are
**not** non-halting proofs, and neither Wily Coyote (#531/#532) nor #397 is solved. Axioms for every
lemma below are `propext` (and `Quot.sound` for the two block-power lemmas); no `sorry`, no
`Classical.choice`.

Files:

* `bbwork/cryptids_a6/BusyBeaver/BB33/WilyCoyote.lean` — shared engine for #531/#532.
* `bbwork/cryptids_a6/BusyBeaver/BB33/M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA.lean` — #397 (Ralph Wolf).

## 1. The two exclusion lemmas

### Wily Coyote: no halting word ends in `2 2`

```lean
theorem wilyPass_ne_none_of_ends_false_false (q : WilyMode) (u : List Bool) :
    wilyPass q (u ++ [false, false]) ≠ none

theorem next_ne_none_of_ends_false_false (u : List Bool) :
    next (.W (u ++ [false, false])) ≠ none
```

Halting is `.s1` reaching the blank boundary, and the only transitions *into* `.s1` are `s0`
reading `2` (`false`) and `s2` reading `1` (`true`). Two cases kill a word ending `22`: reading the
final `2` in `s0` would require the penultimate cell to be `1`, and `s2` reading `2` returns to
`s2` rather than `.s1`. Proof: induction on `u` generalizing the mode; every recursion rule lands
on a shorter suffix still ending in `22`, `.s3` returns `some` outright, and the suffix never
empties.

### #397: no halting word ends in `1`

```lean
theorem pass_ne_none_of_ends_true (q : Carry) (u : List Bool) :
    pass q (u ++ [true]) ≠ none

theorem next_ne_none_of_ends_true (u : List Bool) :
    next (.W (u ++ [true])) ≠ none
```

`pass` halts only at the boundary in carry `.cc` or `.ce`, and those are entered *only* by `ca`
reading `false` and `cd` reading `false`. Reading a `1` never lands in `.cc`/`.ce`
(`ca ↦ cb`, `cb ↦ some`, `cc ↦ cd`, `cd ↦ cf`, `ce ↦ cd`, `cf ↦ ca`), so one trailing cell
suffices.

### A word ending in `0, 1` steps to one ending in `1`

```lean
theorem pass_ends_true_of_ends_false_true (q : Carry) (u : List Bool) :
    ∃ v : List Bool, pass q (u ++ [false, true]) = some (v ++ [true])

theorem next_ends_true_of_ends_false_true (u : List Bool) :
    ∃ v : List Bool, next (.W (u ++ [false, true])) = some (.W (v ++ [true]))

theorem next_next_ne_none_of_ends_false_true (u : List Bool) :
    (next (.W (u ++ [false, true]))).bind next ≠ none
```

The scan can lose a trailing `1` only by exiting early at the *final* cell, and that early exit is
the rule `cb` reading a cell. `cb` is entered only from `ca` reading a `1`, so an early exit at the
final cell needs the *penultimate* cell to be `1`. When the word ends in `0, 1` the penultimate
cell is `0`, so no such exit can occur: every other branch appends a boundary block ending in `1`
or copies the word's own trailing `1`. The last corollary says such a configuration survives at
least two steps.

### Companion transparency lemmas (same files)

* `pass_ca_block`, `pass_ca_blocks`: `pass .ca (0 1 0 0 :: u) = 1 0 0 0 :: pass .ca u`, hence
  `pass .ca ((0100)^k ++ t) = (1000)^k ++ pass .ca t`.
* `wilyPass_s0_block`, `wilyPass_s0_blocks`: `wilyPass .s0 (0 1 :: u) = 1 0 :: wilyPass .s0 u`,
  hence `wilyPass .s0 ((01)^k ++ t) = (10)^k ++ wilyPass .s0 t`.

Consequence: both machines' words have the form `block^k ++ t`, and the step acts on `t` alone.
`k` is irrelevant to halting.

## 2. Why the excluded suffix is not the same for the two machines

| machine | halt mode | entered from | excluded suffix |
| :--- | :--- | :--- | :--- |
| Wily Coyote | `.s1` | `s0` on `2`, **and** `s2` on `1` | `22` (two cells) |
| #397 | `.cc`, `.ce` | `ca` on `2`, `cd` on `2` only | `1` (one cell) |

Wily's halt mode has two entry paths, so both must be closed off, which forces the penultimate
cell; #397's two halt modes share a single entry symbol, so the final cell alone decides.

## 3. Halting-set counts (all words of the given word length, brute force)

### Wily Coyote — Fibonacci

Halting words by length `n = 1..14`:

```
1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377      (= F(n))
```

Last-two cells among the 985 halting words of length ≤ 14:

| last two | count |
| :--- | ---: |
| `11` | 233 |
| `10` | 376 |
| `01` | 376 |
| `00` | **0** |

### #397 — geometric

Halting words by length `n = 0..14`:

```
0, 1, 0, 2, 0, 6, 0, 18, 0, 54, 0, 162, 0, 486, 0
```

i.e. no halting word of even length, and `2 · 3^(m-1)` at odd length `2m+1` for `m ≥ 1`.
Total up to length 13: `729 = 3^6`.

| feature | count / value |
| :--- | :--- |
| last cell `1` | **0** of 729 (all end in `2`) |
| last two `00` | 364 |
| last two `10` | 364 |

So the complementary suffix does **not** work here: `[2,2,2]` halts. The `1`-suffix lemma is the
correct analogue, not a `22` analogue.

## 4. The carry obstruction for #397, and what it rules out

`next` prepends `false`, so every successor word starts with `2`. That suggested a tape-only
invariant on the right end. **No fixed-length cell-suffix predicate can be preserved.** The
following transfer table is exhaustive: for a three-cell suffix `s` it lists `pass q s` (the
boundary is treated as the end of the word, so this is exactly the sweep's local behaviour).

| s | ca | cb | cc | cd | ce | cf |
| :-- | :-- | :-- | :-- | :-- | :-- | :-- |
| `001` | 11001 | 101 | 110001 | 00001 | 010001 | 001001 |
| `101` | 011 | 001 | 001001 | 1011001 | 101001 | 110001 |
| `011` | 1011001 | 111 | 100 | 0111001 | 000 | 0111 |
| `000` | **halt** | 100 | 1111 | **halt** | 0111 | 0001 |
| `010` | **halt** | 110 | 101 | **halt** | 001 | 010001 |
| `100` | 010 | 000 | 0001 | **halt** | 1001 | 1111 |
| `110` | 000 | 010 | 010001 | **halt** | 110001 | 101 |
| `111` | 001 | 011 | 0111 | 11001 | 1111 | 100 |

Reachable words all end in `001` — 5000 consecutive tails in the reduced model, and 20,000
consecutive words in the full-word simulation (final length 20,065) — and for `s = 001` the five
good carries reproduce `001` while `cb` produces `101`. Closing `{001}` under the table therefore
yields **all eight** suffixes, including halting ones (`000` in `ca`) and suffixes ending in `2`.
Hence a preserved suffix predicate must mention the carry.

The obstruction is one configuration: **carry `.cb` facing cell `n-3`**. Since `.cb` is entered
only from `ca` reading a `1`, this means `w[n-4] = 1` with carry `.ca` at `n-4` — the same
"`11` under `.ca`" shape as before, one cell further left. The kernel-checked
`pass_ends_true_of_ends_false_true` covers the carry-independent half of it: the penultimate `0`
of a `0, 1` ending makes the fatal early exit unreachable, so the output re-ends in `1`.

## 5. The reachable tail set

The tails are the words left after deleting the maximal `(0100)` head. They are far sparser than
any suffix-closed class.

**No fixed-length suffix language works.** Closing the observed suffix `001` under the transfer
table of §4 gives every suffix of that length: 8 of 8 at length 3, 16 of 16 at length 4, 32 of 32 at
length 5. The closures are complete and include halting suffixes (`000` in carry `ca`). So no
predicate of the form "last `k` cells lie in `T`" can be preserved for *any* `k`; the reachable set
is not a suffix language.

**The orbit is tiny at the right end.** Over 20 000 full-word steps the last four cells take only
the values

```
0001 (10215), 1001 (6905), 1101 (1703), 0101 (1177)
```

and among the 19 999 words of length ≥ 5 the last five take only

```
11001 (6697), 00001 (6261), 10001 (3953), 01101 (1703), 10101 (1177), 01001 (208)
```

all ending in `001`. The gap between these handfuls and the complete closures is exactly the carry
condition of §4.

**The left end is periodic with period 4.** Over 2000 consecutive tails the leading three cells are
a function of the step index alone:

| `k mod 4` | leading cells |
| :--- | :--- |
| 0 | `000` |
| 1 | `011` |
| 2 | `010` |
| 3 | `111` |

500 occurrences each, no exceptions. The right end carries the complementary law: every tail ends
in `0^a 1` with `a ≥ 2`, i.e. in `001`. The trailing-zero count takes the values 2, 3, 4, 5, 6, 7, 8
with frequencies 1182, 16, 343, 12, 355, 48, 44 over the same 2000-step run (minimum 2).

**The block count grows by one every four steps.** For the word sequence `w_0 = [1]`, the number of
transparent `(0100)` blocks in front of the tail is exactly `⌊k/4⌋`:

```
a_k = 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, ...   (k = 0..15)
```

so each four-step block of the dynamics adds exactly one transparent block, and the prefix phase
advances by one per step within the block. This is the cleanest statement of the orbit's shape found
so far.

**Formalisation.** The tail dynamics is now in the Lean file as `tailStrip` (delete the maximal
`(0100)^a` head), `tailStep` (sweep, prepend `false`, re-strip), `tailStart`, `phases` and
`prefixes` (collect the leading three cells of the first `n` tails). The theorem

```lean
theorem prefix_law_200 :
    prefixes 200 tailStart = (List.range 200).map expectedPrefix := by
  decide
```

is a **kernel-checked verification of the period-4 prefix law over the first 200 tails**, closed by
`decide` with no added axioms (`propext` only). The 40-step instance closes with no options at all;
100 and 200 need raised recursion-depth and heartbeat budgets, which the theorem sets explicitly and
comments, following the repository convention for kernel `decide` checks. It is a finite
verification, not a proof of the general statement:
the general law would need the position where the emitted string stops matching `1000`, which is the
block count `a_k` and therefore a global quantity.

**The block-count law in Lean.** `blocks` counts the leading `(0100)` blocks of a word;
`blocks_split` splits any word as `(0100)^{blocks w}` followed by `tailStrip w`,
`blocks_append_blocks` makes the count additive, and `blocks_tailStrip` shows a stripped tail
contributes no block. The general result is monotonicity:

```lean
theorem blocks_le_of_pass {w out : List Bool} (h : pass .ca w = some out) :
    blocks w ≤ blocks (false :: out)
```

so `a_{k+1} ≥ a_k` at every step: a sweep rewrites the whole `(0100)^a` head to `(1000)^a`, the next
word prepends `0`, and the head is intact again. The exact value is kernel-verified for the first
200 words:

```lean
theorem block_law_200 :
    blockSeq 200 [true] = (List.range 200).map (fun k => k / 4) := by
  decide
```

**The general equality is open, and the block law cannot yield the prefix law.** The count says how
many blocks precede the tail, never what the tail contains, so the two laws are logically
independent: no information about `a_k` determines the first cells of `t_k`. Both need the same
missing analysis. The obstruction is concrete: the number of blocks stripped in one step is the
position where the emitted string first departs from `1000`, a global property of the tail, so no
fixed-length prefix argument controls it.

**Prefix locality, and why it does not close the block count.** The sweep is local: its first `N`
output cells are determined by the first `N` input cells. That is now a theorem (`pass_take_eq`),
proved from a one-cell decomposition `pass_cons` (`stepCarry`, `stepEmit`):

```lean
theorem pass_take_eq (N : Nat) (q : Carry) (u v ou ov : List Bool)
    (hu : pass q u = some ou) (hv : pass q v = some ov) (hlen : N ≤ u.length)
    (hpre : u.take N = v.take N) : ou.take N = ov.take N
```

So a truncated tail *is* a valid stand-in for the cells it covers, and finite-window computations
are exact. What locality does not give is a small closed state. Measured eventual period of the
`L`-cell tail prefix on the orbit (1200 steps, window 800–1200):

| `L` | 4 | 8 | 12 | 16 | 20 | 24 | 32 |
| `P_L` | 4 | 16 | 32 | 64 | 128 | 256 | > 400 |

The period doubles with the window, so no fixed `L` carries a 4-cycle: the window state is locally
determined but its orbit period grows without bound. A finite-state closure at any fixed window
therefore yields only `P_L`-periodicity of the block increment, never the 4-periodicity that
`a_k = ⌊k/4⌋` needs. The state that does carry the 4-cycle is the deviation position, which is
unbounded. This closes off *front-anchored* finite-state proofs of the general block-count law;
anchoring at the deviation instead works (next paragraph).

**Anchoring at the deviation works.** The front window is the wrong state; the deviation is the
right one. With `pattern = 0 1 0 0`, define

    dev(w) = least i such that w[i] ≠ pattern[i mod 4]

(the end of the maximal block-consistent prefix). On the orbit, 1500 steps:

    dev(w_k) = k  for every k ≤ 1500,     and     blocks(w_k) = dev(w_k) // 4

so the block-count law `a_k = ⌊k/4⌋` is exactly the statement that *the deviation advances one cell
per step*. Since `dev(w_k) = k`, the residue `dev mod 4` runs `0,1,2,3` cyclically, and the
increment is the boundary crossing: `a_{k+1} − a_k = 1 ⟺ dev ≡ 3 (mod 4)` (checked on all 1500
steps).

The state `(dev mod 4, w[dev .. dev+8))` takes **16** values on the orbit and its transition is
**functional** — no state has two successors — so this is a genuine closed finite state, unlike the
front window whose orbit period doubles without bound. Four of the sixteen:

| phase | cells at the deviation | successor cells |
|---|---|---|
| 0 | `11100000` | `00100000` |
| 0 | `11100001` | `00100001` |
| 1 | `00100000` | `11000111` |
| 1 | `00100001` | `11000110` |

The last cell is carried through unchanged and the phase advances by one, so the residue cycle is
`0,1,2,3,0,1,2,3,…` with exactly one block increment per period.

*Local proof.* Write `w = (0100)^m ++ pattern[0..r) ++ (b :: rest)` with `b ≠ pattern[r]`, so
`dev w = 4m + r`. The carry is `ca` again after every complete block, hence
`pass ca w = (1000)^m ++ pass ca (pattern[0..r) ++ b :: rest)`, and the four residues force the
local input and output:

| `r` | cells from `dev` | output prefix | `dev` of successor |
|---|---|---|---|
| 0 | `1 …` | `0` | `4m+1` |
| 1 | `0 0 …` | `1 1` | `4m+2` |
| 2 | `0 1 1 …` | `1 0 1` | `4m+3` |
| 3 | `0 1 0 1 …` | `1 0 0 1` | `4m+4` |

In each row the successor word `0 :: pass ca w` agrees with the pattern through cell `4m+r` and
fails at `4m+r+1`, so `dev (0 :: pass ca w) = dev w + 1`. This is a four-case local induction with
no unbounded state; `dev (0 :: pass .ca w) = dev w + 1` is the statement still to be formalised.
*Status: kernel-checked.* The four-row case analysis above is now in the module: `devTail` (deviation
of a block-free tail), `dev = 4 * blocks + devTail ∘ tailStrip`, `devTail_step` (the four local
cases, plus the two vacuous short-tail cases), `dev_step`
(`pass .ca w = some out → dev w + 2 ≤ w.length → dev (false :: out) = dev w + 1`), and
`run_dev` (`run k = some w → dev w = k`, from `k = 1`), with `blocks_eq_dev_div
(`blocks w = dev w / 4`) giving **`block_law`**: `run k = some w → blocks w = k / 4`.

Two honest side conditions: `dev_step` needs two cells of runway past the deviation (a sweep that
reaches the blank boundary first moves the deviation by a different amount), and `block_law` is
conditional on the run producing a word at step `k` -- which is exactly the non-halting question,
still open. What is now unconditional is the *local* law: every sweep advances the deviation by one
cell. The earlier front-window obstruction is untouched by this -- it is a statement about the
wrong state.

**Consequence for the `0, 1` invariant.** These laws describe the orbit but do not chain it. The
prefix law constrains the *left* end and says nothing about the carry at cell `n-3`, which is what
the `0, 1` step needs; the trailing-zero law is the very assertion whose preservation fails for
arbitrary words. Chaining therefore requires a global argument tying the four-step phase to the
right-end carry, which is not available. #397 remains open.

## 6. What is still missing

An exclusion certificate only helps if the orbit stays inside the excluded class. It does not:

* **Wily Coyote.** Reachable tails end in `00` or `11` interchangeably, so the `22`-certificate
  covers only part of the orbit and never chains. Reachable tail lengths grow without bound:
  2 cells at the start, 22 at 100 sweeps, 30 at 1k, 41 at 10k, 49 at 50k, with no repeat in 50,000
  tail steps. No modular invariant exists (every residue of length, popcount, value and alternating
  sum mod 2..16 occurs) and every factor of length 2, 3 and 4 occurs somewhere in the orbit.
* **#397.** The `1`-certificate would apply at every step if trailing `1` were preserved, and it
  *is* preserved on the orbit (20,000 sweeps) — but not by a suffix argument: 364 words of length
  ≤ 14 that start with `2` and end in `1` have successors ending in `2`, the shortest being
  `[0,0,1,1] ↦ [0,1,1,0,0]`. The step from "ends in `1`" to "ends in `0, 1`" fails precisely at
  carry `cb` at cell `n-3` (see §4), and that condition is global, not local. Tail lengths grow to
  ~80 cells over 200,000 tail steps with no repeat.

Neither machine is proved non-halting anywhere in this repository; both remain open holdouts.

## 7. Wily Coyote: the same law at period 2

The deviation method transfers to the Wily pair (#531/#532) with the block `01` instead of `0100`.
Measured on the orbit (`wilyPass .s0`, `start = [false, false]`, 700 sweeps, no halt):

    dev2(w_k) = k + 1          for every k <= 700
    blocks2(w_k) = dev2(w_k)/2
    a_{k+1} - a_k = 1  <=>  dev2(w_k) odd      (increments 1,0,1,0,...)

Unlike #397, the step law needs **no runway condition**: the two local cases (`t = 1 :: rest` and
`t = 0 :: 0 :: rest`) both work at the word end, because mode `.s3` returns immediately with at most
two appended cells. So the deviation law is unconditional here:

    wilyPass .s0 w = some out  ->  dev2 (false :: out) = dev2 w + 1

Kernel-checked in `BusyBeaver/BB33/WilyCoyote.lean`: `blocks2`, `tailStrip2`, `devTail2`, `dev2`,
`blocks2_split`, `blocks2_append_blocks`, `tailStrip2_append_blocks`, `devTail2_step`, `dev2_step`,
`blocks2_eq_dev2_div`, `runW`, `runW_dev`, and

    blocks2_law : runW k = some w -> blocks2 w = (k + 1) / 2

Both Wily modules (#531 and #532) build against it. The 128 deviation states seen on the orbit are
not a small *window* state, but (as with #397) the law does not need one: the local argument covers
every word, so no closure hypothesis is left over. Halting for #531/#532 remains open for the usual
reason -- `blocks2_law` is conditional on `runW k = some w`.

## 8. Which holdouts have a deviation law: three of six

The six `BB(3,3)` holdouts split into two families, and the deviation law is exactly a
*sweep-transducer* phenomenon.

**Have it (kernel-checked).** `#397`, Wily Coyote `#531`, `#532`:

    #397 :  blocks w  = dev w / 4,    dev (w_{k+1}) = dev (w_k) + 1   (dev w_k = k)
    Wily :  blocks2 w = dev2 w / 2,   dev2 (w_{k+1}) = dev2 (w_k) + 1 (dev2 w_k = k+1)

In both, `next = W (false :: .) <$> pass w` with `pass` a finite-mode left-to-right pass, the word
grows by exactly one cell per sweep, and the matching prefix has a fixed period (`0100`: period 4;
`01`: period 2). That is what makes the deviation position a valid finite-state carrier, and hence
what makes the law possible.

**Do not have it.** Bigfoot `#829`, `#758`, `#153`. All three are regime-switching affine maps on
`Nat^k` that *multiply* a counter; none has a word, a pass function or a monotone "one block per
sweep", so none has a deviation position at all. Measured orbits (Python, exact integer arithmetic):

| machine | macro map | measurement |
| :-- | :-- | :-- |
| Bigfoot `#829` | `b' = 8*(b/6) + c + k`, `c' in {0,1,3}`, `a' = a + {-1,0,1}` | `b : 0 -> 3.7e59` in 400 steps, log-slope `0.288 = ln(4/3)` (log-residual `0.000`); `a <= 70`, not eventually affine |
| `#758` (start `A(0,1)`) | `a' = 3a` (growing regime) / `a - c - k`, `c' = 3(c/2) + k` | `a` reaches `2003` in 400 steps; second difference non-zero at 399/399 steps; 20000 steps without halting, final `A(35, 50367)` |
| `#153` (start `A(1,1)`, same `next`) | identical dynamics | `a` reaches `2003`; second difference non-zero at 399/399 steps |

So the counters are not eventually affine: Bigfoot's `b` is exactly exponential with ratio `4/3` per
macro step (the `8/6` carry), and in the `#758`/`#153` class a single macro step can jump `a` by 12
(`A(5,3) -> A(17,1)`) or by 36 (`A(17,15) -> A(53,1)`). No `blocks = dev / p` law can be stated for
these machines.

**What was added to the kernel**, in each of the three modules (`decide`, and `#print axioms` reports
*no axioms at all* for each): a `runMacro` iteration of `next` and three step facts exhibiting the
multiplicative jump:

    M_1RB2LC1RC_...  step_start : next start = some (A 1 3)
                     runMacro_three : runMacro 3 start = some (A 17 1)
                     counter_jump : next (A 5 3) = some (A 17 1)
    M_1RB0LB0RC_...  step_start : next start = some (A 5 1)
                     runMacro_two : runMacro 2 start = some (A 2 5)
                     counter_jump : next (A 17 15) = some (A 53 1)
    M_1RB2RA1LC_...  step_start : next start = some (A 3 0 1)
                     runMacro_ten : runMacro 10 start = some (A 4 65 1)
                     counter_jump : next (A 4 1 1) = some (A 3 5 0)

**Conclusion.** The deviation programme covers 3 of the 6 machines -- the whole sweep-transducer
class, i.e. 2 of the 4 dynamical classes. The other three are multiplicative Collatz cryptids
(base-6 carry; 2-counter contraction) where the deviation law has no analogue, so their holdout
status has to be attacked by other means. Halting for all six remains open.

## 9. Certified geometric growth of Bigfoot's b-counter

Kernel-checked in `BusyBeaver/BB33/M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean` (section "Certified
geometric growth of the `b`-counter"), axioms exactly `propext, Classical.choice, Quot.sound`,
no `sorry`:

    b_step      : next s = some s' -> 4 * (bOf s - 20) <= 3 * (bOf s' - 20)
    b_step_abs  : next s = some s' -> 4 * bOf s <= 3 * bOf s' + 20      (truncation-free)
    b_orbit     : runMacro n s0 = some s -> 4^n * (b0 - 20) <= 3^n * (b - 20)
    b_lower     : runMacro k (.A 4 65 1) = some s -> 45 * 4^k <= 3^k * (b - 20)

So `b' - 20 >= (4/3)(b - 20)`: the counter grows at least geometrically at the carry rate
`8/6 = 4/3`, matching the measured log-slope `ln(4/3)`. Instantiated at `A(4, 65, 1)` (reached
from `start = A(2,0,0)` in ten macro steps), every later state satisfies
`b >= 20 + 45 * (4/3)^k` -- certified, not just measured.

Sharpness: all six rules produce `b' = 8*(b/6) + c + k` with `k` in `{0,2,4,6,8}`, hence
`3 b' >= 24*(b/6) = 4*(6*(b/6)) >= 4b - 20` (using `b = 6*(b/6) + r`, `r <= 5`), with equality at
`r = 5`, `c = 0`. The constant `20` cannot be lowered across the whole rule table, and the rate
`4/3` is exact. This is a growth bound only: it does not decide halting (halting needs `a = 0` and
`b` congruent `1` mod 6, and `b` never decreases below `8*(b/6)`).

## 10. Attempted non-halting for the transducer holdouts: exact obstruction

Goal: `NeverHaltsFrom target (init [])` for #397/#531/#532, via `IsValidAcceleration.isHalt_iff`.
This reduces to totality of the accelerated orbit, `run k != none` for every `k`. Both sweeps
already have a kernel-proven *suffix* exclusion, so the only question is whether the orbit keeps
its safe suffix forever. It does not follow from anything in the modules, and the reason is sharp.

### The halt criterion, exactly

#397: the halt modes are `.cc` and `.ce`, and both are entered only by reading `false` (`2`).
Reading the final cell in any carry gives `ca -> cb`, `cb -> exit`, `cc -> cd`, `cd -> cf`,
`ce -> cd`, `cf -> ca` when that cell is `true` (`1`), and none of those is a halt mode. So a word
ending in `1` never halts: `pass_ne_none_of_ends_true`. Hence #397 never halts iff every orbit
word ends in `1`.

Wily: the halt mode is `.s1`, entered only from `.s0` on `2` and from `.s2` on `1`; a word ending
in `2 2` therefore never halts (`wilyPass_ne_none_of_ends_false_false`). For a word ending in
`1 1` the danger is the penultimate cell being read in `.s0` (`s0 --1--> s2 --1--> s1`, then
`s1, []` halts).

### Why the natural invariant cannot be proven

The safe suffix is not preserved by the pass, so no one-step closure exists:

    pass .ca [1,1]        = some [2,2]        -- word now ends in 2
    pass .ca [2,2,2]      = none              -- W(222) halts
    pass .ca [1,2,1]      = some [2,1,1]      -- even the 21-suffix class is not preserved
    wilyPass .s0 [2,2,2]  = some [1,1,1]
    wilyPass .s0 [2,1,1,1] = none             -- halts

The pass is a deterministic automaton whose state at the end of the word is a function of the
*entire* prefix, so a predicate on the last two cells cannot be inductive. Equivalently: the
deviation advances by one cell per sweep and is unbounded (`dev2 w_k = k+1`, `dev w_k = k`), so the
reached family of words has no finite quotient on which the halting condition could be decided.
The only available statement is "the tail map keeps the last cell `1` for every `k`", which is
exactly the open Collatz-type question for these machines.

### Measurements (`bbwork/orbit_probe.py`, 3000 sweeps)

    #397: no halt; last two cells = 21 at every k (first word is the single cell 1); tail 1..53
    WILY: no halt; last two cells 22 (2254 times) or 11 (746); tail 2..37

Both stripped tails grow without bound. Empirical survival to 3000 sweeps is consistent with
non-halting but proves nothing: the block and deviation laws were already conditional on the sweep
surviving, and the survival itself is the open part.

### Conclusion

No unconditional non-halting proof is reachable for any of the six holdouts by the deviation method:
#829, #758, #153 are multiplicative Collatz cryptids (open outright), and #397, #531, #532 reduce to
an unbounded automaton-state condition on the orbit. What is kernel-checked and unconditional is the
halting criterion (`pass ... = none` exactly at the bad suffix) plus the suffix exclusions; what is
missing is a proof that the orbit never produces a bad suffix, and that is not a finite check.

## 11. The halting criterion, formalised

Kernel-checked in `bbwork/cryptids_a6`; both modules build clean, `sorries = 0`, and every theorem
below has axioms within `propext, Classical.choice, Quot.sound`.

### #397 (`BusyBeaver/BB33/M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA.lean`)

    iterate_map_run_run      : (next^[n] (some start)).map unW = run n
    exists_halting_of_run_eq_none : run n = none -> ∃ k w, run k = some w ∧ pass .ca w = none
    isHalt_iff_exists_orbit_haltingWord :
        IsHalt target ↔ ∃ k w, run k = some w ∧ pass .ca w = none
    not_isHalt_iff_orbitSurvives : ¬ IsHalt target ↔ OrbitSurvives
    not_isHalt_of_forall_endsTrue : (∀ k w, run k = some w -> EndsTrue w) -> ¬ IsHalt target
    exists_not_endsTrue_of_isHalt :
        IsHalt target -> ∃ k w, run k = some w ∧ ¬ EndsTrue w

### Wily `#531`/`#532` (`BusyBeaver/BB33/WilyCoyote.lean`, generic over `StepSpec M`)

    iterate_map_runW_run      : (next^[n] (some start)).map unW = runW n
    exists_halting_of_runW_eq_none : runW n = none -> ∃ k w, runW k = some w ∧ wilyPass .s0 w = none
    isHalt_iff_exists_orbit_haltingWord : StepSpec M ->
        (IsHalt M ↔ ∃ k w, runW k = some w ∧ wilyPass .s0 w = none)
    not_isHalt_iff_wilySurvives : StepSpec M -> (¬ IsHalt M ↔ WilySurvives)
    not_isHalt_of_forall_endsFF : StepSpec M ->
        (∀ k w, runW k = some w -> EndsFF w) -> ¬ IsHalt M
    exists_not_endsFF_of_isHalt : StepSpec M -> IsHalt M ->
        ∃ k w, runW k = some w ∧ ¬ EndsFF w

So the machine halts iff some word on the accelerated orbit halts the sweep, and the residual
obligation is a *named predicate* (`OrbitSurvives`, `WilySurvives`) rather than an axiom: the
non-halting corollaries consume it as a hypothesis. The suffix forms are deliberately one-directional
-- `EndsTrue`/`EndsFF` everywhere on the orbit gives non-halting, and halting forces a reached word
that fails the test -- because the converse is false: `pass .ca [true, false] = some [false, true]`
is a word that fails the test and does not halt. That is exactly why the exact criterion is stated
at the sweep level, and why no fixed suffix can replace it.

### Per-machine instances (`#531`, `#532`)

Both machine modules now carry the criterion at their own `target`, with the residual hypothesis as a
local definition:

    #531 M_1RB2LA1LA_2LA0RA2RC_HHH0LC2RA,  #532 ..._HHH1RB2RA
    OrbitSurvives : Prop := WilySurvives
    isHalt_iff_exists_orbit_haltingWord :
        IsHalt target ↔ ∃ k w, runW k = some w ∧ wilyPass .s0 w = none
    not_isHalt_iff_orbitSurvives : ¬ IsHalt target ↔ OrbitSurvives
    not_isHalt_of_orbitSurvives  : OrbitSurvives → ¬ IsHalt target
    not_isHalt_of_forall_endsFF  : (∀ k w, runW k = some w → EndsFF w) → ¬ IsHalt target
    exists_not_endsFF_of_isHalt  : IsHalt target → ∃ k w, runW k = some w ∧ ¬ EndsFF w

Each is a one-line application of the generic `WilyCoyote` theorem to that module's private
`stepSpec`, so no proof is duplicated and the two machines provably share the residual obligation.

## 12. Three invariants that do not close (measured 2026-11-09)

Attempts to turn the surviving orbit into an inductive invariant, with the numbers that killed each.

### 12.1 Eventual periodicity of the word tails: false for both transducers

State would have to be `(tail, phase)` with `tail` the suffix past the deviation position. Measured,
400 sweeps, phase modulus up to 60:

    #397 : tailLen 1 -> 40 ;  no repeat of (tail, blocks mod M) for M = 4, 8, 16, 32, 64
    WILY : tailLen 2 -> 25 ;  no repeat of (tail, blocks2 mod M) for M = 2, 4, 6, 8, 12, 24, 48, 60

So the deviation advances without ever re-entering a finite state; a cycle argument cannot prove
survival. This is the measurement behind the phrase "the tail map keeps the last cell `1` for
every `k`" being the whole question.

### 12.2 Bigfoot's `a`-walk: `a = 0` never occurs, but no modular invariant sees why

300 000 macro steps from `A(2,0,0)`:

    a = 0                      never (count 0)
    a = 2                      exactly k = 0 (b = 0) and k = 8 (b = 36)
    a = 3 and r = 1            exactly once, k = 7 (b = 25, c = 0) -> A(2,36,0)
    last k with a <= 2         8
    min a on k >= 9            3
    max a                       49811

`a` is decremented only by the rule `r = 1` (and only from `a > 0`); every other rule either raises
`a` (r in {0,3}) or leaves it. So `a >= 3` for all `k >= 9` would exclude the halt branch
`a = 0, r = 1`, and the measured orbit satisfies it. It is not provable from the rule table alone:
entering `a = 2` requires an `a = 3, r = 1` state, and whether the resulting
`b' = 8*(b/6) + c + 4` is `0 mod 6` depends on `b mod 18`, not on `b mod 6`.

A detailed proof attempt along these lines, including the legal counterexample `A(4,1,3) -> A(3,7,0)` that kills the one-step induction, is in `bigfoot_a_ge_3.md`.

### 12.3 Why no finite modulus closes

`b' = 8*(b/6) + s`, with `s` ranging over a finite set. To know `b' mod 3^k` one needs
`b/6 mod 3^k`, hence `b mod 2*3^(k+1)`: the 3-adic precision required grows by a factor 3 every
macro step, because `6` is not invertible mod 3. No modulus `M` makes `(a, b mod M, c)` closed, so the
halting question is not a finite congruence condition. A saturating abstraction of `a` likewise
cannot exclude `a = 0`: decrements are guarded only by `r = 1`, so the abstract transformer always
admits a spurious descending path. This is the precise sense in which Bigfoot, `#758` and `#153` are
multiplicative Collatz cryptids rather than machines with a hidden finite-state invariant.

### 12.4 The log-comparison potential: `b < 6^a` is false

A potential-function proof would compare the two counters: halting needs `a = 0` and
`b = 1 mod 6` (so `b >= 1`), hence the single invariant `b < 6^a` would already exclude it. Measured
on 300 000 macro steps (from `k = 9`, where `a = 3`):

    max log2(b / 6^a) =  81.517  at k = 1238
    min log2(b / 6^a) = -4274.958 at k = 299875
    violations of b < 6^a: 3994

So the ratio is not bounded above by 1; it climbs to `2^81.5` early and decays only later. No constant
slack repairs this: at `k = 8` one has `b = 36 = 6^2`, so any invariant `b < K * 6^a` needs `K > 1`,
and the halt state `(a, b) = (0, 1)` then satisfies it. A comparison potential must therefore be
strictly `b < 6^a` (false) or carry a non-constant correction, which is the same difficulty as before.

The same run shows why `a` cannot be treated as bounded: `a` reaches 49 811 by `k = 300 000` and
tracks `log_6 b` (16 601 against `log_6 b ~= 16 055` at `k = 100 000`), so `a` grows without bound
while its minimum on `k >= 9` is 3. The empirical statement "`a >= 3` for every `k >= 9`" is exactly
what a proof of Bigfoot's non-halting would need, and it is not a congruence or a one-step potential:
`a` jumps down by 1 on `r = 1` regardless of its size, and the guard for that rule is `b mod 6` alone.

### 12.5 Status

Nothing here is a proof of non-halting for any of the six. The halt criteria of §11 remain the only
unconditional new facts: they reduce `IsHalt` to one named survival predicate per machine. Solving a
holdout requires proving that predicate, and §12.1-12.4 close the four natural finite routes.
