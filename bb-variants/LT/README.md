# Ladder Tag (LT)

**Ladder Tag** is a variant of the [Absorbing Tag System](../ATS/README.md)
(which is itself a member of the Tiny Tag / cyclic-tag family).  It keeps the
ATS tape language, absorption phase, length convention and halting rule, and
changes exactly two head rules — both chosen so that **short tapes run much
longer**:

| rule | ATS | Ladder Tag |
|---|---|---|
| head `1` | appends copies of the next **two** tokens | appends copies of the next **three** tokens |
| zero-rule | pops the tail token | pops the tail token and appends `fn(0)` — a **cinder** |

Everything else is ATS: primitives `0`/`1` and functions `fn(alpha)` with
`alpha in {0,1}+`; absorption folds an internal function's right neighbour into
it, `fn(alpha) -> fn(d alpha)`, once per step, left to right; `length(fn(alpha))
= len(alpha)` with the wrapper free; a composite head fires the one-rule and
the zero-rule in the ATS order (`c0 = 0` one only, `c1 > c0` one then zero,
`c0 > c1` zero then one, `c1 = c0` decided by `alpha[0]`); the machine halts
when the tape becomes empty.

## Why these two changes

The step count of a halting run is bounded by the number of tokens the run ever
creates, because every step pops exactly one head token.  ATS therefore spends
its life in short growth/shed cycles, and a length-`n` tape tops out around
`2^n` steps.  LT lengthens both halves of the cycle:

* the wider `1` copy raises the growth multiplier per fuel token (three tokens
  per step instead of two);
* the cinder makes each zero-rule firing cost *two* steps instead of one: the
  token it spends is replaced by `fn(0)`, which cannot grow anything, but still
  has to be carried all the way to the head and popped.

The cinder half is what makes it work.  An earlier version paid the zero-rule
back in real fuel (`fn(1)`), and that is worse than ATS at low lengths: tapes
explode without halting (nothing below `n = 5` halted above 25 steps) and the
exhaustive search drowns in token-cap hits.  Handing back a token that costs a
step but cannot reproduce keeps the growth/shed balance while stretching the
shed.

## Transposition cache (two tapes are equivalent when one reaches a state the other reached)

A tape's runtime is a property of the state it reaches: if candidate A reaches
a state S that candidate B already visited, A's runtime is `steps(A -> S)` plus
R(S).  The searcher therefore keeps a global table of `state -> outcome` and
probes it every step, for tapes of at most 64 tokens (that is where candidates
converge; long tapes are rarely revisited).  Keys are 128-bit state hashes; on
a hit the run short-circuits, on a miss the states visited are recorded and
back-filled with the outcome once the run terminates.

Measured on the LT sweeps (`--max-steps 100000 --max-tokens 2000`):

| n | probes | hits | hit rate | before cache | after cache |
|---:|---:|---:|---:|---:|---:|
| 4 | 3,349 | 454 | 13.6% | 0.01 s | 0.01 s |
| 5 | 15,278 | 2,585 | 16.9% | 0.28 s | 0.05 s |
| 6 | 69,216 | 14,125 | 20.4% | 1.98 s | 0.20 s |
| 7 | 312,899 | 75,703 | 24.2% | 13.76 s | 0.70 s |
| 8 | 1,415,196 | 401,419 | 28.4% | - (cap too shallow) | 18.5 s |
| 9 | 8,046,692 | 2,115,195 | 26.3% | - | 33.9 s |

All champions below are unchanged by the cache, so the speedup is free: it buys
deeper caps, which is what raised the length-8 and length-9 records.  The same
cache was added to `../ATS/ats_search.c`; ATS's champions there are unchanged
(253 / 307 / 598) while the length-9 sweep drops from ~2.5 min to 11 s at the
same caps, with hit rates of 37-42%.

## Champions

Best halting tape per LT length, exhaustive over all tapes of that length.
Values for lengths 2-7 are re-verified in the Python reference `lt.py`; the two
deep-cache records (8 and 9) come from the C searcher and are reproducible from
the printed tape.

| length | ATS best | LT best | tape | LT speedup |
|---:|---:|---:|---|---:|
| 1 | 1 | 1 | `[0]` | 1.0x |
| 2 | 3 | 4 | `[fn(10)]` | 1.3x |
| 3 | 11 | 22 | `[1, 1, fn(0)]` | 2.0x |
| 4 | 21 | **243** | `[fn(10), 1, 1]` | 11.6x |
| 5 | 48 | **583** | `[1, 0, fn(1), fn(0), 1]` | 12.1x |
| 6 | 108 | **3188** | `[1, 0, fn(1), fn(1), fn(0), 1]` | 29.5x |
| 7 | 253 | **7644** | `[1, 0, fn(1), fn(1), fn(0), 1, 1]` | 30.2x |
| 8 | 307 | **25198** | `[fn(10), 1, 1, 1, 1, 0, 0]` | 82.1x |
| 9 | 598 | **110175** | `[fn(10), 1, 1, 1, 1, 0, 0, fn(1)]` | 184.2x |

Sweep settings: lengths 1-7 at `--max-steps 2000000 --max-tokens 20000`,
lengths 8-9 at the same caps (18.5 s and 66 s).  The gain arrives where it was
wanted: from length 4 upward LT is an order of magnitude past ATS, and by
length 9 it is ~184x.

Caveats, stated plainly:

* The sweeps are exhaustive over the tapes of each length (4, 20, 104, 544,
  2848, 14912, 78080, 408832 and 2140672 candidates at lengths 1-9, matching
  ATS's candidate counts).  Runs that hit a cap are unresolved, so every entry
  is a **lower bound**: 892,571 length-9 tapes were still running at the
  2,000,000-step cap and 14,630 were over the 20,000-token cap.
* The cinder never creates a zero from a zero-free tape (it is only appended
  when the head's `alpha` already holds a `0`), so ATS's zero-free decider
  carries over unchanged.
* Length 10 was not swept: at LT's growth rate it is roughly ten times the
  length-9 run, i.e. ~11 minutes single-threaded per shard.

## Files

* `lt.py` — readable reference simulator and searcher (same CLI shape as
  `../ATS/ats.py`); every low-length champion was checked against it.
* `lt_search.c` / `lt_search.exe` — exhaustive C searcher with the
  transposition cache and `--n`, `--max-steps`, `--max-tokens`, `--shard`,
  `--shards`, `--dump-limit`.
* `tune.py` — the tuning scan that rejected the fuel-payback rule.

## Reproduce

```powershell
cd bbwork/bb-variants/LT

python lt.py sim "[1, 0, fn(1), fn(1), fn(0), 1]" --max-steps 10000   # 3188
python lt.py search --max-n 6

gcc -O3 -std=c11 -o lt_search.exe lt_search.c
./lt_search.exe --n 7 --max-steps 2000000 --max-tokens 20000           # 7644
./lt_search.exe --n 9 --max-steps 2000000 --max-tokens 20000           # 110175
```

## Status

LT is an informal variant in the same sense as ATS: no termination theorem is
claimed, the published values are exhaustive-search lower bounds with explicit
caps, and no claim is made about the model's computational power.
