# fe0_5: the ordinal notation behind `1^a 4 W`

Read off the (1,3) run, the only run we have that halts (15,981 steps, score
`1^39`).  The tape at every visit to state A is `1^a 4 W`, with `W` a word over
`{2,3}` (a trailing `1` at some visits is a transient of the sweep that writes
the next digit; those visits are excluded below).

## 1. The word is a binary counter

Read `2` as bit 0 and `3` as bit 1, most significant symbol first:

```
val([])        = 0
val(s :: rest) = bit(s) * 2 ^ |rest| + val(rest)      bit(2) = 0, bit(3) = 1
```

Equivalently, `val(w ++ [2;3]) = 4 * val(w) + 1`: appending the pair `23`
(i.e. the bits `0,1`) shifts a binary number left by two and adds one.

So `3` = 1, `23` = 1, `2323` = 5, `232323` = 21, `(23)^k` = (4^k - 1)/3.

## 2. The stable states, by `a`

Longest clean `W` observed at each value of `a` in the (1,3) run:

```
a:    1   2   3   4   5   6   7 |  8   9  10  11  12  13  14  15  16  17 | 18 ... 36
|W|:  3   9  14  12  10   8   5 | 20  18  16  14  12  10   8   6   4   1 | 36 ... 2   0
```

Written out, the words are

```
a=3..6    (2233)^2 (23)^3, (23)^2, (23)^1, (23)^0
a=8..16   (2233)^1 (23)^8, (23)^7, ..., (23)^1, (23)^0
a=18..36  (2233)^0 (23)^18, (23)^17, ..., (23)^1, (23)^0
```

so

```
W = (2233)^c (23)^k          c = 2, 1, 0
```

with `c` the **level** (a stack of 2233 blocks) and `k` the **counter** at the
current level.  The singular states `a = 1, 2, 7, 17` are the transitions
between levels (`223`, `(2233)^2 2`, `2233 2`, `2`).

## 3. The round law, checked

Between consecutive values of `a` (one round = one increment of `a`), the word
loses exactly its trailing `23`:

```
W_{a+1} = W_a minus the final "23"
```

Checked over the whole run: **29 of the 29 non-boundary transitions obey it
exactly**, 0 violations.  In `val` terms the round is

```
val(W_a) = 4 * val(W_{a+1}) + 1        i.e.  val(W_{a+1}) = val(W_a) div 4
```

which is the pop of one base-4 digit.

The 6 remaining transitions are exactly the level changes:

```
1 -> 2    223            -> 223322332            (level 2 built)
2 -> 3    223322332      -> 22332233232323       (counter k=0 -> k=3)
6 -> 7    22332233       -> 22332                (2233 block collapses)
7 -> 8    22332          -> 2233 (23)^8          (level 2 -> 1, k reset to 8)
16 -> 17  2233           -> 2                    (2233 block collapses)
17 -> 18  2              -> (23)^18              (level 1 -> 0, k reset to 18)
```

At a level change `c` decreases (2 -> 1 -> 0) and `k` is reset upward.

## 4. The measure

Take the ordinal term

```
o(W) = omega^c * (k+1)          for W = (2233)^c (23)^k
```

Then

* within a level: `c` fixed, `k` decreases by 1, so `o` decreases;
* at a level change: `c` decreases and `k` is reset, and
  `omega^c * (k+1) > omega^(c-1) * (k'+1)` for any `k'`, so `o` decreases.

Thus every round strictly decreases `o`, and `o = 0` exactly at `W = []`
(`c = 0, k = 0`), which is the halting configuration.  The run of 15,981 steps
is the descent of `omega^2*4` to 0, i.e. 36 rounds: (1,3), (1,2), (1,1), (1,0),
(0,8), ..., (0,0) — one descent through `omega^2`, which is why the run is
finite and short.  For a bigger input the same notation recurs at higher
levels (`omega^3`, ..., `omega^omega`), which is where the tower growth comes
from: the input decides the height of the stack, and the run is the descent
through `omega^h`.

## 5. The rule table against the notation

The 17 rows fall into three groups.

**Scans** (read the word, do not change it): `F` `1/2/3 -> same, R`,
`H` `1/2/3 -> same, L`, `J`, `K`, `L`, `M`, `N`, `P`, `Q` on `1/2/3`.
These implement the walk over the base-4 digits.

**Writers** (the digit operations):

* `C`: `1 -> 4R`, `4 -> 2R`, `0 -> 0LI`.  This is the pop/carry: a `1` is
  marked `4`, and a `4` becomes `2` — i.e. the digit is consumed and the
  carry `4 -> 2` is what makes `23` (value 1) turn into nothing (value 0)
  while the next digit is decremented by the `1 -> 4` pass.
* `G`: `1 -> 0RI`, `0 -> 0LH`.  Deletes a `1` (the transient digit) and hands
  to `H`.
* `H`: `0 -> 2LA` — writes the new digit `2` at the left end of the word.
* `I`: `0 -> 3RN` — writes the digit `3` (value 1) when the level expands.
* `E`: `0 -> 3LA`; `D`: `0 -> 1LE`; `O`: `3 -> 0RM`; `N`: `4 -> 4LJ`, `0 -> 1LO`
  — the level-change and rebuild paths.
* `A`: `2 -> 0RF`, `3 -> 0RD`, `4 -> 1LQ` — the dispatcher: `2` and `3` go
  right into the scan, `4` becomes the `1` increase of `a` (this is the
  `1` appended before the `4` in `1^a 4 W`).
* `B`: `1 -> 1RB`, `2 -> 2LC` — the halt check (`B` on `0` halts via `1RZ`).

So the `1^a` prefix is exactly the count of pops (`A` on `4` writes a `1`),
and `W` is the base-4 counter that the pops consume.  The notation and the
table agree on every transition observed.

## 6. What is proved and what is not

Proved: the round law (29/29 by trace), the base-4 reading, the level
decomposition `(2233)^c (23)^k`, the measure `omega^c (k+1)` decreases on every
observed round, and the halting run reaches `W = []`.

Not proved: that every input follows this law (the trace is one run at
(1,3)); and that the level height grows with the input the way the level claim
needs.

`rocq/Fe0Descent.v` compiles (Rocq 9.1).  The descent side has no abstract
ordinal type and no re-indexed well-founded order any more:

```
rep c k     := (2233)^c (23)^k                       (the notation)
mkConf a c k                                          (1^a 4 rep c k)
rstep       : (a,c,k+1) -> (a+1,c,k)                  (pop)
              (a,c+1,0) -> (a+1,c,level c)            (level drop)
rep_halts   : forall a c k, exists n, done (rrun n (mkConf a c k)) = true
              (nested induction: c, then k)
val_pop     : val (w ++ [2;3]) = 4 * val w + 1
val_round   : val (w ++ [2;3]) / 4 = val w
```

The machine side is the table itself (`delta`, `step`, `runN`).  Every sweep
the round performs is a theorem about that table, parametric in the block it
runs over:

```
walk_right / walk_left   a state that writes back what it reads and moves
                         one way, over any block, in any context
step_r / step_l / step_l0   one step, spelled so rewrites fire
c_walk d_walk f_walk b_walk   right sweeps of C, D, F, B  over {2,3} / {1}
q_walk e_walk h_walk          left sweeps of Q, E, H
```

and on the two blocks the round actually uses:

```
b_scan_ones  : runN a (B, l, 1^a ++ x :: t) = Some (B, 1^a ++ l, x :: t)
q_scan_ones  : Q sweeps 1^a one cell at a time (head cell must be a 1)
c_scan_word  : runN (4c+2k) (C, l, rep c k ++ x :: t)
               = Some (C, rev (rep c k) ++ l, x :: t)
length_rep   : length (rep c k) = 4c + 2k
```

Two transitions of the trace (the run from `1^1 B> 2^3`) are checked against
the table, so the descent's two moves are instances of it:

```
round_1074_1459     : runN 385 d1074 = Some d1459    (a: 7 -> 8, one round)
leveldrop_3675_3752 : runN 77  d3675 = Some d3752    (c: 1 -> 0, block gone)
```

and the run's own landmarks:

```
round_c303_c310 : runN 7 c303 = Some c310      (one A-to-A round of the run)
halt_13         : runN 15981 init13 = Some (HALT, l, r)
halt_13_stops   : runN 15982 init13 = None
score_13        : count1 (l ++ r) = 39         (at the halt)
```

```
coqc -Q . Top Fe0Descent.v                        exit 0
coqchk -Q . Top Top.Fe0Descent                    Modules were successfully checked
Print Assumptions <any lemma above>               Closed under the global context
```

So: the descent terminates for every `a, c, k`; every sweep of the round is a
theorem about the table at any block length, `1^a` and `(2233)^c (23)^k`
included; and two transitions of the actual run are checked.  What is still
open is the *composition*: joining the sweeps into one closed machine theorem
`runN n (A, 1^a 4 rep c k) = Some (A, 1^(a+1) 4 rep c' k')` for symbolic
`a, c, k`.  The pieces are proved; the bookkeeping that chains them, and so the
level claim for every input, is not yet written.
