# The non-halting proof, in words

Machine: `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA`, blank tape, state `A`.
Final theorem: `SOC.Completion.neverHalts : SOC.NeverHalts`.

Throughout, a *block* is a two-cell group on the right of the head and is named
by its first cell: the labels `4`, `0`, `2`, `1` stand for the tape blocks `44`,
`04`, `24`, `14`.  The left counter is a list of digits
`LD = d0 | d1 | dB | dA`, i.e. `02`, `22` (radix 2) and `03`, `23` (radix 3/2),
least significant digit first, and `gap w` is the number of increments the
counter `w` still admits before it overflows (`RequestProject/Counter.lean`).

## 1. From the tape to a scalar recursion

The machine runs in *revolutions*.  Starting from the configuration
`phaseStart L = .22 B> 44 (blocks of L) 1.` one revolution consists of

* a **reset phase**: the blocks of `L` are absorbed into the left counter,
  one counter position per block (`resetF`);
* the **junction**: the terminating `1` is read, the lowest binary digit is spent
  and two radix-3/2 digits are pushed (`junctionF`);
* a **normal phase**: the counter is spent one increment at a time, each cycle
  pushing a digit `03`, until it overflows (`normalF`);
* the **overflow**, which releases the counter's digits as the blocks of the next
  reset phase (`ovfF`).

`revolutionF L` performs all of this on block sequences and `revolutionF_spec`
proves that a successful computation is a genuine positive-length run of the
Turing machine; `revIter n` iterates it from `firstBlocks`, the sequence of the
first overflow (reached after 306 steps, `run_init_306`).  Hence
(`neverHalts_of_revIter`): **if `revIter n` succeeds for every `n`, the machine
never halts.** Everything below is about block sequences only.

## 2. The exact reset maps

`xnext g b` (`CompletionArithmetic.lean`) is the **exact** gap after absorbing a
block `b` into a counter with binary lowest digit and gap `g`:

```
b = 4 (44):  2g + 1
b = 0 (04):  2g
b = 2 (24):  2g − 1          (affordable only if g ≥ 1)
b = 1 (14):  2⌊(g − 8)/3⌋+1  (affordable only if g ≥ 8)
```

`XSafe g L` says every block of `L` is affordable along the way, `xfold g L` is
the final gap, and `reset_exact` proves that these scalars really describe
`resetF`: a safe word can be absorbed and the resulting counter again has a
binary lowest digit and exactly the gap `xfold g L`.

`inv b T` is the least starting gap from which block `b` is affordable and leaves
at least `T`; `inv_sound` and `inv_twice_bound` (`2 inv b T ≤ 3T + 16`) are the
only facts about it that the proof needs.

## 3. Saturation: what the overflow will release

For a counter `w` define the tape-order word `sat w` (`CompletionSaturation.lean`):
a radix-2 digit contributes the label `4`, a digit `03` above a tail of gap `h`
contributes `beta h`, and a digit `23` contributes `alpha h`, where

| `h mod 3` | `beta h` | `alpha h` |
| --- | --- | --- |
| 0 | 0 | 2 |
| 1 | 2 | 1 |
| 2 | 1 | 0 |

The key new fact is `sat_preserved`: **a successful increment does not change
`sat`.**  (It reduces to `beta (h+1) = alpha h` and `alpha (h+2) = beta h`, which
is the table above; `03` emits one carry and becomes `23`, `23` emits two and
becomes `03`.)  Consequently `ovf_sat`: at gap zero the overflow releases exactly
`sat w`.  One does not have to follow the timing of the final sweep.

## 4. The word a normal phase creates is a function of the gap

With `descend g = ⌊(2g − 1)/3⌋` and

```
freshDigit g = 1 if g ≡ 0,  0 if g ≡ 1,  2 if g ≡ 2   (mod 3)
fresh 0 = [],  fresh g = freshDigit g :: fresh (descend g)
```

`normal_exact` proves `normalF w acc = some (sat w ++ fresh (gap w) ++ acc)`.
Since `descend g = 0` forces `g = 1` and `freshDigit 1 = 0`, every nonempty
`fresh g` ends with the block `04` (`fresh_ends_zero`) — this is where the parity
of the next reset gap comes from.

Similarly `junction_exact` computes the junction exactly: with
`junctionTop g = ⌊(g − 8)/3⌋` and `junctionGap g = ⌊2 junctionTop g/3⌋`, the
junction leaves a counter of gap `junctionGap g` and appends the two labels
`junctionFirst g`, `alpha (junctionTop g)` to the saturation word.

Putting the three together (`revolution_suffix`): one revolution of a sequence
`L` whose reset produces the counter `w` releases

```
L' = S ++ suffix (gap w),
suffix g = junctionFirst g :: alpha (junctionTop g) :: fresh (junctionGap g),
```

where the *inherited* part `S` has a block `44` exactly at the positions where
`L` has a block different from `14` (this is the radix-pattern theorem
`resetF_pat` / `patF_true` of `Shape.lean`).

## 5. The inherited part is free

`inherited_exact`: if `L` is safely resettable from `g`, `G ≥ g`, and `S` has a
`44` wherever `L` is not `14`, then `S` is safely resettable from `G` and
`xfold G S ≥ xfold g L`.  At a position where `L` is not `14` the new sequence has
the best possible block `44`; at a position where `L` has a `14` the old gap was
at least 8, so the new (larger) gap can afford whatever block stands there, and
every block is at least as good as `14`.  Monotonicity (`xnext_mono`) propagates
the comparison.  No density or counting argument is involved.

## 6. The fresh part is safe: `62`, even

Let `need g` be the starting gap required for `fresh g` to be read safely and to
end at gap at least 62, built from `inv`; `need_safe` is its correctness.

* `need_bound`: `need g + 30 ≤ 2g` for all `g ≥ 133`.  Strong induction on `g`;
  for `g ≥ 200` the inductive hypothesis applies to `descend g` and the three
  residue classes are elementary, and the 67 values `133 ≤ g < 200` are the finite
  certificate `normal_small_certificate`.
* `suffix_need_bound`: `suffixNeed g ≤ g` for even `g ≥ 62`, where `suffixNeed` is
  the requirement of the whole junction word `suffix g`.  For `g ≥ 608` this
  follows from `need_bound`, `2 inv b T ≤ 3T + 16` applied twice, and
  `9 junctionGap g ≤ 2g`; the 273 even values `62 ≤ g < 608` are the finite
  certificate `junction_small_certificate`.  (The bound is tight at `g = 76`,
  which is why the constant is 62 and not 64.)
* `suffix_safe`: for even `g ≥ 62` and any `G ≥ g`, the word `suffix g` is safely
  resettable from `G`, finishes at gap at least 62, and that gap is **even** —
  because the last block of `suffix g` is the `04` of §4.

## 7. The invariant and the seed

```lean
def Invariant (L : List Sym) : Prop :=
  XSafe 1 L ∧ 62 ≤ xfold 1 L ∧ xfold 1 L % 2 = 0
```

`invariant_step`: a sequence with this property has a successor.  Its reset
succeeds with exact gap `g = xfold 1 L ≥ 62 ≥ 9`, so the junction succeeds and the
normal phase always does; by §4 the next sequence is `S ++ suffix g`, by §5 the
inherited part `S` is safe and rebuilds a gap `≥ g`, and by §6 the suffix is then
safe and ends even and `≥ 62`.

The machine enters the invariant at its **second** released sequence

```
seed = [4,4,4,4,4,4,4,0,2,0,0,0,2,1,2,1,0],   xfold 1 seed = 28958
```

(the first one, `[4,4,4,0,4,0,2]`, has the odd gap 243, so it is stepped over by
the finite check `seed_reached : revIter 1 = some seed`).  Hence
`all_later_iterations`: every `revIter (n+1)` succeeds, and with `revIter 0 =
some firstBlocks` and `neverHalts_of_revIter` the machine never halts.
