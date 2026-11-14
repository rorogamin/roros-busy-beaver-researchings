# A Turing machine for the greedy U-a-U-free sequence

## Object being generated

The alphabet is `{0,1,2,...}`.  A finite word is legal if it has no factor

```
U a U
```

where `a` is one symbol and `U` is a nonempty block of symbols.  Examples of
forbidden factors are `1115111` (`U=111`, `a=5`), `34234` (`U=34`, `a=2`) and
`000` (`U=0`, `a=0`).  At every position choose the smallest symbol that keeps
the word legal.

The first occurrences are

```
0 at 1
1 at 3
2 at 7
3 at 10
4 at 1355
```

and the first 200,000 terms have exactly

```
0: 81475
1: 72578
2: 40434
3: 5463
4: 50
```

with no 5.  `ua_sequence.cpp` reproduces those counts, and
`ua_sequence.py` is a readable reference implementation with a brute-force
cross-check.

## Reversed form used by the machine

Let `S` be the word so far, `R = reverse(S)`, and let `Z[i]` be the length of
the longest common prefix of `R` and `R[i:]`.

When the next symbol is `c`, a new forbidden factor must use the new symbol,
and reversing the whole word turns it into a factor at the **front** of
`c + R`.  Writing the first `U` as length `L`, the condition is exactly

```
R[L] == c  and  Z[L+1] >= L-1        (L >= 1)
```

(the empty-suffix case at the very start is handled separately).  Thus:

```
forbidden = { R[L] : L >= 1 and Z[L+1] >= L-1 }
next      = mex(forbidden)
```

If `mex` is 5, the machine halts.  Otherwise prepend it to `R` and update

```
Z_new[0]   = n+1
Z_new[i]   = 1 + Z_old[i]   if R_old[i-1] == c
             0              otherwise          (1 <= i <= n)
```

This is the recurrence implemented by `ua_sequence.py` and
`ua_sequence.cpp`.

## Two-tape machine

A direct construction uses **two tapes**.  It is a standard TM with a finite
control and unbounded tapes; the state and symbol counts are allowed to be
large.  It is not a 7-state BB machine.

### Tape layout

* **Tape 1** holds `# R[0] R[1] ... R[n-1] #`, one cell per term.  Symbols
  are the terms `0,1,2,3,4`; `5` is used only as the halt symbol.  `#` is an
  end marker.
* **Tape 2** is the work tape.  It contains the Z-values and the scratch
  fields in two tracks, separated by a marker `|`:

  ```
  # (Z[0], scratch) (Z[1], scratch) ... (Z[n-1], scratch) | scratch #
  ```

  A cell is a pair of symbols; `Z[i]` is stored in unary as `1^{Z[i]} 0`.
  The `|` region is scratch space for comparing unary counters and for the
  five forbidden-symbol flags.  One head serves the whole work tape; moving
  it from the Z track to the scratch track is an ordinary tape move.

The finite control has these macro-states (each expands to finitely many
ordinary TM states; all loops terminate because they walk to a tape marker):

1. **SCAN-L.** Move the R head to `L=1,2,...` while `2L+1 <= n+1`.
   The current `L` is kept as a unary counter in the scratch region of tape 2
   (the finite control never stores an unbounded integer).  At each `L`, copy
   `Z[L+1]` and the counter `L-1` to the scratch region and compare their
   unary lengths.  If `Z[L+1] >= L-1`, read `R[L]` and set the corresponding
   one of five flags in the control.
2. **CHOOSE.** The first unset flag is the least symbol `c` not forbidden.
   If all five flags are set, write `5` and enter the halting state.
3. **PREPEND.** Shift the R tape one cell right (or use the empty cell at
   the left end marker), write `c` at the new `R[0]`, and increment `n`.
4. **UPDATE-Z.** Walk the old R and Z tapes together.  For each `i`, if the
   old `R[i-1]` is `c`, write `Z_old[i]+1` in unary at the new `Z[i]`;
   otherwise write zero.  Set `Z[0] = n+1`.
5. **LOOP.** Clear the flags and go to SCAN-L.

Every tape operation above is a fixed finite-state scan: moving to an end
marker, copying a unary block, comparing two unary blocks, or shifting a
block by one cell.  Therefore the description is a finite transition table
once the macros are expanded; no arithmetic unit or unbounded control is
hidden in the states.  The machine starts with empty tapes and runs forever
if 5 never appears.  It halts at the first position where the forbidden set
contains all of `0,1,2,3,4`.

The machine is intentionally a **simulator**, so it has a large finite
control and two tapes.  It is not a 7-state, 2-symbol BB(7) candidate.

## One-tape machine

The two-tape machine can be converted to a **one-tape machine** without
changing its halting behaviour.  Since state and symbol counts are allowed to
be large, use the standard one-tape encoding of a multi-tape machine rather
than trying to compress the algorithm.

### Encoding

Let `Gamma1` be the tape-1 alphabet from above and `Gamma2` the tape-2
alphabet.  The one-tape alphabet is

```
Gamma = {@} union (Gamma1 x Gamma2 x {0,1} x {0,1})
```

There is one home cell `@` at index 0.  Data cells start at index 1; cell `i`
stores `(a_i, b_i, h1_i, h2_i)`: the old tape-1 symbol, the old tape-2 symbol,
and one flag for each simulated head.  A flag is `1` exactly in the cell where
that head sits.  The `#` end markers of the two simulated tapes are ordinary
symbols in `Gamma1` and `Gamma2` and occupy data cells; the home cell `@` is
only the one-tape scanner's fixed starting point.  Both simulated tapes are
one-way infinite with their left end at data cell 1, and neither simulated
head ever moves left of its own `#` marker.

This is a finite alphabet.  It is large because it contains every pair of
old symbols and all four head-flag combinations, but it does not grow during
the run.  The initial one-tape configuration is `@` followed by the data cell
`(blank1, blank2, h1 = 1, h2 = 1)`; all data cells to its right are blank.

### Simulating one two-tape step

The one-tape finite control has these phases, each of which is a finite scan:

1. **READ-H1.** Sweep right from `@` until the cell with `h1 = 1`.  Remember
   its tape-1 symbol `a` in the control.
2. **READ-H2.** Sweep right from `@` again until the cell with `h2 = 1`.
   Remember its tape-2 symbol `b`.
3. **STEP.** Apply the two-tape transition
   `(q, a, b) -> (q', a', d1, b', d2)` in the finite control.  Both old symbols
   and both directions are now finite-control data.
4. **WRITE-H1.** Sweep from `@` to the `h1` marker.  Replace `a` by `a'`, clear
   `h1`, move one cell in direction `d1`, and set `h1` on the destination cell.
5. **WRITE-H2.** Sweep from `@` to the `h2` marker.  Replace `b` by `b'`, clear
   `h2`, move one cell in direction `d2`, and set `h2` on the destination cell.
6. **NEXT.** Sweep back to `@` and enter state `q'`.

A marker move is local: the one-tape head is already on the marked cell, so it
clears the flag, moves to the adjacent cell, and sets the flag there.  If the
adjacent cell is beyond the written part of the tape, it is blank and is
created by the move.  A left move from data cell 1 would enter the home cell
`@`, but that case never occurs: the simulated head is on its left end marker
and the two-tape construction never moves left from that marker.  The flags are
independent, so both markers may occupy the same cell.

Each phase is a bounded number of sweeps to a marked cell and back.  The
control only stores `q`, the phase, the two read symbols, the written symbols,
and the two directions; all of those range over finite sets.  Therefore this
is an ordinary one-tape Turing machine with finitely many states and symbols.
It halts exactly when the simulated two-tape machine halts, i.e. at the first
position where the forbidden set contains all of `0,1,2,3,4`.

The cost is a polynomial slowdown: one two-tape step becomes a fixed number of
sweeps over the current tape extent, so a halting run of `T` two-tape steps
becomes a halting one-tape run of `O(T * extent)` steps.  This is a simulation
result, not a claim about the exact step count.

### If an explicit transition table is wanted

The layouts above are already machines at the macro level; the macro-states
are bookkeeping for the finite control.  Expanding them gives a table with
finitely many states and symbols (the table is large because every unary
comparison and shift is expanded into local moves).  The one-tape reduction
uses the same expansion, followed by the standard two-track encoding: every
cell stores one symbol from each simulated tape, and the head flags record
where the two old heads are.  One sweep of the encoded tape supplies the pair
of read symbols; further sweeps write the pair of new symbols and move the two
flags.  This proves the one-tape machine exists without changing the halting
condition; it does not reduce the state or symbol count.

## What this does and does not prove

* If the sequence contains a 5 at position `N`, this machine halts after a
  finite number of steps (the simulation overhead is a fixed polynomial in
  `N`; it is far larger than `N` but finite).  The one-tape version preserves
  this halting condition, with a further polynomial slowdown.
* This is **not** an FGH-level machine.  No ordinal `alpha`, no bound
  `f_alpha(n)`, and no Rocq verification are claimed here.  It is a direct
  simulator of the sequence, and its halting question is the first-5 question;
  that is a different obligation from an FGH machine that must halt within
  `f_alpha(n)` steps.
* If the sequence never contains a 5, the machine runs forever.
* "No 5 in the first `10^310` terms" is a finite-prefix lower bound.  It does
  **not** by itself make the machine a cryptid.  A cryptid needs a proof (or
  at least strong evidence) that the halting question is independent of the
  accepted axioms, not merely that a direct search is long.  A machine that
  halts at position `10^310` is still a halter, and a machine that provably
  never halts is a non-halter; neither is automatically a cryptid.

## Decimal rendering

Terms are integers.  When rendered in decimal, the term ten is the two
characters `10`; the pattern checks above are over **terms**, not over the
concatenated decimal characters.  If the intended object is instead a
character-level word over decimal digits, that is a different sequence and
the machine above must not be used for it.
