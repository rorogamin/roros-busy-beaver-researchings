# `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` never halts

**Result.** `ShiftOverflow.Counter.never_halts` (`RequestProject/NoHalt.lean`):

```lean
theorem never_halts : ∀ n, steps n init ≠ none
```

started on the blank tape, the machine is still running after every number of
steps.  The proof is complete and sorry-free; the only axioms it uses are
Lean's own (`propext`, `Classical.choice`, `Quot.sound`) together with
`Lean.ofReduceBool` / `Lean.trustCompiler`, which come from the two finite
checks that are discharged by evaluation (§6).

The machine is a **shift-overflow counter**, and the proof is the quantitative
form of the user's original intuition: what could kill the machine is a loose
`4` being swallowed by a block, i.e. an epoch reaching some position of the word
with too few visits of the head; and the number of visits arriving at every
position only ever grows from one epoch to the next.

---

## 1. The machine

`RequestProject/TuringMachine.lean`.  Two states `A`, `B`; tape symbols
`0,1,2,3,4` with `0` blank; `tr s a = some (w, d, s')` writes `w`, moves right
if `d`, and goes to `s'`; `tr B 4 = none` is the single halting instruction.
The ten equations `tr_A0 … tr_B4` are the ten instructions of the description
string, spelled out one by one, so that the formalised table can be checked
against `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---` by eye.

A configuration is a bi-infinite tape `ℤ → ℕ`, a head position and a state;
`steps n c` runs `n` steps and is `none` once the machine has halted.

## 2. Local passages and the excursion calculus

`RequestProject/Transits.lean` proves fourteen *transit* lemmas of the form

```lean
theorem transitL_22 (t : ℤ → ℕ) (p : ℤ) (h0 : t p = 2) (h1 : t (p + 1) = 2) :
    steps 2 ⟨t, p, .A⟩ = some ⟨upd2 t p 0 1, p + 2, .A⟩
```

each describing one uninterrupted passage of the head through a two- or
three-cell window, over an **arbitrary** tape outside the window.  The head
always enters in state `A` and always leaves in state `A`: the `A` signal is the
machine's only long-distance signal.

`RequestProject/Excursion.lean` makes these composable.  `Exc p t u` says: the
head arriving at cell `p` in state `A` moving right eventually leaves the
half-tape `[p, ∞)` again, arriving at `p - 1` in state `A`, touching no cell
`< p` and leaving the cells `≥ p` as in `u`; the definition quantifies over the
left context, so an `Exc` fact may be used inside any surroundings.  `ExcN k p t u`
is the `k`-fold iteration.  The file then restates every transit as an
excursion rule (`exc_22`, `exc_20`, `exc_23`, `exc_02`, `exc_00`, `exc_1`,
`exc_4`, `exc_223`, `exc_023`, …) and proves `ExcN_split`, the composition law
the whole development runs on.

## 3. The counter model

`RequestProject/DigitModel.lean`.  At an **epoch boundary** — the head in state
`A` on a fresh blank cell with nothing but blanks to its left — the word to the
right of the head has the shape

```
2 l₀ 2 l₁ 2 l₂ … 2 l_{m-1}          l_j ∈ {0,1,2,3}
```

so the configuration is just the list of low digits `L = [l₀,…,l_{m-1}]`.  One
epoch prefixes one blank cell, which shifts the block parse by one: the tokens
the head meets have *heads* `0 :: L`, and one single visit enters.  So one epoch
is a single left-to-right scan:

```lean
def epochF (L : List ℕ) : Option (List ℕ) := scan 1 (0 :: L)
```

`scan t s` sends `t` visits into the token whose head is the first entry of `s`,
the next entry being the cell behind it, and returns the low digits left behind.
Three kinds of token occur (`RequestProject/Steps.lean` names their arithmetic):

| token | transfer | digit left |
| --- | --- | --- |
| cheap `(a, c)`, `c ≠ 3` — radix 2 | `chT a t = 2t − hcost a` | `2` |
| expensive `(a, 3)` — radix 3/2 | `expT a t ≈ 2t/3` | `expD a t ∈ {0,1,3}` |
| frontier `[a]` — the last token | `frT a t ≈ 2t/3` run off the end | `frD a t`, then `freshW (frT a t)` |

with `hcost 2 = 0`, `hcost 0 = 1`, `hcost 1 = 2` — what the head of a token
costs it.  The radix-3/2 cycle is `2 0 → 2 3 → 2 1 → 2 0`: of every three
visits two get through (`cycE`, `cycS`).

`scan` returns `none` in exactly the dangerous situations: a token that receives
no visit at all, and the token `0 2 3`, which writes a `4` (`A · 0 2 3 = 2 3 4`)
that only a further visit erases, receiving fewer than two visits.  **That, and
nothing else, is how this machine can halt.**

## 4. The model is the machine

`RequestProject/ModelSpec.lean` proves the model faithful, by composing the
excursion rules of §2 — nothing about the machine's behaviour is assumed:

* `scan_spec` — if `scan t s = some o`, then `t` successive visits to the word
  whose token heads are `s` are all returned, and they leave the word `o`;
* `epoch_spec` / `boundary_step` — if `epochF L = some L'`, the head at an epoch
  boundary with word `L` comes back out to the left (so the machine does not
  halt during that epoch) and the next boundary shows the word `L'`;
* `never_halts_of_model` — if every iterate `epochIter n []` succeeds, then
  `∀ n, steps n init ≠ none`.

From here on everything is a statement about lists of digits and natural
numbers; the Turing machine does not appear again.

## 5. The frontier count, and what has to be proved

`RequestProject/Terminal.lean` isolates the one number that matters: `scanT t s`
is the scan run for the **frontier count** alone — the number of visits that run
off the right end of the word — and it succeeds exactly when `scan` does
(`scanT_isSome_iff`).  The fresh piece of word those `v` visits grow is
`freshW v`, one cell at a time, and its cells are read off by

| `v mod 3` | the cell holds | the rest is grown by |
| --- | --- | --- |
| `0` | `3` — an expensive (radix-3/2) cell | `v − 1 − v/3 ≈ 2v/3 − 1` |
| `1` | `1` — a cheap cell | `≈ 2v/3` |
| `2` | `0` — a cheap cell | `≈ 2v/3` |

Write

```lean
WordRich L  :=  ∃ w, scanT 1 (0 :: L) = some w ∧ 25 ≤ w
```

"the epoch of `L` succeeds and at least `25` visits run off the end of its
word".  Non-halting follows at once from: (i) `WordRich` reproduces itself, and
(ii) it holds at some epoch of the machine.  The whole of §§6–8 is (i).

## 6. The fresh part hands on a large frontier count

`RequestProject/Exit.lean`, theorem `fresh_exit`:

> a fresh part grown by `v ≥ 25` visits, entered with at least as many visits as
> grew it (three times as many behind a loose `1`), is left with at least `25`
> visits again.

Walk along the fresh part writing `v` for the visits that grew the current cell
and `u` for the visits arriving at it now.  At an **expensive** cell both are
multiplied by about `2/3`, so the ratio `u/v` is unchanged; at a **cheap** cell
`u` doubles while `v` still falls to `≈ 2v/3`, so the ratio gains a factor of
three.  The exit count is about `2u/3` at the end, so three cheap cells suffice,
and the proof is a chain of four invariants:

| phase | invariant | side condition |
| --- | --- | --- |
| 0 | `v ≤ u` | `400 ≤ postRun (v+3)` |
| 1 | `5(v+3) ≤ 2(u+3)` | `30 ≤ postRun (v+3)` |
| 2 | `7(v+3) ≤ u+3` | `4 ≤ postRun (v+3)` |
| 3 | `14(v+3) ≤ u+3` | — |

Each is preserved by an expensive cell and improved by a cheap one.  The side
conditions are what forbids an endless run of expensive cells.  In the variable
`n = v + 3` the growth step is exactly `n ↦ ⌈2n/3⌉`, and a cell is expensive
precisely when `3 ∣ n`; so an expensive run is as long as the `3`-adic valuation
of `n` and ends at

```
postRun n = 2 ^ v₃(n) · (n / 3 ^ v₃(n))
```

(`RequestProject/PostRun.lean`).  An expensive step leaves `postRun (v+3)`
unchanged while `v` falls, so the induction can run; and `n ^ 17 ≤ postRun n ^ 27`
— because `3 ^ 17 ≤ 2 ^ 27` — says that when the run ends the count is still
large enough to enter the next phase.  *A long expensive run has to be paid for
in advance by a large count.*

Phase 0 needs `postRun (v + 3) ≥ 400`, which holds as soon as `v ≥ 14000`.
Below that the statement is **checked by evaluation** (`exit_small_check`,
`native_decide`), and only for the tight arrival `u = v` (`u = 3v` behind a
loose `1`), which is enough because more arriving visits never hurt
(`scanT_mono`).

## 7. One epoch dominates the previous one

`RequestProject/Lockstep.lean`, theorem `lockstepT`.  Two consecutive epochs
scan the *same* positions: token `j` of the later epoch reads the digit token
`j` of the earlier one wrote, and sits behind the digit token `j-1` wrote.  The
comparison is carried token by token with the invariant

> the later epoch reaches each token with at least as many visits, and either
> its token head is no more expensive than the old one or it is ahead by one
> visit,

which closes because: where the old token was cheap the new one is cheap too and
gets the best head `2` (`chT_le_chT`); where both are expensive the heads keep
their order (`expT_le_expT`); and where the old token was expensive and the new
one cheap, the new one gains a whole visit (`expT_lt_chT`) — exactly what pays
for the only head that can get worse, a loose `1`.  At the end of the word the
new epoch walks into the fresh part the old one grew, and `fresh_exit` takes
over.  Conclusion:

```lean
theorem lockstepT … : scan t (a :: rest) = some o → scanT t (a :: rest) = some w → 25 ≤ w →
    a' ≤ 2 → t ≤ t' → (hcost a' ≤ hcost a ∨ t + 1 ≤ t') →
    ∃ w', scanT t' (a' :: o) = some w' ∧ 25 ≤ w'
```

## 8. Non-halting

`RequestProject/NoHalt.lean`.  `wordRich_step` is `lockstepT` applied with
`t = t' = 1` and head `0` on both sides: **if a word is rich, the next one is**.
The machine's fourth epoch boundary is rich — `78` visits run off the end of its
word — which is the second finite check (`seed_rich_check`, `native_decide`).
Hence `rich_forever`, hence `model_survives : ∀ n, (epochIter n []).isSome`, and
`never_halts_of_model` turns that into

```lean
theorem never_halts : ∀ n, steps n init ≠ none
```

The constant `25` is not sharp; it is simply a threshold comfortably above the
`2` at which a token could starve, and small enough to be verified at the fourth
epoch.

---

## The files

Eleven files, in dependency order; nothing else is needed for `never_halts`.

| file | contents |
| --- | --- |
| `RequestProject/TuringMachine.lean` | transition table, configurations, `steps`, `upd1/2/3` |
| `RequestProject/Transits.lean` | the fourteen local passages of the head |
| `RequestProject/Excursion.lean` | `Exc`, `ExcN`, composition, every rule as an excursion; `blank`, `init` |
| `RequestProject/DigitModel.lean` | the counter model: `stDigit`, `cycE`, `cycS`, `freshW`, `scan`, `epochF`, `epochIter` |
| `RequestProject/ModelSpec.lean` | `scan_spec`, `epoch_spec`, `never_halts_of_model` — the model is the machine |
| `RequestProject/Terminal.lean` | `hcost`, the frontier count `scanT`, the cells of `freshW` |
| `RequestProject/Steps.lean` | `chT`, `expT`, `expD`, `frT`, `frD` and the three unfolding rules |
| `RequestProject/PostRun.lean` | `postRun`, `n ^ 17 ≤ postRun n ^ 27` — the end of an expensive run |
| `RequestProject/Exit.lean` | `fresh_exit`: the fresh part hands on `25` visits |
| `RequestProject/Lockstep.lean` | token comparison and `lockstepT` |
| `RequestProject/NoHalt.lean` | `WordRich`, the seed, `never_halts` |

`lake build` builds all of them; the project depends only on Mathlib.

Earlier stages of this work — the cell-by-cell verification of the longitudinal
analysis table, the classification of the halting windows, the counting-phase
and carry lemmas for the left half of the tape, and the Python simulations used
to explore the dynamics — were checks along the way and are not used by the
final proof.  They are preserved in the git history (commit `3313969`) and have
been removed from the working tree to keep the development minimal.

## Notes for a translation to Rocq

* **Arithmetic.** Everything is `ℕ` with *truncated* subtraction and *floor*
  division, exactly as in Rocq's `Nat`; `cycE t d = t - (t - ((3 - d % 3) % 3) + 2) / 3`
  and the transfer functions are literal formulas, and every inequality between
  them is closed by `omega`, i.e. by linear arithmetic over `ℕ` with `/ 3` and
  `% 3` eliminated — `lia` after the same case split on `t mod 3` will do.
* **Recursive definitions.** Three definitions are well-founded rather than
  structural: `freshW` (measure `t`, decreasing by `cycE t 2 ≤ t`), `scan`
  (structural in the list except for the `0 :: rest` tail, where the list
  shortens), and `postRun` (measure `n`, decreasing by `2n/3 < n` when `3 ∣ n`
  and `n > 0`).  Use `Equations`/`Program Fixpoint` with those measures.
* **Tapes.** A tape is a function `ℤ → ℕ` updated pointwise (`Function.update`);
  no finiteness or normalisation is ever needed, and all tape reasoning is
  confined to §§1–4.
* **The two finite checks.** `seed_rich_check` evaluates `epochIter 4 []` and
  its frontier count; `exit_small_check` runs `scanT` over `freshW v` for every
  `v < 14000` and three head values.  Both are pure closed computations on
  `ℕ`/`list ℕ` and translate to `vm_compute`/`native_compute` goals; neither
  needs more than a second.
* **Structure.** §§1–4 (machine → model) and §§5–8 (model → non-halting) are
  independent: the second half never mentions `Cfg`, `step` or `steps`.
