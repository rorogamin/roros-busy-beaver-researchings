/-
# The counter model of `1RB2LA0RB4LB0LA_1LA3LA1RA4RA---`

One epoch of the machine can be described cell by cell, counting the visits of
the head one at a time; that description is faithful but can only be run for a
handful of epochs.  This file gives instead the **counter model**: the same
computation described by *digits* and *arrival counts*, which is what makes the
machine a shift-overflow counter and what one can actually prove things about.
`RequestProject/ModelSpec.lean` proves that the model does describe the
machine.

## The state

At an epoch boundary (the head on a fresh blank cell with only blanks to its
left) the word to the right of the head has the shape

```
2 l₀ 2 l₁ 2 l₂ … 2 l_{m-1}
```

so it is determined by its **low digits** `L = [l₀, …, l_{m-1}]`, each in
`{0,1,2,3}`.  One epoch prefixes a blank cell, which shifts the block parse by
one: the tokens the head now meets are

```
(0, 2)  (l₀, 2)  (l₁, 2)  …  (l_{m-2}, 2)  (l_{m-1}, 0)  (0,0) (0,0) …
```

i.e. the *heads* of the tokens are the list `0 :: L` and the cell following the
`j`-th token is the next entry of that list.  This is why one epoch is a single
left-to-right scan of `0 :: L`.

## The scan

A token receives `t` signals from the left and passes some number on to its
right neighbour:

| token | signals out | note |
| --- | --- | --- |
| `(2,2)` | `2t` | radix-2 digit: the doubling block `A · 2 2 = 2 2 A A` |
| `(0,2)` | `2t - 1` | a fresh block joining the counter |
| `(1,2)` | `2t - 2` | a loose `1` eats one signal, then doubles |
| `(a,2)` with a `3` behind it | `≈ 2(t-1)/3` | radix-3/2 digit: the expensive one |
| `(a,0)` | `≈ 2t/3` | the frontier, where the word grows |

The three-cell tokens `2 2 3` and `0 2 3` are the *only* way the second cell of a
token stops being a `2`; they turn a radix-2 position into a radix-3/2 one, and
the digit cycle `2 0 → 2 3 → 2 1 → 2 0` (`cycE`, `cycS` below) is that
radix-3/2 position: three signals in, two out.

`0 2 3` also writes a `4`, and the machine dies at a `4` unless a further signal
erases it; that is the single place where `scan` can fail (`t < 2`), and it is
the only halting danger this model knows of.
-/
import RequestProject.TuringMachine

namespace ShiftOverflow
namespace Counter

/-! ## The radix-3/2 digit

A digit sits in one of three states, named by the low cell of its block:

* state `0` — block `2 0`: **absorbs** the signal and becomes `2 3`;
* state `1` — block `2 3`: **passes** the signal on and becomes `2 1`;
* state `2` — block `2 1`: **passes** the signal on and becomes `2 0`.

So of every three signals two get through: the digit is a radix-3/2 position. -/

/-- The low cell of the block of a digit in state `d`. -/
def stDigit (d : ℕ) : ℕ := if d % 3 = 0 then 0 else if d % 3 = 1 then 3 else 1

/-- The state of a digit that started in state `d` and received `t` signals. -/
def cycS (t d : ℕ) : ℕ := (d + t) % 3

/-- The number of signals a digit in state `d` passes on out of `t` arrivals:
`t` minus the number of arrivals that find it in the absorbing state `0`. -/
def cycE (t d : ℕ) : ℕ := t - (t - ((3 - d % 3) % 3) + 2) / 3

theorem cycE_le (t d : ℕ) : cycE t d ≤ t := Nat.sub_le _ _

/-- The word the frontier grows when `t` signals run off the end of the used
tape: each fresh blank pair eats one signal, becomes a radix-3/2 digit and
passes about two thirds of the rest on. -/
def freshW : ℕ → List ℕ
  | 0 => []
  | t + 1 => stDigit (cycS t 2) :: freshW (cycE t 2)
  decreasing_by exact Nat.lt_succ_of_le (cycE_le _ _)

/-- **One epoch, as a scan.**  `scan t s` runs `t` signals into the token whose
head is the first entry of `s`, the following entry being the cell behind it.
It returns the list of low digits of the word that is left behind, or `none` if
the machine is in danger: a `4` that no further signal erases, or a token that
receives no signal at all. -/
def scan : ℕ → List ℕ → Option (List ℕ)
  | t, [] => some (freshW t)
  | t, [a] =>
      -- the last digit: its block is `(a, 0)`, the word ends here
      if t = 0 then none
      else if a = 0 then some (stDigit (cycS (t - 1) 2) :: freshW (cycE (t - 1) 2))
      else if a = 1 then some (stDigit (cycS (t - 1) 0) :: freshW (cycE (t - 1) 0))
      else if a = 2 then some (stDigit (cycS t 0) :: freshW (cycE t 0))
      else none
  | t, a :: c :: rest =>
      if t = 0 then none
      else if c = 3 then
        -- the expensive tokens: a `3` behind the block turns it into a digit
        if a = 2 then
          (scan (cycE (t - 1) 0) (0 :: rest)).map (fun o => stDigit (cycS (t - 1) 0) :: o)
        else if a = 0 then
          -- `A · 0 2 3 = 2 3 4`: a `4` is written, and only a further signal erases it
          if t < 2 then none
          else (scan (cycE (t - 1) 1 - 1) (0 :: rest)).map (fun o => stDigit (cycS (t - 1) 1) :: o)
        else if a = 1 then
          if t < 2 then none
          else (scan (cycE (t - 2) 0) (0 :: rest)).map (fun o => stDigit (cycS (t - 2) 0) :: o)
        else none
      else
        if a = 2 then (scan (2 * t) (c :: rest)).map (fun o => 2 :: o)
        else if a = 0 then (scan (2 * t - 1) (c :: rest)).map (fun o => 2 :: o)
        else if a = 1 then (scan (2 * t - 2) (c :: rest)).map (fun o => 2 :: o)
        else none

/-- **The one-epoch map of the counter model.**  Prefixing the blank cell means
prefixing a `0` to the list of token heads; one signal enters. -/
def epochF (L : List ℕ) : Option (List ℕ) := scan 1 (0 :: L)

/-- Iterating `epochF`. -/
def epochIter : ℕ → List ℕ → Option (List ℕ)
  | 0, L => some L
  | n + 1, L => (epochIter n L).bind epochF

end Counter
end ShiftOverflow
