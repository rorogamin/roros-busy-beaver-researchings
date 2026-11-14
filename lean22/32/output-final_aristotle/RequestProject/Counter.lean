import RequestProject.Macro

/-!
# The capacity of the mixed-radix counter

The left counter of `1LB3RB0LB---2RB_2RA3LA4LB2LB0RA` is a mixed-radix counter:
its radix-2 positions hold the digits `02`/`22` and its radix-3/2 positions the
digits `23`/`03`.  This file defines the **gap** of a counter,

```
gap w = the number of increments the counter can still perform
        before the sweep runs into the marker
```

and proves that it deserves the name:

* `Inc.gap_eq` — an increment decreases the gap by exactly one;
* `inc_exists` — an increment is possible as soon as the gap is positive, which
  is the reason a counter `w` performs exactly `gap w` increments
  and then overflows.  The
recursion for `gap` is where the two radices show up: a radix-2 digit doubles
the gap of the digits above it, a radix-3/2 digit multiplies it by `2/3`.
-/

namespace SOC

/--
`gap w` is the number of increments the counter `w` (least significant digit
first) can perform before it overflows.

Reading the recursion from the bottom digit up: a position holding `02` lets
`2 g + 1` increments through before the higher digits `w` have received their
`g`-th carry, one holding `22` lets `2 g` through, and the radix-3/2 positions
`03`, `23` — which emit *three* carries for every *two* increments — let only
about `2 g / 3` through.
-/
def gap : List LD → Nat
  | [] => 0
  | .d0 :: w => 2 * gap w + 1
  | .d1 :: w => 2 * gap w
  | .dB :: w => (2 * gap w + 1) / 3
  | .dA :: w => (2 * gap w) / 3

@[simp] theorem gap_nil : gap [] = 0 := rfl
@[simp] theorem gap_d0 (w : List LD) : gap (.d0 :: w) = 2 * gap w + 1 := rfl
@[simp] theorem gap_d1 (w : List LD) : gap (.d1 :: w) = 2 * gap w := rfl
@[simp] theorem gap_dB (w : List LD) : gap (.dB :: w) = (2 * gap w + 1) / 3 := rfl
@[simp] theorem gap_dA (w : List LD) : gap (.dA :: w) = (2 * gap w) / 3 := rfl

/-- **An increment uses up exactly one unit of gap.** -/
theorem Inc.gap_eq {w w' : List LD} (h : Inc w w') : gap w = gap w' + 1 := by
  induction h with
  | d0 w => simp
  | @d1 w w' _ ih => simp [ih]; omega
  | @dB w w' _ ih => simp [ih]; omega
  | @dA w w' w'' _ _ ih1 ih2 => simp [ih1, ih2]; omega

/-- An increment is possible exactly when the gap is positive. -/
theorem Inc.gap_pos {w w' : List LD} (h : Inc w w') : 0 < gap w := by
  rw [h.gap_eq]; omega

/-- An increment does not change the number of digits. -/
theorem Inc.length_eq {w w' : List LD} (h : Inc w w') : w'.length = w.length := by
  induction h with
  | d0 w => rfl
  | @d1 w w' _ ih => simp [ih]
  | @dB w w' _ ih => simp [ih]
  | @dA w w' w'' _ _ ih1 ih2 => simp [ih1, ih2]

/-- **If the gap is positive the counter can be incremented.** -/
theorem inc_exists : ∀ {w : List LD}, 0 < gap w → ∃ w', Inc w w'
  | [], h => by simp at h
  | .d0 :: w, _ => ⟨_, Inc.d0 w⟩
  | .d1 :: w, h => by
      have hw : 0 < gap w := by simp at h; omega
      obtain ⟨w', hw'⟩ := inc_exists (w := w) hw
      exact ⟨_, Inc.d1 hw'⟩
  | .dB :: w, h => by
      have hw : 0 < gap w := by simp only [gap_dB] at h; omega
      obtain ⟨w', hw'⟩ := inc_exists (w := w) hw
      exact ⟨_, Inc.dB hw'⟩
  | .dA :: w, h => by
      have hw : 1 < gap w := by simp only [gap_dA] at h; omega
      obtain ⟨w', hw'⟩ := inc_exists (w := w) (by omega : 0 < gap w)
      have hw'' : 0 < gap w' := by have := hw'.gap_eq; omega
      have hlen : w'.length = w.length := hw'.length_eq
      obtain ⟨w'', hw2⟩ := inc_exists (w := w') hw''
      exact ⟨_, Inc.dA hw' hw2⟩
  termination_by w => w.length
  decreasing_by
    all_goals simp_all [List.length_cons]
    all_goals omega

/-! ## Pushing a digit

The macro rules push a new least significant digit onto the counter.  The
effect on the gap is the recursion of `gap` itself, and it is what makes the
reset stage safe: pushing a radix-2 digit roughly doubles the gap, so a counter
that is being rebuilt from the right-hand material quickly gets enough room for
the four or five increments that reading a `1` costs.
-/

end SOC
