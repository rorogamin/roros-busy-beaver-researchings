import RequestProject.Fast

/-!
# The radix of a counter position

A position of the left counter is either radix 2 (the digits `02`, `22`) or
radix 3/2 (`03`, `23`); `rad2` records which.  The one fact needed later is that
**an increment never changes the radix of a position** (`rad2_nextD`,
`addT_rad2`).  It is what makes the radix pattern of a counter a function of the
block sequence that built it (`RequestProject.Shape`) and what lets a released
block be predicted from the digit that releases it.
-/

namespace SOC

/-! ## Radix-2 digits -/

/-- The radix of a position: `true` for the radix-2 digits `02`, `22`. -/
def rad2 : LD → Bool
  | .d0 => true
  | .d1 => true
  | _ => false

theorem rad2_nextD (d : LD) (t : Nat) : rad2 (nextD d t) = rad2 d := by
  unfold nextD
  split
  · rfl
  · cases d <;> rfl

/-- **An increment never changes the radix of a position.** -/
theorem addT_rad2 : ∀ {w w' : List LD} {t : Nat}, addT w t = some w' →
    w'.map rad2 = w.map rad2
  | w, w', 0, h => by simp at h; rw [h]
  | [], w', t + 1, h => by rw [addT_nil (by omega)] at h; exact absurd h (by simp)
  | d :: w, w', t + 1, h => by
      rw [addT_cons d w (by omega : t + 1 ≠ 0)] at h
      cases hv : addT w (carries d (t + 1)) with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some v =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          simp only [List.map_cons, addT_rad2 hv, List.cons.injEq, and_true]
          exact rad2_nextD d (t + 1)

/-! ## The overflow releases the top of the counter as blocks `44` -/

/-! ## The top of the counter survives the whole revolution -/

/-! ## The leading run of a block sequence -/

end SOC
