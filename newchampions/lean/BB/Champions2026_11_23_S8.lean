/-
  BB/Champions2026_11_23_S8.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 1 8-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_23.S8
open BB

/-! ### BB(6,8) — > f_{ω×2+1}(1) (`fwm21_8_blank` @ step 131) -/
def tm_6_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.L, some 5⟩
  | 0, 5 => some ⟨0, Dir.L, some 3⟩
  | 0, 6 => some ⟨0, Dir.L, some 5⟩
  | 0, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨2, Dir.R, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.R, some 3⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨2, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 5⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.L, some 3⟩
  | 5, 1 => some ⟨2, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.R, some 3⟩
  | 5, 3 => some ⟨4, Dir.L, some 2⟩
  | 5, 4 => some ⟨7, Dir.L, some 2⟩
  | 5, 5 => some ⟨1, Dir.R, some 0⟩
  | 5, 6 => some ⟨1, Dir.L, some 5⟩
  | 5, 7 => some ⟨4, Dir.R, some 3⟩
  | _, _ => none

theorem valid_6_8 : ValidTM 6 8 tm_6_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 6 => rfl

def landmark_6_8 : Config := { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 7] }
theorem reaches_landmark_6_8 : steps tm_6_8 131 initConfig = some landmark_6_8 := by
  have h0 : steps tm_6_8 35 initConfig = some { st := some 5, left := [5], cur := 5, right := [] } := rfl
  have hstep1 : steps tm_6_8 35 { st := some 5, left := [5], cur := 5, right := [] } = some { st := some 2, left := [], cur := 3, right := [3, 2, 2] } := rfl
  have h1 : steps tm_6_8 70 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 2, 2] } := steps_add tm_6_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_8 35 { st := some 2, left := [], cur := 3, right := [3, 2, 2] } = some { st := some 2, left := [2, 2], cur := 2, right := [3, 7] } := rfl
  have h2 : steps tm_6_8 105 initConfig = some { st := some 2, left := [2, 2], cur := 2, right := [3, 7] } := steps_add tm_6_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_8 26 { st := some 2, left := [2, 2], cur := 2, right := [3, 7] } = some { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 7] } := rfl
  have h3 : steps tm_6_8 131 initConfig = some { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 7] } := steps_add tm_6_8 105 26 initConfig _ _ h2 hstep3
  exact h3

end BB.Champions2026_11_23.S8
