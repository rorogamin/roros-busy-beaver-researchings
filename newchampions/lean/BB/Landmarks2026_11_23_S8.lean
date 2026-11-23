/-
  BB/Landmarks2026_11_23_S8.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs
  for 13 8-symbol landmark machines (2026-11-23 sweep).
-/
import BB.TM

namespace BB.Landmarks2026_11_23.S8
open BB

/-! ### 5x8 — fw2_7 @ step 252 -/
def tm_5_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨5, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.L, some 0⟩
  | 0, 7 => some ⟨7, Dir.R, some 4⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 1⟩
  | 1, 5 => some ⟨4, Dir.L, some 2⟩
  | 1, 6 => some ⟨6, Dir.L, some 2⟩
  | 1, 7 => some ⟨1, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨6, Dir.R, some 4⟩
  | 2, 6 => some ⟨6, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.R, some 3⟩
  | 3, 0 => some ⟨1, Dir.R, some 0⟩
  | 3, 1 => some ⟨0, Dir.L, some 4⟩
  | 3, 2 => some ⟨0, Dir.L, some 3⟩
  | 3, 3 => some ⟨1, Dir.L, some 4⟩
  | 3, 4 => some ⟨4, Dir.R, some 3⟩
  | 3, 5 => some ⟨5, Dir.R, some 3⟩
  | 3, 6 => some ⟨6, Dir.R, some 3⟩
  | 3, 7 => some ⟨5, Dir.R, some 4⟩
  | 4, 0 => some ⟨1, Dir.L, some 3⟩
  | 4, 1 => some ⟨2, Dir.R, some 3⟩
  | 4, 2 => some ⟨4, Dir.R, some 0⟩
  | 4, 3 => some ⟨0, Dir.R, some 4⟩
  | 4, 4 => some ⟨5, Dir.R, some 0⟩
  | 4, 5 => some ⟨6, Dir.R, some 0⟩
  | 4, 6 => some ⟨7, Dir.L, some 2⟩
  | 4, 7 => some ⟨6, Dir.L, some 1⟩
  | _, _ => none

theorem valid_5_8 : ValidTM 5 8 tm_5_8 := by
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
    | _ + 5 => omega
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
    | _ + 5 => rfl

def landmark_5_8 : Config := { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 6] }
theorem reaches_landmark_5_8 : steps tm_5_8 252 initConfig = some landmark_5_8 := by
  have h0 : steps tm_5_8 35 initConfig = some { st := some 0, left := [4, 0, 3], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_5_8 35 { st := some 0, left := [4, 0, 3], cur := 0, right := [] } = some { st := some 3, left := [3, 3], cur := 5, right := [] } := rfl
  have h1 : steps tm_5_8 70 initConfig = some { st := some 3, left := [3, 3], cur := 5, right := [] } := steps_add tm_5_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_8 35 { st := some 3, left := [3, 3], cur := 5, right := [] } = some { st := some 3, left := [6, 2, 3], cur := 0, right := [] } := rfl
  have h2 : steps tm_5_8 105 initConfig = some { st := some 3, left := [6, 2, 3], cur := 0, right := [] } := steps_add tm_5_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_8 35 { st := some 3, left := [6, 2, 3], cur := 0, right := [] } = some { st := some 2, left := [], cur := 2, right := [3, 7] } := rfl
  have h3 : steps tm_5_8 140 initConfig = some { st := some 2, left := [], cur := 2, right := [3, 7] } := steps_add tm_5_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_8 35 { st := some 2, left := [], cur := 2, right := [3, 7] } = some { st := some 2, left := [], cur := 3, right := [3, 3, 6, 6] } := rfl
  have h4 : steps tm_5_8 175 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 3, 6, 6] } := steps_add tm_5_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_8 35 { st := some 2, left := [], cur := 3, right := [3, 3, 6, 6] } = some { st := some 2, left := [2, 2, 3, 3], cur := 4, right := [5, 5, 6] } := rfl
  have h5 : steps tm_5_8 210 initConfig = some { st := some 2, left := [2, 2, 3, 3], cur := 4, right := [5, 5, 6] } := steps_add tm_5_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_8 35 { st := some 2, left := [2, 2, 3, 3], cur := 4, right := [5, 5, 6] } = some { st := some 2, left := [2, 2], cur := 2, right := [1, 1, 4, 5, 5, 6] } := rfl
  have h6 : steps tm_5_8 245 initConfig = some { st := some 2, left := [2, 2], cur := 2, right := [1, 1, 4, 5, 5, 6] } := steps_add tm_5_8 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_8 7 { st := some 2, left := [2, 2], cur := 2, right := [1, 1, 4, 5, 5, 6] } = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 6] } := rfl
  have h7 : steps tm_5_8 252 initConfig = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 6] } := steps_add tm_5_8 245 7 initConfig _ _ h6 hstep7
  exact h7

/-! ### 5x8 — fwm21_7 @ step 221 -/
def tm_5_8_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.L, some 0⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 0, 6 => some ⟨3, Dir.R, some 3⟩
  | 0, 7 => some ⟨2, Dir.L, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 4⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.L, some 1⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨2, Dir.L, some 0⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨5, Dir.L, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨4, Dir.R, some 2⟩
  | _, _ => none

theorem valid_5_8_1 : ValidTM 5 8 tm_5_8_1 := by
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
    | _ + 5 => omega
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
    | _ + 5 => rfl

def landmark_5_8_1 : Config := { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2] }
theorem reaches_landmark_5_8_1 : steps tm_5_8_1 221 initConfig = some landmark_5_8_1 := by
  have h0 : steps tm_5_8_1 35 initConfig = some { st := some 0, left := [3, 3, 3, 3], cur := 3, right := [4, 1] } := rfl
  have hstep1 : steps tm_5_8_1 35 { st := some 0, left := [3, 3, 3, 3], cur := 3, right := [4, 1] } = some { st := some 0, left := [3, 6, 3, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_5_8_1 70 initConfig = some { st := some 0, left := [3, 6, 3, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] } := steps_add tm_5_8_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_8_1 35 { st := some 0, left := [3, 6, 3, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 7, 1] } := rfl
  have h2 : steps tm_5_8_1 105 initConfig = some { st := some 2, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 7, 1] } := steps_add tm_5_8_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_8_1 35 { st := some 2, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 7, 1] } = some { st := some 2, left := [2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7] } := rfl
  have h3 : steps tm_5_8_1 140 initConfig = some { st := some 2, left := [2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7] } := steps_add tm_5_8_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_8_1 35 { st := some 2, left := [2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 7, right := [2] } := rfl
  have h4 : steps tm_5_8_1 175 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 7, right := [2] } := steps_add tm_5_8_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_8_1 35 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 7, right := [2] } = some { st := some 2, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2, 2] } := rfl
  have h5 : steps tm_5_8_1 210 initConfig = some { st := some 2, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2, 2] } := steps_add tm_5_8_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_8_1 11 { st := some 2, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2, 2] } = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2] } := rfl
  have h6 : steps tm_5_8_1 221 initConfig = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2] } := steps_add tm_5_8_1 210 11 initConfig _ _ h5 hstep6
  exact h6

/-! ### 5x8 — fwm21_8 @ step 151 -/
def tm_5_8_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.L, some 2⟩
  | 1, 5 => some ⟨1, Dir.R, some 1⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 1, 7 => some ⟨3, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.R, some 3⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨7, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨7, Dir.L, some 4⟩
  | _, _ => none

theorem valid_5_8_2 : ValidTM 5 8 tm_5_8_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 1 =>
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
    | _ + 5 => omega
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
    | _ + 5 => rfl

def landmark_5_8_2 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 3, 2] }
theorem reaches_landmark_5_8_2 : steps tm_5_8_2 151 initConfig = some landmark_5_8_2 := by
  have h0 : steps tm_5_8_2 35 initConfig = some { st := some 4, left := [5, 5, 6], cur := 7, right := [2] } := rfl
  have hstep1 : steps tm_5_8_2 35 { st := some 4, left := [5, 5, 6], cur := 7, right := [2] } = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 6, right := [7, 2] } := rfl
  have h1 : steps tm_5_8_2 70 initConfig = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 6, right := [7, 2] } := steps_add tm_5_8_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_8_2 35 { st := some 4, left := [6, 6, 6, 6, 6], cur := 6, right := [7, 2] } = some { st := some 2, left := [2, 2, 3], cur := 3, right := [3, 7, 2, 3, 2] } := rfl
  have h2 : steps tm_5_8_2 105 initConfig = some { st := some 2, left := [2, 2, 3], cur := 3, right := [3, 7, 2, 3, 2] } := steps_add tm_5_8_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_8_2 35 { st := some 2, left := [2, 2, 3], cur := 3, right := [3, 7, 2, 3, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2], cur := 1, right := [7, 2, 3, 2] } := rfl
  have h3 : steps tm_5_8_2 140 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2], cur := 1, right := [7, 2, 3, 2] } := steps_add tm_5_8_2 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_8_2 11 { st := some 2, left := [2, 2, 2, 2, 2], cur := 1, right := [7, 2, 3, 2] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 3, 2] } := rfl
  have h4 : steps tm_5_8_2 151 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 3, 2] } := steps_add tm_5_8_2 140 11 initConfig _ _ h3 hstep4
  exact h4

/-! ### 5x8 — fwm21_8_blank @ step 146 -/
def tm_5_8_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.R, some 3⟩
  | 0, 5 => some ⟨0, Dir.R, some 0⟩
  | 0, 6 => some ⟨1, Dir.L, some 3⟩
  | 0, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨0, Dir.L, some 4⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 4⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.L, some 1⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨0, Dir.R, some 4⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.L, some 2⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | _, _ => none

theorem valid_5_8_3 : ValidTM 5 8 tm_5_8_3 := by
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
    | _ + 5 => omega
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
    | _ + 5 => rfl

def landmark_5_8_3 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7] }
theorem reaches_landmark_5_8_3 : steps tm_5_8_3 146 initConfig = some landmark_5_8_3 := by
  have h0 : steps tm_5_8_3 35 initConfig = some { st := some 0, left := [1, 3], cur := 6, right := [] } := rfl
  have hstep1 : steps tm_5_8_3 35 { st := some 0, left := [1, 3], cur := 6, right := [] } = some { st := some 4, left := [6, 6], cur := 5, right := [4, 3, 2] } := rfl
  have h1 : steps tm_5_8_3 70 initConfig = some { st := some 4, left := [6, 6], cur := 5, right := [4, 3, 2] } := steps_add tm_5_8_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_8_3 35 { st := some 4, left := [6, 6], cur := 5, right := [4, 3, 2] } = some { st := some 2, left := [3, 3, 3], cur := 3, right := [4, 7, 7] } := rfl
  have h2 : steps tm_5_8_3 105 initConfig = some { st := some 2, left := [3, 3, 3], cur := 3, right := [4, 7, 7] } := steps_add tm_5_8_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_8_3 35 { st := some 2, left := [3, 3, 3], cur := 3, right := [4, 7, 7] } = some { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 7, 7, 7] } := rfl
  have h3 : steps tm_5_8_3 140 initConfig = some { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 7, 7, 7] } := steps_add tm_5_8_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_8_3 6 { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 7, 7, 7] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7] } := rfl
  have h4 : steps tm_5_8_3 146 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7] } := steps_add tm_5_8_3 140 6 initConfig _ _ h3 hstep4
  exact h4

/-! ### 6x8 — fwm21_8_blank @ step 131 -/
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

/-! ### 6x8 — fwm2_7 @ step 190 -/
def tm_6_8_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.R, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 5⟩
  | 1, 6 => some ⟨2, Dir.R, some 3⟩
  | 1, 7 => some ⟨4, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨1, Dir.R, some 4⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.R, some 5⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨7, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨6, Dir.L, some 5⟩
  | 5, 0 => some ⟨1, Dir.R, some 1⟩
  | 5, 1 => some ⟨2, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.R, some 3⟩
  | 5, 3 => some ⟨4, Dir.L, some 2⟩
  | 5, 4 => some ⟨7, Dir.L, some 0⟩
  | 5, 5 => some ⟨4, Dir.R, some 3⟩
  | 5, 6 => some ⟨0, Dir.L, some 3⟩
  | 5, 7 => some ⟨1, Dir.L, some 4⟩
  | _, _ => none

theorem valid_6_8_1 : ValidTM 6 8 tm_6_8_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 1 =>
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

def landmark_6_8_1 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [2] }
theorem reaches_landmark_6_8_1 : steps tm_6_8_1 190 initConfig = some landmark_6_8_1 := by
  have h0 : steps tm_6_8_1 35 initConfig = some { st := some 3, left := [0, 3], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_6_8_1 35 { st := some 3, left := [0, 3], cur := 1, right := [] } = some { st := some 4, left := [6], cur := 4, right := [4, 5] } := rfl
  have h1 : steps tm_6_8_1 70 initConfig = some { st := some 4, left := [6], cur := 4, right := [4, 5] } := steps_add tm_6_8_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_8_1 35 { st := some 4, left := [6], cur := 4, right := [4, 5] } = some { st := some 0, left := [6], cur := 6, right := [7] } := rfl
  have h2 : steps tm_6_8_1 105 initConfig = some { st := some 0, left := [6], cur := 6, right := [7] } := steps_add tm_6_8_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_8_1 35 { st := some 0, left := [6], cur := 6, right := [7] } = some { st := some 2, left := [2, 2, 2], cur := 7, right := [2] } := rfl
  have h3 : steps tm_6_8_1 140 initConfig = some { st := some 2, left := [2, 2, 2], cur := 7, right := [2] } := steps_add tm_6_8_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_8_1 35 { st := some 2, left := [2, 2, 2], cur := 7, right := [2] } = some { st := some 0, left := [5, 1, 5, 3, 2, 2, 2], cur := 0, right := [] } := rfl
  have h4 : steps tm_6_8_1 175 initConfig = some { st := some 0, left := [5, 1, 5, 3, 2, 2, 2], cur := 0, right := [] } := steps_add tm_6_8_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_6_8_1 15 { st := some 0, left := [5, 1, 5, 3, 2, 2, 2], cur := 0, right := [] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [2] } := rfl
  have h5 : steps tm_6_8_1 190 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [2] } := steps_add tm_6_8_1 175 15 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x8 — fwm21_7 @ step 169 -/
def tm_7_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.L, some 0⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 0, 6 => some ⟨1, Dir.L, some 6⟩
  | 0, 7 => some ⟨1, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 4⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨1, Dir.R, some 5⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.R, some 0⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 0⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨2, Dir.R, some 5⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨5, Dir.L, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨0, Dir.L, some 5⟩
  | 5, 0 => some ⟨0, Dir.L, some 2⟩
  | 5, 1 => some ⟨1, Dir.R, some 2⟩
  | 5, 2 => some ⟨1, Dir.R, some 0⟩
  | 5, 3 => some ⟨0, Dir.L, some 6⟩
  | 5, 4 => some ⟨4, Dir.R, some 2⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨7, Dir.R, some 3⟩
  | 5, 7 => some ⟨2, Dir.L, some 0⟩
  | 6, 0 => some ⟨0, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 2⟩
  | 6, 2 => some ⟨4, Dir.R, some 0⟩
  | 6, 3 => some ⟨1, Dir.L, some 3⟩
  | 6, 4 => some ⟨4, Dir.R, some 3⟩
  | 6, 5 => some ⟨0, Dir.L, some 0⟩
  | 6, 6 => some ⟨1, Dir.L, some 2⟩
  | 6, 7 => some ⟨7, Dir.R, some 0⟩
  | _, _ => none

theorem valid_7_8 : ValidTM 7 8 tm_7_8 := by
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
    | 6 =>
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
    | _ + 7 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 7 => rfl

def landmark_7_8 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [2] }
theorem reaches_landmark_7_8 : steps tm_7_8 169 initConfig = some landmark_7_8 := by
  have h0 : steps tm_7_8 35 initConfig = some { st := some 0, left := [1], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_7_8 35 { st := some 0, left := [1], cur := 0, right := [] } = some { st := some 0, left := [3, 4, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_7_8 70 initConfig = some { st := some 0, left := [3, 4, 3], cur := 0, right := [] } := steps_add tm_7_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_8 35 { st := some 0, left := [3, 4, 3], cur := 0, right := [] } = some { st := some 5, left := [1, 2, 3], cur := 1, right := [] } := rfl
  have h2 : steps tm_7_8 105 initConfig = some { st := some 5, left := [1, 2, 3], cur := 1, right := [] } := steps_add tm_7_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_8 35 { st := some 5, left := [1, 2, 3], cur := 1, right := [] } = some { st := some 3, left := [7], cur := 5, right := [5, 5, 0, 1] } := rfl
  have h3 : steps tm_7_8 140 initConfig = some { st := some 3, left := [7], cur := 5, right := [5, 5, 0, 1] } := steps_add tm_7_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_8 29 { st := some 3, left := [7], cur := 5, right := [5, 5, 0, 1] } = some { st := some 1, left := [2, 2, 3], cur := 1, right := [2] } := rfl
  have h4 : steps tm_7_8 169 initConfig = some { st := some 1, left := [2, 2, 3], cur := 1, right := [2] } := steps_add tm_7_8 140 29 initConfig _ _ h3 hstep4
  exact h4

/-! ### 7x8 — fwm21fw1_7 @ step 311 -/
def tm_7_8_1 : TM
  | 0, 0 => some ⟨5, Dir.L, some 5⟩
  | 0, 1 => some ⟨6, Dir.L, some 0⟩
  | 0, 2 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 5⟩
  | 0, 4 => some ⟨6, Dir.R, some 0⟩
  | 0, 5 => some ⟨4, Dir.L, some 3⟩
  | 0, 6 => some ⟨5, Dir.R, some 1⟩
  | 0, 7 => some ⟨3, Dir.R, some 5⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 4⟩
  | 1, 2 => some ⟨6, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 0⟩
  | 1, 5 => some ⟨1, Dir.L, some 4⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 2, 0 => some ⟨6, Dir.R, some 0⟩
  | 2, 1 => some ⟨0, Dir.L, some 0⟩
  | 2, 2 => some ⟨4, Dir.L, some 2⟩
  | 2, 3 => some ⟨4, Dir.L, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 0⟩
  | 2, 5 => some ⟨6, Dir.L, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 5⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.L, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 3⟩
  | 3, 3 => some ⟨2, Dir.R, some 3⟩
  | 3, 4 => some ⟨0, Dir.L, some 5⟩
  | 3, 5 => some ⟨6, Dir.L, some 2⟩
  | 3, 6 => some ⟨5, Dir.R, some 2⟩
  | 3, 7 => some ⟨7, Dir.R, some 2⟩
  | 4, 0 => some ⟨6, Dir.R, some 0⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 4, 3 => some ⟨2, Dir.R, some 1⟩
  | 4, 4 => some ⟨2, Dir.R, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 4⟩
  | 4, 6 => some ⟨2, Dir.L, some 4⟩
  | 4, 7 => some ⟨3, Dir.R, some 5⟩
  | 5, 0 => some ⟨0, Dir.L, some 3⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨0, Dir.L, some 6⟩
  | 5, 3 => some ⟨4, Dir.R, some 5⟩
  | 5, 4 => some ⟨7, Dir.L, some 0⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.R, some 4⟩
  | 5, 7 => some ⟨7, Dir.L, some 3⟩
  | 6, 0 => some ⟨0, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.R, some 0⟩
  | 6, 2 => some ⟨3, Dir.L, some 0⟩
  | 6, 3 => some ⟨3, Dir.R, some 0⟩
  | 6, 4 => some ⟨1, Dir.L, some 6⟩
  | 6, 5 => some ⟨1, Dir.R, some 3⟩
  | 6, 6 => some ⟨0, Dir.L, some 6⟩
  | 6, 7 => some ⟨5, Dir.L, some 2⟩
  | _, _ => none

theorem valid_7_8_1 : ValidTM 7 8 tm_7_8_1 := by
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
    | 6 =>
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
    | _ + 7 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 7 => rfl

def landmark_7_8_1 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 2] }
theorem reaches_landmark_7_8_1 : steps tm_7_8_1 311 initConfig = some landmark_7_8_1 := by
  have h0 : steps tm_7_8_1 35 initConfig = some { st := some 4, left := [3], cur := 0, right := [5, 0, 4, 6, 2] } := rfl
  have hstep1 : steps tm_7_8_1 35 { st := some 4, left := [3], cur := 0, right := [5, 0, 4, 6, 2] } = some { st := some 0, left := [3], cur := 5, right := [4, 3] } := rfl
  have h1 : steps tm_7_8_1 70 initConfig = some { st := some 0, left := [3], cur := 5, right := [4, 3] } := steps_add tm_7_8_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_8_1 35 { st := some 0, left := [3], cur := 5, right := [4, 3] } = some { st := some 6, left := [], cur := 1, right := [7, 5] } := rfl
  have h2 : steps tm_7_8_1 105 initConfig = some { st := some 6, left := [], cur := 1, right := [7, 5] } := steps_add tm_7_8_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_8_1 35 { st := some 6, left := [], cur := 1, right := [7, 5] } = some { st := some 5, left := [], cur := 3, right := [3, 7, 5] } := rfl
  have h3 : steps tm_7_8_1 140 initConfig = some { st := some 5, left := [], cur := 3, right := [3, 7, 5] } := steps_add tm_7_8_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_8_1 35 { st := some 5, left := [], cur := 3, right := [3, 7, 5] } = some { st := some 5, left := [], cur := 1, right := [5, 3, 7, 5] } := rfl
  have h4 : steps tm_7_8_1 175 initConfig = some { st := some 5, left := [], cur := 1, right := [5, 3, 7, 5] } := steps_add tm_7_8_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_8_1 35 { st := some 5, left := [], cur := 1, right := [5, 3, 7, 5] } = some { st := some 0, left := [6, 3], cur := 5, right := [6, 7, 5, 2, 2] } := rfl
  have h5 : steps tm_7_8_1 210 initConfig = some { st := some 0, left := [6, 3], cur := 5, right := [6, 7, 5, 2, 2] } := steps_add tm_7_8_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_8_1 35 { st := some 0, left := [6, 3], cur := 5, right := [6, 7, 5, 2, 2] } = some { st := some 2, left := [5, 3], cur := 4, right := [7, 0, 7, 5, 2, 2] } := rfl
  have h6 : steps tm_7_8_1 245 initConfig = some { st := some 2, left := [5, 3], cur := 4, right := [7, 0, 7, 5, 2, 2] } := steps_add tm_7_8_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_8_1 35 { st := some 2, left := [5, 3], cur := 4, right := [7, 0, 7, 5, 2, 2] } = some { st := some 5, left := [], cur := 1, right := [5, 7, 6, 2, 2] } := rfl
  have h7 : steps tm_7_8_1 280 initConfig = some { st := some 5, left := [], cur := 1, right := [5, 7, 6, 2, 2] } := steps_add tm_7_8_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_8_1 31 { st := some 5, left := [], cur := 1, right := [5, 7, 6, 2, 2] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 2] } := rfl
  have h8 : steps tm_7_8_1 311 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 2] } := steps_add tm_7_8_1 280 31 initConfig _ _ h7 hstep8
  exact h8

/-! ### 7x8 — fwm2_7 @ step 309 -/
def tm_7_8_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨1, Dir.L, some 0⟩
  | 1, 5 => some ⟨0, Dir.L, some 5⟩
  | 1, 6 => some ⟨2, Dir.R, some 3⟩
  | 1, 7 => some ⟨7, Dir.R, some 6⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 1⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.R, some 0⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 6⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨1, Dir.R, some 4⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨2, Dir.L, some 6⟩
  | 5, 0 => some ⟨1, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨2, Dir.R, some 6⟩
  | 5, 4 => some ⟨4, Dir.R, some 5⟩
  | 5, 5 => some ⟨0, Dir.L, some 6⟩
  | 5, 6 => some ⟨0, Dir.L, some 3⟩
  | 5, 7 => some ⟨7, Dir.L, some 2⟩
  | 6, 0 => some ⟨1, Dir.R, some 3⟩
  | 6, 1 => some ⟨2, Dir.L, some 3⟩
  | 6, 2 => some ⟨3, Dir.R, some 3⟩
  | 6, 3 => some ⟨4, Dir.L, some 2⟩
  | 6, 4 => some ⟨6, Dir.L, some 2⟩
  | 6, 5 => some ⟨4, Dir.R, some 3⟩
  | 6, 6 => some ⟨1, Dir.L, some 3⟩
  | 6, 7 => some ⟨5, Dir.R, some 6⟩
  | _, _ => none

theorem valid_7_8_2 : ValidTM 7 8 tm_7_8_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 1 =>
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
    | 6 =>
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
    | _ + 7 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 7 => rfl

def landmark_7_8_2 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 2] }
theorem reaches_landmark_7_8_2 : steps tm_7_8_2 309 initConfig = some landmark_7_8_2 := by
  have h0 : steps tm_7_8_2 35 initConfig = some { st := some 0, left := [3], cur := 6, right := [] } := rfl
  have hstep1 : steps tm_7_8_2 35 { st := some 0, left := [3], cur := 6, right := [] } = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := rfl
  have h1 : steps tm_7_8_2 70 initConfig = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := steps_add tm_7_8_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_8_2 35 { st := some 4, left := [6], cur := 5, right := [4, 4] } = some { st := some 2, left := [], cur := 0, right := [6] } := rfl
  have h2 : steps tm_7_8_2 105 initConfig = some { st := some 2, left := [], cur := 0, right := [6] } := steps_add tm_7_8_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_8_2 35 { st := some 2, left := [], cur := 0, right := [6] } = some { st := some 3, left := [4, 6], cur := 2, right := [] } := rfl
  have h3 : steps tm_7_8_2 140 initConfig = some { st := some 3, left := [4, 6], cur := 2, right := [] } := steps_add tm_7_8_2 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_8_2 35 { st := some 3, left := [4, 6], cur := 2, right := [] } = some { st := some 3, left := [5, 5], cur := 4, right := [5, 7, 6] } := rfl
  have h4 : steps tm_7_8_2 175 initConfig = some { st := some 3, left := [5, 5], cur := 4, right := [5, 7, 6] } := steps_add tm_7_8_2 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_8_2 35 { st := some 3, left := [5, 5], cur := 4, right := [5, 7, 6] } = some { st := some 2, left := [6, 6], cur := 6, right := [1, 1, 1, 3, 7, 6] } := rfl
  have h5 : steps tm_7_8_2 210 initConfig = some { st := some 2, left := [6, 6], cur := 6, right := [1, 1, 1, 3, 7, 6] } := steps_add tm_7_8_2 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_8_2 35 { st := some 2, left := [6, 6], cur := 6, right := [1, 1, 1, 3, 7, 6] } = some { st := some 6, left := [2, 2, 2, 3, 3, 3, 3, 3], cur := 7, right := [1] } := rfl
  have h6 : steps tm_7_8_2 245 initConfig = some { st := some 6, left := [2, 2, 2, 3, 3, 3, 3, 3], cur := 7, right := [1] } := steps_add tm_7_8_2 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_8_2 35 { st := some 6, left := [2, 2, 2, 3, 3, 3, 3, 3], cur := 7, right := [1] } = some { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 2] } := rfl
  have h7 : steps tm_7_8_2 280 initConfig = some { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 2] } := steps_add tm_7_8_2 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_8_2 29 { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 2] } := rfl
  have h8 : steps tm_7_8_2 309 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 2] } := steps_add tm_7_8_2 280 29 initConfig _ _ h7 hstep8
  exact h8

/-! ### 14x8 — fwpw4_8_blank @ step 266 -/
def tm_14_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨0, Dir.L, some 4⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨1, Dir.R, some 2⟩
  | 0, 6 => some ⟨4, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.R, some 12⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 4⟩
  | 4, 5 => some ⟨0, Dir.L, some 12⟩
  | 4, 6 => some ⟨1, Dir.R, some 1⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨4, Dir.R, some 11⟩
  | 6, 5 => some ⟨0, Dir.L, some 8⟩
  | 6, 6 => some ⟨0, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 0⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨6, Dir.L, some 11⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 13⟩
  | 8, 5 => some ⟨0, Dir.L, some 9⟩
  | 8, 6 => some ⟨1, Dir.L, some 13⟩
  | 8, 7 => some ⟨0, Dir.L, some 12⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨4, Dir.L, some 11⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨5, Dir.R, some 9⟩
  | 9, 5 => some ⟨0, Dir.L, some 10⟩
  | 9, 6 => some ⟨4, Dir.L, some 10⟩
  | 9, 7 => some ⟨1, Dir.L, some 10⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨0, Dir.L, some 13⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨1, Dir.R, some 13⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨0, Dir.L, some 11⟩
  | 10, 7 => some ⟨2, Dir.L, some 0⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨1, Dir.L, some 0⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 8⟩
  | 11, 5 => some ⟨7, Dir.R, some 12⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨2, Dir.L, some 5⟩
  | 12, 0 => some ⟨1, Dir.L, some 0⟩
  | 12, 1 => some ⟨1, Dir.L, some 9⟩
  | 12, 2 => some ⟨0, Dir.R, some 9⟩
  | 12, 3 => some ⟨0, Dir.L, some 13⟩
  | 12, 4 => some ⟨7, Dir.L, some 11⟩
  | 12, 5 => some ⟨0, Dir.L, some 13⟩
  | 12, 6 => some ⟨4, Dir.L, some 8⟩
  | 12, 7 => some ⟨2, Dir.L, some 13⟩
  | 13, 0 => some ⟨1, Dir.L, some 5⟩
  | 13, 1 => some ⟨1, Dir.L, some 5⟩
  | 13, 2 => some ⟨0, Dir.R, some 13⟩
  | 13, 3 => some ⟨1, Dir.L, some 11⟩
  | 13, 4 => some ⟨4, Dir.R, some 12⟩
  | 13, 5 => some ⟨0, Dir.L, some 0⟩
  | 13, 6 => some ⟨0, Dir.L, some 0⟩
  | 13, 7 => some ⟨2, Dir.L, some 12⟩
  | _, _ => none

theorem valid_14_8 : ValidTM 14 8 tm_14_8 := by
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
      | 0 => exact ⟨by decide, by decide⟩
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
    | 6 =>
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
    | 7 =>
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
    | 8 =>
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
    | 9 =>
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
    | 10 =>
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
    | 11 =>
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
    | 12 =>
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
    | 13 =>
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
    | _ + 14 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 14 => rfl

def landmark_14_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 7] }
theorem reaches_landmark_14_8 : steps tm_14_8 266 initConfig = some landmark_14_8 := by
  have h0 : steps tm_14_8 35 initConfig = some { st := some 11, left := [], cur := 0, right := [1] } := rfl
  have hstep1 : steps tm_14_8 35 { st := some 11, left := [], cur := 0, right := [1] } = some { st := some 3, left := [], cur := 4, right := [2, 1] } := rfl
  have h1 : steps tm_14_8 70 initConfig = some { st := some 3, left := [], cur := 4, right := [2, 1] } := steps_add tm_14_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_8 35 { st := some 3, left := [], cur := 4, right := [2, 1] } = some { st := some 13, left := [], cur := 7, right := [] } := rfl
  have h2 : steps tm_14_8 105 initConfig = some { st := some 13, left := [], cur := 7, right := [] } := steps_add tm_14_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_8 35 { st := some 13, left := [], cur := 7, right := [] } = some { st := some 1, left := [5, 3], cur := 5, right := [1] } := rfl
  have h3 : steps tm_14_8 140 initConfig = some { st := some 1, left := [5, 3], cur := 5, right := [1] } := steps_add tm_14_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_8 35 { st := some 1, left := [5, 3], cur := 5, right := [1] } = some { st := some 10, left := [7], cur := 7, right := [1, 1] } := rfl
  have h4 : steps tm_14_8 175 initConfig = some { st := some 10, left := [7], cur := 7, right := [1, 1] } := steps_add tm_14_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_14_8 35 { st := some 10, left := [7], cur := 7, right := [1, 1] } = some { st := some 0, left := [3, 1, 7], cur := 3, right := [] } := rfl
  have h5 : steps tm_14_8 210 initConfig = some { st := some 0, left := [3, 1, 7], cur := 3, right := [] } := steps_add tm_14_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_14_8 35 { st := some 0, left := [3, 1, 7], cur := 3, right := [] } = some { st := some 11, left := [3, 4, 7], cur := 1, right := [] } := rfl
  have h6 : steps tm_14_8 245 initConfig = some { st := some 11, left := [3, 4, 7], cur := 1, right := [] } := steps_add tm_14_8 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_14_8 21 { st := some 11, left := [3, 4, 7], cur := 1, right := [] } = some { st := some 8, left := [2, 3], cur := 1, right := [4, 7] } := rfl
  have h7 : steps tm_14_8 266 initConfig = some { st := some 8, left := [2, 3], cur := 1, right := [4, 7] } := steps_add tm_14_8 245 21 initConfig _ _ h6 hstep7
  exact h7

/-! ### 15x8 — fwpw_8 @ step 19925 -/
def tm_15_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨3, Dir.L, some 6⟩
  | 0, 5 => some ⟨0, Dir.L, some 1⟩
  | 0, 6 => some ⟨0, Dir.L, some 6⟩
  | 0, 7 => some ⟨0, Dir.L, some 5⟩
  | 1, 0 => some ⟨7, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 8⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 13⟩
  | 4, 5 => some ⟨0, Dir.L, some 9⟩
  | 4, 6 => some ⟨3, Dir.L, some 13⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.L, some 8⟩
  | 6, 5 => some ⟨0, Dir.L, some 3⟩
  | 6, 6 => some ⟨0, Dir.L, some 8⟩
  | 6, 7 => some ⟨0, Dir.L, some 4⟩
  | 7, 0 => some ⟨0, Dir.L, some 0⟩
  | 7, 1 => some ⟨5, Dir.R, some 7⟩
  | 7, 2 => some ⟨0, Dir.L, some 0⟩
  | 7, 3 => some ⟨6, Dir.R, some 7⟩
  | 7, 4 => some ⟨4, Dir.R, some 5⟩
  | 7, 5 => some ⟨0, Dir.L, some 11⟩
  | 7, 6 => some ⟨6, Dir.L, some 13⟩
  | 7, 7 => some ⟨7, Dir.R, some 7⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨2, Dir.R, some 11⟩
  | 8, 3 => some ⟨0, Dir.R, some 2⟩
  | 8, 4 => some ⟨5, Dir.L, some 5⟩
  | 8, 5 => some ⟨0, Dir.L, some 4⟩
  | 8, 6 => some ⟨1, Dir.L, some 13⟩
  | 8, 7 => some ⟨0, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 9⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨0, Dir.L, some 13⟩
  | 9, 3 => some ⟨0, Dir.L, some 1⟩
  | 9, 4 => some ⟨2, Dir.R, some 13⟩
  | 9, 5 => some ⟨5, Dir.L, some 10⟩
  | 9, 6 => some ⟨0, Dir.L, some 7⟩
  | 9, 7 => some ⟨2, Dir.R, some 12⟩
  | 10, 0 => some ⟨0, Dir.R, some 10⟩
  | 10, 1 => some ⟨0, Dir.L, some 11⟩
  | 10, 2 => some ⟨0, Dir.R, some 12⟩
  | 10, 3 => some ⟨3, Dir.L, some 7⟩
  | 10, 4 => some ⟨0, Dir.L, some 8⟩
  | 10, 5 => some ⟨5, Dir.L, some 13⟩
  | 10, 6 => some ⟨7, Dir.L, some 10⟩
  | 10, 7 => some ⟨0, Dir.L, some 13⟩
  | 11, 0 => some ⟨0, Dir.R, some 11⟩
  | 11, 1 => some ⟨0, Dir.L, some 12⟩
  | 11, 2 => some ⟨2, Dir.L, some 13⟩
  | 11, 3 => some ⟨1, Dir.R, some 14⟩
  | 11, 4 => some ⟨4, Dir.R, some 12⟩
  | 11, 5 => some ⟨0, Dir.L, some 14⟩
  | 11, 6 => some ⟨2, Dir.R, some 13⟩
  | 11, 7 => some ⟨4, Dir.L, some 0⟩
  | 12, 0 => some ⟨1, Dir.R, some 2⟩
  | 12, 1 => some ⟨1, Dir.L, some 14⟩
  | 12, 2 => some ⟨1, Dir.L, some 11⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.L, some 3⟩
  | 12, 5 => some ⟨3, Dir.R, some 5⟩
  | 12, 6 => some ⟨3, Dir.L, some 6⟩
  | 12, 7 => some ⟨0, Dir.L, some 4⟩
  | 13, 0 => some ⟨0, Dir.R, some 13⟩
  | 13, 1 => some ⟨0, Dir.L, some 14⟩
  | 13, 2 => some ⟨2, Dir.L, some 14⟩
  | 13, 3 => some ⟨3, Dir.L, some 14⟩
  | 13, 4 => some ⟨2, Dir.R, some 12⟩
  | 13, 5 => some ⟨5, Dir.L, some 14⟩
  | 13, 6 => some ⟨3, Dir.L, some 11⟩
  | 13, 7 => some ⟨4, Dir.L, some 11⟩
  | 14, 0 => some ⟨1, Dir.R, some 12⟩
  | 14, 1 => some ⟨1, Dir.L, some 7⟩
  | 14, 2 => some ⟨3, Dir.L, some 7⟩
  | 14, 3 => some ⟨2, Dir.R, some 3⟩
  | 14, 4 => some ⟨4, Dir.R, some 6⟩
  | 14, 5 => some ⟨0, Dir.L, some 7⟩
  | 14, 6 => some ⟨0, Dir.L, some 10⟩
  | 14, 7 => some ⟨3, Dir.L, some 7⟩
  | _, _ => none

theorem valid_15_8 : ValidTM 15 8 tm_15_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | _ + 8 => omega
    | 1 =>
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
    | 6 =>
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
    | 7 =>
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
    | 8 =>
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
    | 9 =>
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
    | 10 =>
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
    | 11 =>
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
    | 12 =>
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
    | 13 =>
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
    | 14 =>
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
    | _ + 15 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 15 => rfl

def landmark_15_8 : Config := { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 1, 0, 0, 3] }
set_option maxHeartbeats 800000 in
theorem reaches_landmark_15_8 : steps tm_15_8 19925 initConfig = some landmark_15_8 := by
  have h0 : steps tm_15_8 35 initConfig = some { st := some 1, left := [], cur := 0, right := [7, 7, 3, 2, 1] } := rfl
  have hstep1 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [7, 7, 3, 2, 1] } = some { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1] } := rfl
  have h1 : steps tm_15_8 70 initConfig = some { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1] } := steps_add tm_15_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_15_8 35 { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1] } = some { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1] } := rfl
  have h2 : steps tm_15_8 105 initConfig = some { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1] } := steps_add tm_15_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1] } = some { st := some 11, left := [], cur := 1, right := [] } := rfl
  have h3 : steps tm_15_8 140 initConfig = some { st := some 11, left := [], cur := 1, right := [] } := steps_add tm_15_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_15_8 35 { st := some 11, left := [], cur := 1, right := [] } = some { st := some 12, left := [1], cur := 1, right := [] } := rfl
  have h4 : steps tm_15_8 175 initConfig = some { st := some 12, left := [1], cur := 1, right := [] } := steps_add tm_15_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_15_8 35 { st := some 12, left := [1], cur := 1, right := [] } = some { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 0, 1, 1] } := rfl
  have h5 : steps tm_15_8 210 initConfig = some { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_15_8 35 { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 0, 1, 1] } = some { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h6 : steps tm_15_8 245 initConfig = some { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h7 : steps tm_15_8 280 initConfig = some { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_15_8 35 { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h8 : steps tm_15_8 315 initConfig = some { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 8, left := [], cur := 1, right := [0, 1, 3] } := rfl
  have h9 : steps tm_15_8 350 initConfig = some { st := some 8, left := [], cur := 1, right := [0, 1, 3] } := steps_add tm_15_8 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_15_8 35 { st := some 8, left := [], cur := 1, right := [0, 1, 3] } = some { st := some 7, left := [7, 3, 3, 3, 1], cur := 0, right := [] } := rfl
  have h10 : steps tm_15_8 385 initConfig = some { st := some 7, left := [7, 3, 3, 3, 1], cur := 0, right := [] } := steps_add tm_15_8 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_15_8 35 { st := some 7, left := [7, 3, 3, 3, 1], cur := 0, right := [] } = some { st := some 0, left := [6, 5, 5, 7], cur := 6, right := [] } := rfl
  have h11 : steps tm_15_8 420 initConfig = some { st := some 0, left := [6, 5, 5, 7], cur := 6, right := [] } := steps_add tm_15_8 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_15_8 35 { st := some 0, left := [6, 5, 5, 7], cur := 6, right := [] } = some { st := some 0, left := [2, 1], cur := 1, right := [] } := rfl
  have h12 : steps tm_15_8 455 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [] } := steps_add tm_15_8 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_15_8 35 { st := some 0, left := [2, 1], cur := 1, right := [] } = some { st := some 4, left := [7], cur := 1, right := [1, 0, 0, 0, 0, 0, 3] } := rfl
  have h13 : steps tm_15_8 490 initConfig = some { st := some 4, left := [7], cur := 1, right := [1, 0, 0, 0, 0, 0, 3] } := steps_add tm_15_8 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_15_8 35 { st := some 4, left := [7], cur := 1, right := [1, 0, 0, 0, 0, 0, 3] } = some { st := some 4, left := [], cur := 7, right := [0, 0, 0, 1, 0, 1, 0, 0, 0, 3] } := rfl
  have h14 : steps tm_15_8 525 initConfig = some { st := some 4, left := [], cur := 7, right := [0, 0, 0, 1, 0, 1, 0, 0, 0, 3] } := steps_add tm_15_8 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_15_8 35 { st := some 4, left := [], cur := 7, right := [0, 0, 0, 1, 0, 1, 0, 0, 0, 3] } = some { st := some 2, left := [], cur := 7, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } := rfl
  have h15 : steps tm_15_8 560 initConfig = some { st := some 2, left := [], cur := 7, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } := steps_add tm_15_8 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_15_8 35 { st := some 2, left := [], cur := 7, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } := rfl
  have h16 : steps tm_15_8 595 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } := steps_add tm_15_8 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3] } = some { st := some 7, left := [6, 7, 3, 1, 1], cur := 0, right := [] } := rfl
  have h17 : steps tm_15_8 630 initConfig = some { st := some 7, left := [6, 7, 3, 1, 1], cur := 0, right := [] } := steps_add tm_15_8 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_15_8 35 { st := some 7, left := [6, 7, 3, 1, 1], cur := 0, right := [] } = some { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 4, 1] } := rfl
  have h18 : steps tm_15_8 665 initConfig = some { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 4, 1] } := steps_add tm_15_8 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_15_8 35 { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 4, 1] } = some { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 4, 1] } := rfl
  have h19 : steps tm_15_8 700 initConfig = some { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 4, 1] } := steps_add tm_15_8 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_15_8 35 { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 4, 1] } = some { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 4, 1] } := rfl
  have h20 : steps tm_15_8 735 initConfig = some { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 4, 1] } := steps_add tm_15_8 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_15_8 35 { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 4, 1] } = some { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 4, 1] } := rfl
  have h21 : steps tm_15_8 770 initConfig = some { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 4, 1] } := steps_add tm_15_8 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 4, 1] } = some { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 4, 0, 1] } := rfl
  have h22 : steps tm_15_8 805 initConfig = some { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 4, 0, 1] } := steps_add tm_15_8 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_15_8 35 { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 4, 0, 1] } = some { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := rfl
  have h23 : steps tm_15_8 840 initConfig = some { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := steps_add tm_15_8 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_15_8 35 { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 4, 0, 1] } = some { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := rfl
  have h24 : steps tm_15_8 875 initConfig = some { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := steps_add tm_15_8 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_15_8 35 { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } = some { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := rfl
  have h25 : steps tm_15_8 910 initConfig = some { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } := steps_add tm_15_8 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_15_8 35 { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1] } = some { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 4, 0, 1] } := rfl
  have h26 : steps tm_15_8 945 initConfig = some { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 4, 0, 1] } := steps_add tm_15_8 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_15_8 35 { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 4, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 3, 2, 4, 1, 1] } := rfl
  have h27 : steps tm_15_8 980 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 3, 2, 4, 1, 1] } := steps_add tm_15_8 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 3, 2, 4, 1, 1] } = some { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 2, 4, 1, 1] } := rfl
  have h28 : steps tm_15_8 1015 initConfig = some { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 2, 4, 1, 1] } := steps_add tm_15_8 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_15_8 35 { st := some 3, left := [7, 7], cur := 7, right := [2, 1, 0, 0, 2, 4, 1, 1] } = some { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } := rfl
  have h29 : steps tm_15_8 1050 initConfig = some { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } := steps_add tm_15_8 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [3, 2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } = some { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } := rfl
  have h30 : steps tm_15_8 1085 initConfig = some { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } := steps_add tm_15_8 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_15_8 35 { st := some 3, left := [5, 7], cur := 6, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1] } = some { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 2, 4, 1, 1] } := rfl
  have h31 : steps tm_15_8 1120 initConfig = some { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 2, 4, 1, 1] } := steps_add tm_15_8 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [0, 0, 1, 0, 0, 2, 4, 1, 1] } = some { st := some 11, left := [], cur := 0, right := [1, 4, 1, 1] } := rfl
  have h32 : steps tm_15_8 1155 initConfig = some { st := some 11, left := [], cur := 0, right := [1, 4, 1, 1] } := steps_add tm_15_8 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [1, 4, 1, 1] } = some { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 0, 3, 1, 1] } := rfl
  have h33 : steps tm_15_8 1190 initConfig = some { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 0, 3, 1, 1] } := steps_add tm_15_8 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_15_8 35 { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 0, 3, 1, 1] } = some { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := rfl
  have h34 : steps tm_15_8 1225 initConfig = some { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := steps_add tm_15_8 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_15_8 35 { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 0, 3, 1, 1] } = some { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := rfl
  have h35 : steps tm_15_8 1260 initConfig = some { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := steps_add tm_15_8 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_15_8 35 { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } = some { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := rfl
  have h36 : steps tm_15_8 1295 initConfig = some { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } := steps_add tm_15_8 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_15_8 35 { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1] } = some { st := some 13, left := [], cur := 0, right := [0, 1, 0, 0, 3, 1, 1] } := rfl
  have h37 : steps tm_15_8 1330 initConfig = some { st := some 13, left := [], cur := 0, right := [0, 1, 0, 0, 3, 1, 1] } := steps_add tm_15_8 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_15_8 35 { st := some 13, left := [], cur := 0, right := [0, 1, 0, 0, 3, 1, 1] } = some { st := some 1, left := [7, 2, 1], cur := 6, right := [1] } := rfl
  have h38 : steps tm_15_8 1365 initConfig = some { st := some 1, left := [7, 2, 1], cur := 6, right := [1] } := steps_add tm_15_8 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_15_8 35 { st := some 1, left := [7, 2, 1], cur := 6, right := [1] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 0, 3, 2, 1] } := rfl
  have h39 : steps tm_15_8 1400 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 0, 3, 2, 1] } := steps_add tm_15_8 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_15_8 35 { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 0, 3, 2, 1] } = some { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := rfl
  have h40 : steps tm_15_8 1435 initConfig = some { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := steps_add tm_15_8 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_15_8 35 { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } = some { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := rfl
  have h41 : steps tm_15_8 1470 initConfig = some { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := steps_add tm_15_8 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_15_8 35 { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := rfl
  have h42 : steps tm_15_8 1505 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } := steps_add tm_15_8 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1] } = some { st := some 7, left := [7, 3, 1, 1], cur := 3, right := [2, 1] } := rfl
  have h43 : steps tm_15_8 1540 initConfig = some { st := some 7, left := [7, 3, 1, 1], cur := 3, right := [2, 1] } := steps_add tm_15_8 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_15_8 35 { st := some 7, left := [7, 3, 1, 1], cur := 3, right := [2, 1] } = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 4, 1, 0, 0, 1] } := rfl
  have h44 : steps tm_15_8 1575 initConfig = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_15_8 35 { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 4, 1, 0, 0, 1] } = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := rfl
  have h45 : steps tm_15_8 1610 initConfig = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_15_8 35 { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := rfl
  have h46 : steps tm_15_8 1645 initConfig = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_15_8 35 { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := rfl
  have h47 : steps tm_15_8 1680 initConfig = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1] } = some { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } := rfl
  have h48 : steps tm_15_8 1715 initConfig = some { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } := steps_add tm_15_8 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_15_8 35 { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } = some { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := rfl
  have h49 : steps tm_15_8 1750 initConfig = some { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := steps_add tm_15_8 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_15_8 35 { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } = some { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := rfl
  have h50 : steps tm_15_8 1785 initConfig = some { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := steps_add tm_15_8 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_15_8 35 { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } = some { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := rfl
  have h51 : steps tm_15_8 1820 initConfig = some { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } := steps_add tm_15_8 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_15_8 35 { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1] } = some { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } := rfl
  have h52 : steps tm_15_8 1855 initConfig = some { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } := steps_add tm_15_8 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_15_8 35 { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 4, 0, 1, 0, 1] } = some { st := some 8, left := [], cur := 0, right := [0, 3, 2, 4, 1, 1, 0, 1] } := rfl
  have h53 : steps tm_15_8 1890 initConfig = some { st := some 8, left := [], cur := 0, right := [0, 3, 2, 4, 1, 1, 0, 1] } := steps_add tm_15_8 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_15_8 35 { st := some 8, left := [], cur := 0, right := [0, 3, 2, 4, 1, 1, 0, 1] } = some { st := some 1, left := [7, 7, 7], cur := 6, right := [1, 0, 0, 2, 4, 1, 1, 0, 1] } := rfl
  have h54 : steps tm_15_8 1925 initConfig = some { st := some 1, left := [7, 7, 7], cur := 6, right := [1, 0, 0, 2, 4, 1, 1, 0, 1] } := steps_add tm_15_8 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_15_8 35 { st := some 1, left := [7, 7, 7], cur := 6, right := [1, 0, 0, 2, 4, 1, 1, 0, 1] } = some { st := some 3, left := [], cur := 7, right := [2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := rfl
  have h55 : steps tm_15_8 1960 initConfig = some { st := some 3, left := [], cur := 7, right := [2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := steps_add tm_15_8 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_15_8 35 { st := some 3, left := [], cur := 7, right := [2, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } = some { st := some 1, left := [6, 5, 7], cur := 6, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := rfl
  have h56 : steps tm_15_8 1995 initConfig = some { st := some 1, left := [6, 5, 7], cur := 6, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := steps_add tm_15_8 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_15_8 35 { st := some 1, left := [6, 5, 7], cur := 6, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } = some { st := some 10, left := [], cur := 1, right := [0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := rfl
  have h57 : steps tm_15_8 2030 initConfig = some { st := some 10, left := [], cur := 1, right := [0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } := steps_add tm_15_8 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_15_8 35 { st := some 10, left := [], cur := 1, right := [0, 1, 0, 0, 2, 4, 1, 1, 0, 1] } = some { st := some 11, left := [], cur := 0, right := [0, 1, 4, 1, 1, 0, 1] } := rfl
  have h58 : steps tm_15_8 2065 initConfig = some { st := some 11, left := [], cur := 0, right := [0, 1, 4, 1, 1, 0, 1] } := steps_add tm_15_8 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [0, 1, 4, 1, 1, 0, 1] } = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1] } := rfl
  have h59 : steps tm_15_8 2100 initConfig = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1] } := steps_add tm_15_8 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_15_8 35 { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1] } = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := rfl
  have h60 : steps tm_15_8 2135 initConfig = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := steps_add tm_15_8 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_15_8 35 { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := rfl
  have h61 : steps tm_15_8 2170 initConfig = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := steps_add tm_15_8 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_15_8 35 { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := rfl
  have h62 : steps tm_15_8 2205 initConfig = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } := steps_add tm_15_8 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_15_8 35 { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1] } = some { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 1, 1, 0, 1] } := rfl
  have h63 : steps tm_15_8 2240 initConfig = some { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 1, 1, 0, 1] } := steps_add tm_15_8 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_15_8 35 { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 1, 1, 0, 1] } = some { st := some 1, left := [3, 7, 2, 1], cur := 7, right := [] } := rfl
  have h64 : steps tm_15_8 2275 initConfig = some { st := some 1, left := [3, 7, 2, 1], cur := 7, right := [] } := steps_add tm_15_8 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_15_8 35 { st := some 1, left := [3, 7, 2, 1], cur := 7, right := [] } = some { st := some 3, left := [1], cur := 0, right := [1, 1, 1] } := rfl
  have h65 : steps tm_15_8 2310 initConfig = some { st := some 3, left := [1], cur := 0, right := [1, 1, 1] } := steps_add tm_15_8 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_15_8 35 { st := some 3, left := [1], cur := 0, right := [1, 1, 1] } = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 2, 1] } := rfl
  have h66 : steps tm_15_8 2345 initConfig = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 2, 1] } := steps_add tm_15_8 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_15_8 35 { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 2, 1] } = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 2, 1] } := rfl
  have h67 : steps tm_15_8 2380 initConfig = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 2, 1] } := steps_add tm_15_8 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_15_8 35 { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 2, 1] } = some { st := some 4, left := [3, 7], cur := 3, right := [0, 0, 0, 1] } := rfl
  have h68 : steps tm_15_8 2415 initConfig = some { st := some 4, left := [3, 7], cur := 3, right := [0, 0, 0, 1] } := steps_add tm_15_8 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_15_8 35 { st := some 4, left := [3, 7], cur := 3, right := [0, 0, 0, 1] } = some { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 4, 1, 0, 0, 1] } := rfl
  have h69 : steps tm_15_8 2450 initConfig = some { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_15_8 35 { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 4, 1, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 4, 1, 0, 0, 1] } := rfl
  have h70 : steps tm_15_8 2485 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 4, 1, 0, 0, 1] } := steps_add tm_15_8 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 4, 1, 0, 0, 1] } = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 0, 3, 0, 0, 0, 1] } := rfl
  have h71 : steps tm_15_8 2520 initConfig = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 0, 3, 0, 0, 0, 1] } := steps_add tm_15_8 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_15_8 35 { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 0, 3, 0, 0, 0, 1] } = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := rfl
  have h72 : steps tm_15_8 2555 initConfig = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := steps_add tm_15_8 2520 35 initConfig _ _ h71 hstep72
  have hstep73 : steps tm_15_8 35 { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := rfl
  have h73 : steps tm_15_8 2590 initConfig = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := steps_add tm_15_8 2555 35 initConfig _ _ h72 hstep73
  have hstep74 : steps tm_15_8 35 { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := rfl
  have h74 : steps tm_15_8 2625 initConfig = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } := steps_add tm_15_8 2590 35 initConfig _ _ h73 hstep74
  have hstep75 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1] } = some { st := some 5, left := [1], cur := 1, right := [4, 1, 0, 0, 0, 0, 1] } := rfl
  have h75 : steps tm_15_8 2660 initConfig = some { st := some 5, left := [1], cur := 1, right := [4, 1, 0, 0, 0, 0, 1] } := steps_add tm_15_8 2625 35 initConfig _ _ h74 hstep75
  have hstep76 : steps tm_15_8 35 { st := some 5, left := [1], cur := 1, right := [4, 1, 0, 0, 0, 0, 1] } = some { st := some 7, left := [7], cur := 7, right := [7, 3, 2, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := rfl
  have h76 : steps tm_15_8 2695 initConfig = some { st := some 7, left := [7], cur := 7, right := [7, 3, 2, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := steps_add tm_15_8 2660 35 initConfig _ _ h75 hstep76
  have hstep77 : steps tm_15_8 35 { st := some 7, left := [7], cur := 7, right := [7, 3, 2, 1, 0, 4, 1, 0, 0, 0, 0, 1] } = some { st := some 6, left := [], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := rfl
  have h77 : steps tm_15_8 2730 initConfig = some { st := some 6, left := [], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := steps_add tm_15_8 2695 35 initConfig _ _ h76 hstep77
  have hstep78 : steps tm_15_8 35 { st := some 6, left := [], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } = some { st := some 7, left := [7], cur := 3, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := rfl
  have h78 : steps tm_15_8 2765 initConfig = some { st := some 7, left := [7], cur := 3, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } := steps_add tm_15_8 2730 35 initConfig _ _ h77 hstep78
  have hstep79 : steps tm_15_8 35 { st := some 7, left := [7], cur := 3, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1] } = some { st := some 12, left := [], cur := 0, right := [0, 0, 4, 1, 0, 0, 0, 0, 1] } := rfl
  have h79 : steps tm_15_8 2800 initConfig = some { st := some 12, left := [], cur := 0, right := [0, 0, 4, 1, 0, 0, 0, 0, 1] } := steps_add tm_15_8 2765 35 initConfig _ _ h78 hstep79
  have hstep80 : steps tm_15_8 35 { st := some 12, left := [], cur := 0, right := [0, 0, 4, 1, 0, 0, 0, 0, 1] } = some { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := rfl
  have h80 : steps tm_15_8 2835 initConfig = some { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2800 35 initConfig _ _ h79 hstep80
  have hstep81 : steps tm_15_8 35 { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := rfl
  have h81 : steps tm_15_8 2870 initConfig = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2835 35 initConfig _ _ h80 hstep81
  have hstep82 : steps tm_15_8 35 { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := rfl
  have h82 : steps tm_15_8 2905 initConfig = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2870 35 initConfig _ _ h81 hstep82
  have hstep83 : steps tm_15_8 35 { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := rfl
  have h83 : steps tm_15_8 2940 initConfig = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2905 35 initConfig _ _ h82 hstep83
  have hstep84 : steps tm_15_8 35 { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := rfl
  have h84 : steps tm_15_8 2975 initConfig = some { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2940 35 initConfig _ _ h83 hstep84
  have hstep85 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1] } = some { st := some 0, left := [], cur := 7, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } := rfl
  have h85 : steps tm_15_8 3010 initConfig = some { st := some 0, left := [], cur := 7, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 2975 35 initConfig _ _ h84 hstep85
  have hstep86 : steps tm_15_8 35 { st := some 0, left := [], cur := 7, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } = some { st := some 7, left := [7, 7, 7], cur := 3, right := [2, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := rfl
  have h86 : steps tm_15_8 3045 initConfig = some { st := some 7, left := [7, 7, 7], cur := 3, right := [2, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3010 35 initConfig _ _ h85 hstep86
  have hstep87 : steps tm_15_8 35 { st := some 7, left := [7, 7, 7], cur := 3, right := [2, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } = some { st := some 1, left := [3], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := rfl
  have h87 : steps tm_15_8 3080 initConfig = some { st := some 1, left := [3], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3045 35 initConfig _ _ h86 hstep87
  have hstep88 : steps tm_15_8 35 { st := some 1, left := [3], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } = some { st := some 7, left := [5, 6, 7], cur := 3, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := rfl
  have h88 : steps tm_15_8 3115 initConfig = some { st := some 7, left := [5, 6, 7], cur := 3, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3080 35 initConfig _ _ h87 hstep88
  have hstep89 : steps tm_15_8 35 { st := some 7, left := [5, 6, 7], cur := 3, right := [2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1] } = some { st := some 1, left := [3, 1], cur := 0, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } := rfl
  have h89 : steps tm_15_8 3150 initConfig = some { st := some 1, left := [3, 1], cur := 0, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3115 35 initConfig _ _ h88 hstep89
  have hstep90 : steps tm_15_8 35 { st := some 1, left := [3, 1], cur := 0, right := [0, 2, 4, 1, 1, 0, 0, 0, 1] } = some { st := some 5, left := [6, 1], cur := 4, right := [1, 1, 0, 0, 0, 1] } := rfl
  have h90 : steps tm_15_8 3185 initConfig = some { st := some 5, left := [6, 1], cur := 4, right := [1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3150 35 initConfig _ _ h89 hstep90
  have hstep91 : steps tm_15_8 35 { st := some 5, left := [6, 1], cur := 4, right := [1, 1, 0, 0, 0, 1] } = some { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := rfl
  have h91 : steps tm_15_8 3220 initConfig = some { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3185 35 initConfig _ _ h90 hstep91
  have hstep92 : steps tm_15_8 35 { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } = some { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := rfl
  have h92 : steps tm_15_8 3255 initConfig = some { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3220 35 initConfig _ _ h91 hstep92
  have hstep93 : steps tm_15_8 35 { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } = some { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := rfl
  have h93 : steps tm_15_8 3290 initConfig = some { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3255 35 initConfig _ _ h92 hstep93
  have hstep94 : steps tm_15_8 35 { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := rfl
  have h94 : steps tm_15_8 3325 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3290 35 initConfig _ _ h93 hstep94
  have hstep95 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1] } = some { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 1, 1, 0, 0, 0, 1] } := rfl
  have h95 : steps tm_15_8 3360 initConfig = some { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 1, 1, 0, 0, 0, 1] } := steps_add tm_15_8 3325 35 initConfig _ _ h94 hstep95
  have hstep96 : steps tm_15_8 35 { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 1, 1, 0, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 1, 3, 2, 1, 0, 0, 1] } := rfl
  have h96 : steps tm_15_8 3395 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 1, 3, 2, 1, 0, 0, 1] } := steps_add tm_15_8 3360 35 initConfig _ _ h95 hstep96
  have hstep97 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 1, 3, 2, 1, 0, 0, 1] } = some { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 0, 0, 3, 2, 1, 0, 0, 1] } := rfl
  have h97 : steps tm_15_8 3430 initConfig = some { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 0, 0, 3, 2, 1, 0, 0, 1] } := steps_add tm_15_8 3395 35 initConfig _ _ h96 hstep97
  have hstep98 : steps tm_15_8 35 { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 0, 0, 3, 2, 1, 0, 0, 1] } = some { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := rfl
  have h98 : steps tm_15_8 3465 initConfig = some { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := steps_add tm_15_8 3430 35 initConfig _ _ h97 hstep98
  have hstep99 : steps tm_15_8 35 { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } = some { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := rfl
  have h99 : steps tm_15_8 3500 initConfig = some { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := steps_add tm_15_8 3465 35 initConfig _ _ h98 hstep99
  have hstep100 : steps tm_15_8 35 { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } = some { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := rfl
  have h100 : steps tm_15_8 3535 initConfig = some { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } := steps_add tm_15_8 3500 35 initConfig _ _ h99 hstep100
  have hstep101 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1] } = some { st := some 1, left := [1, 1], cur := 4, right := [1, 0, 0, 1, 0, 0, 1] } := rfl
  have h101 : steps tm_15_8 3570 initConfig = some { st := some 1, left := [1, 1], cur := 4, right := [1, 0, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3535 35 initConfig _ _ h100 hstep101
  have hstep102 : steps tm_15_8 35 { st := some 1, left := [1, 1], cur := 4, right := [1, 0, 0, 1, 0, 0, 1] } = some { st := some 1, left := [], cur := 0, right := [7, 7, 3, 2, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := rfl
  have h102 : steps tm_15_8 3605 initConfig = some { st := some 1, left := [], cur := 0, right := [7, 7, 3, 2, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3570 35 initConfig _ _ h101 hstep102
  have hstep103 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [7, 7, 3, 2, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } = some { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := rfl
  have h103 : steps tm_15_8 3640 initConfig = some { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3605 35 initConfig _ _ h102 hstep103
  have hstep104 : steps tm_15_8 35 { st := some 0, left := [7], cur := 6, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } = some { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := rfl
  have h104 : steps tm_15_8 3675 initConfig = some { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3640 35 initConfig _ _ h103 hstep104
  have hstep105 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [3, 1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1] } = some { st := some 11, left := [], cur := 1, right := [0, 4, 1, 0, 0, 1, 0, 0, 1] } := rfl
  have h105 : steps tm_15_8 3710 initConfig = some { st := some 11, left := [], cur := 1, right := [0, 4, 1, 0, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3675 35 initConfig _ _ h104 hstep105
  have hstep106 : steps tm_15_8 35 { st := some 11, left := [], cur := 1, right := [0, 4, 1, 0, 0, 1, 0, 0, 1] } = some { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := rfl
  have h106 : steps tm_15_8 3745 initConfig = some { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3710 35 initConfig _ _ h105 hstep106
  have hstep107 : steps tm_15_8 35 { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } = some { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := rfl
  have h107 : steps tm_15_8 3780 initConfig = some { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3745 35 initConfig _ _ h106 hstep107
  have hstep108 : steps tm_15_8 35 { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := rfl
  have h108 : steps tm_15_8 3815 initConfig = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3780 35 initConfig _ _ h107 hstep108
  have hstep109 : steps tm_15_8 35 { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := rfl
  have h109 : steps tm_15_8 3850 initConfig = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3815 35 initConfig _ _ h108 hstep109
  have hstep110 : steps tm_15_8 35 { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := rfl
  have h110 : steps tm_15_8 3885 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3850 35 initConfig _ _ h109 hstep110
  have hstep111 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1] } = some { st := some 7, left := [7], cur := 0, right := [2, 4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h111 : steps tm_15_8 3920 initConfig = some { st := some 7, left := [7], cur := 0, right := [2, 4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3885 35 initConfig _ _ h110 hstep111
  have hstep112 : steps tm_15_8 35 { st := some 7, left := [7], cur := 0, right := [2, 4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 7, left := [7, 7], cur := 7, right := [3, 2, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h112 : steps tm_15_8 3955 initConfig = some { st := some 7, left := [7, 7], cur := 7, right := [3, 2, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3920 35 initConfig _ _ h111 hstep112
  have hstep113 : steps tm_15_8 35 { st := some 7, left := [7, 7], cur := 7, right := [3, 2, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 4, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h113 : steps tm_15_8 3990 initConfig = some { st := some 4, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3955 35 initConfig _ _ h112 hstep113
  have hstep114 : steps tm_15_8 35 { st := some 4, left := [], cur := 0, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 7, left := [6, 7], cur := 1, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h114 : steps tm_15_8 4025 initConfig = some { st := some 7, left := [6, 7], cur := 1, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 3990 35 initConfig _ _ h113 hstep114
  have hstep115 : steps tm_15_8 35 { st := some 7, left := [6, 7], cur := 1, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 2, left := [1], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h115 : steps tm_15_8 4060 initConfig = some { st := some 2, left := [1], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4025 35 initConfig _ _ h114 hstep115
  have hstep116 : steps tm_15_8 35 { st := some 2, left := [1], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 5, left := [1], cur := 3, right := [4, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h116 : steps tm_15_8 4095 initConfig = some { st := some 5, left := [1], cur := 3, right := [4, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4060 35 initConfig _ _ h115 hstep116
  have hstep117 : steps tm_15_8 35 { st := some 5, left := [1], cur := 3, right := [4, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h117 : steps tm_15_8 4130 initConfig = some { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4095 35 initConfig _ _ h116 hstep117
  have hstep118 : steps tm_15_8 35 { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h118 : steps tm_15_8 4165 initConfig = some { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4130 35 initConfig _ _ h117 hstep118
  have hstep119 : steps tm_15_8 35 { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h119 : steps tm_15_8 4200 initConfig = some { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4165 35 initConfig _ _ h118 hstep119
  have hstep120 : steps tm_15_8 35 { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h120 : steps tm_15_8 4235 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4200 35 initConfig _ _ h119 hstep120
  have hstep121 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 1, 1, 0, 1, 0, 0, 1] } := rfl
  have h121 : steps tm_15_8 4270 initConfig = some { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 1, 1, 0, 1, 0, 0, 1] } := steps_add tm_15_8 4235 35 initConfig _ _ h120 hstep121
  have hstep122 : steps tm_15_8 35 { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 1, 1, 0, 1, 0, 0, 1] } = some { st := some 3, left := [], cur := 1, right := [1, 7, 3, 0, 0, 0, 0, 1] } := rfl
  have h122 : steps tm_15_8 4305 initConfig = some { st := some 3, left := [], cur := 1, right := [1, 7, 3, 0, 0, 0, 0, 1] } := steps_add tm_15_8 4270 35 initConfig _ _ h121 hstep122
  have hstep123 : steps tm_15_8 35 { st := some 3, left := [], cur := 1, right := [1, 7, 3, 0, 0, 0, 0, 1] } = some { st := some 1, left := [3, 3, 7, 7, 7, 7, 1], cur := 0, right := [] } := rfl
  have h123 : steps tm_15_8 4340 initConfig = some { st := some 1, left := [3, 3, 7, 7, 7, 7, 1], cur := 0, right := [] } := steps_add tm_15_8 4305 35 initConfig _ _ h122 hstep123
  have hstep124 : steps tm_15_8 35 { st := some 1, left := [3, 3, 7, 7, 7, 7, 1], cur := 0, right := [] } = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 7, 7, 1, 3, 3, 1] } := rfl
  have h124 : steps tm_15_8 4375 initConfig = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 7, 7, 1, 3, 3, 1] } := steps_add tm_15_8 4340 35 initConfig _ _ h123 hstep124
  have hstep125 : steps tm_15_8 35 { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 7, 7, 1, 3, 3, 1] } = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1] } := rfl
  have h125 : steps tm_15_8 4410 initConfig = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1] } := steps_add tm_15_8 4375 35 initConfig _ _ h124 hstep125
  have hstep126 : steps tm_15_8 35 { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1] } = some { st := some 1, left := [6, 5, 7, 3, 3, 7], cur := 6, right := [] } := rfl
  have h126 : steps tm_15_8 4445 initConfig = some { st := some 1, left := [6, 5, 7, 3, 3, 7], cur := 6, right := [] } := steps_add tm_15_8 4410 35 initConfig _ _ h125 hstep126
  have hstep127 : steps tm_15_8 35 { st := some 1, left := [6, 5, 7, 3, 3, 7], cur := 6, right := [] } = some { st := some 1, left := [], cur := 0, right := [1, 0, 0, 4] } := rfl
  have h127 : steps tm_15_8 4480 initConfig = some { st := some 1, left := [], cur := 0, right := [1, 0, 0, 4] } := steps_add tm_15_8 4445 35 initConfig _ _ h126 hstep127
  have hstep128 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [1, 0, 0, 4] } = some { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 4] } := rfl
  have h128 : steps tm_15_8 4515 initConfig = some { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 4] } := steps_add tm_15_8 4480 35 initConfig _ _ h127 hstep128
  have hstep129 : steps tm_15_8 35 { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 4] } = some { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } := rfl
  have h129 : steps tm_15_8 4550 initConfig = some { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } := steps_add tm_15_8 4515 35 initConfig _ _ h128 hstep129
  have hstep130 : steps tm_15_8 35 { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } = some { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } := rfl
  have h130 : steps tm_15_8 4585 initConfig = some { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } := steps_add tm_15_8 4550 35 initConfig _ _ h129 hstep130
  have hstep131 : steps tm_15_8 35 { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4] } = some { st := some 0, left := [3, 1], cur := 7, right := [0, 4] } := rfl
  have h131 : steps tm_15_8 4620 initConfig = some { st := some 0, left := [3, 1], cur := 7, right := [0, 4] } := steps_add tm_15_8 4585 35 initConfig _ _ h130 hstep131
  have hstep132 : steps tm_15_8 35 { st := some 0, left := [3, 1], cur := 7, right := [0, 4] } = some { st := some 7, left := [7, 3, 1, 4], cur := 0, right := [] } := rfl
  have h132 : steps tm_15_8 4655 initConfig = some { st := some 7, left := [7, 3, 1, 4], cur := 0, right := [] } := steps_add tm_15_8 4620 35 initConfig _ _ h131 hstep132
  have hstep133 : steps tm_15_8 35 { st := some 7, left := [7, 3, 1, 4], cur := 0, right := [] } = some { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := rfl
  have h133 : steps tm_15_8 4690 initConfig = some { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4655 35 initConfig _ _ h132 hstep133
  have hstep134 : steps tm_15_8 35 { st := some 1, left := [], cur := 2, right := [1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 1] } = some { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := rfl
  have h134 : steps tm_15_8 4725 initConfig = some { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4690 35 initConfig _ _ h133 hstep134
  have hstep135 : steps tm_15_8 35 { st := some 0, left := [7, 7], cur := 6, right := [0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } = some { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := rfl
  have h135 : steps tm_15_8 4760 initConfig = some { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4725 35 initConfig _ _ h134 hstep135
  have hstep136 : steps tm_15_8 35 { st := some 2, left := [2, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := rfl
  have h136 : steps tm_15_8 4795 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4760 35 initConfig _ _ h135 hstep136
  have hstep137 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 1] } = some { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 0, 0, 0, 2, 1] } := rfl
  have h137 : steps tm_15_8 4830 initConfig = some { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4795 35 initConfig _ _ h136 hstep137
  have hstep138 : steps tm_15_8 35 { st := some 1, left := [3, 1, 1], cur := 0, right := [3, 0, 0, 0, 2, 1] } = some { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 4, 1, 0, 0, 0, 0, 2, 1] } := rfl
  have h138 : steps tm_15_8 4865 initConfig = some { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 4, 1, 0, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4830 35 initConfig _ _ h137 hstep138
  have hstep139 : steps tm_15_8 35 { st := some 0, left := [3, 7, 7, 7], cur := 7, right := [0, 4, 1, 0, 0, 0, 0, 2, 1] } = some { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := rfl
  have h139 : steps tm_15_8 4900 initConfig = some { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4865 35 initConfig _ _ h138 hstep139
  have hstep140 : steps tm_15_8 35 { st := some 5, left := [7], cur := 3, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } = some { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := rfl
  have h140 : steps tm_15_8 4935 initConfig = some { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4900 35 initConfig _ _ h139 hstep140
  have hstep141 : steps tm_15_8 35 { st := some 7, left := [6, 6, 5, 7], cur := 1, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := rfl
  have h141 : steps tm_15_8 4970 initConfig = some { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4935 35 initConfig _ _ h140 hstep141
  have hstep142 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 2, 1] } = some { st := some 1, left := [], cur := 0, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := rfl
  have h142 : steps tm_15_8 5005 initConfig = some { st := some 1, left := [], cur := 0, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 4970 35 initConfig _ _ h141 hstep142
  have hstep143 : steps tm_15_8 35 { st := some 1, left := [], cur := 0, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := rfl
  have h143 : steps tm_15_8 5040 initConfig = some { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5005 35 initConfig _ _ h142 hstep143
  have hstep144 : steps tm_15_8 35 { st := some 0, left := [7, 7, 7], cur := 6, right := [0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := rfl
  have h144 : steps tm_15_8 5075 initConfig = some { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5040 35 initConfig _ _ h143 hstep144
  have hstep145 : steps tm_15_8 35 { st := some 0, left := [3], cur := 7, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := rfl
  have h145 : steps tm_15_8 5110 initConfig = some { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5075 35 initConfig _ _ h144 hstep145
  have hstep146 : steps tm_15_8 35 { st := some 0, left := [5, 6, 7], cur := 6, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [3, 1], cur := 7, right := [0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := rfl
  have h146 : steps tm_15_8 5145 initConfig = some { st := some 0, left := [3, 1], cur := 7, right := [0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5110 35 initConfig _ _ h145 hstep146
  have hstep147 : steps tm_15_8 35 { st := some 0, left := [3, 1], cur := 7, right := [0, 0, 3, 4, 0, 1, 0, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 4, right := [3, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h147 : steps tm_15_8 5180 initConfig = some { st := some 10, left := [], cur := 4, right := [3, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5145 35 initConfig _ _ h146 hstep147
  have hstep148 : steps tm_15_8 35 { st := some 10, left := [], cur := 4, right := [3, 2, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h148 : steps tm_15_8 5215 initConfig = some { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5180 35 initConfig _ _ h147 hstep148
  have hstep149 : steps tm_15_8 35 { st := some 5, left := [6, 7, 7, 7], cur := 0, right := [0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h149 : steps tm_15_8 5250 initConfig = some { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5215 35 initConfig _ _ h148 hstep149
  have hstep150 : steps tm_15_8 35 { st := some 1, left := [7], cur := 6, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h150 : steps tm_15_8 5285 initConfig = some { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5250 35 initConfig _ _ h149 hstep150
  have hstep151 : steps tm_15_8 35 { st := some 0, left := [6, 6, 5, 7], cur := 5, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h151 : steps tm_15_8 5320 initConfig = some { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5285 35 initConfig _ _ h150 hstep151
  have hstep152 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 1, right := [1, 4, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h152 : steps tm_15_8 5355 initConfig = some { st := some 10, left := [], cur := 1, right := [1, 4, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5320 35 initConfig _ _ h151 hstep152
  have hstep153 : steps tm_15_8 35 { st := some 10, left := [], cur := 1, right := [1, 4, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h153 : steps tm_15_8 5390 initConfig = some { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5355 35 initConfig _ _ h152 hstep153
  have hstep154 : steps tm_15_8 35 { st := some 0, left := [7], cur := 7, right := [0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h154 : steps tm_15_8 5425 initConfig = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5390 35 initConfig _ _ h153 hstep154
  have hstep155 : steps tm_15_8 35 { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h155 : steps tm_15_8 5460 initConfig = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5425 35 initConfig _ _ h154 hstep155
  have hstep156 : steps tm_15_8 35 { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h156 : steps tm_15_8 5495 initConfig = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5460 35 initConfig _ _ h155 hstep156
  have hstep157 : steps tm_15_8 35 { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := rfl
  have h157 : steps tm_15_8 5530 initConfig = some { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } := steps_add tm_15_8 5495 35 initConfig _ _ h156 hstep157
  have hstep158 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [2, 1, 0, 0, 3, 1, 1, 0, 0, 0, 2, 1] } = some { st := some 5, left := [7, 2, 1], cur := 3, right := [0, 0, 0, 2, 1] } := rfl
  have h158 : steps tm_15_8 5565 initConfig = some { st := some 5, left := [7, 2, 1], cur := 3, right := [0, 0, 0, 2, 1] } := steps_add tm_15_8 5530 35 initConfig _ _ h157 hstep158
  have hstep159 : steps tm_15_8 35 { st := some 5, left := [7, 2, 1], cur := 3, right := [0, 0, 0, 2, 1] } = some { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := rfl
  have h159 : steps tm_15_8 5600 initConfig = some { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5565 35 initConfig _ _ h158 hstep159
  have hstep160 : steps tm_15_8 35 { st := some 2, left := [2], cur := 1, right := [0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } = some { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := rfl
  have h160 : steps tm_15_8 5635 initConfig = some { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5600 35 initConfig _ _ h159 hstep160
  have hstep161 : steps tm_15_8 35 { st := some 7, left := [6, 7, 7], cur := 2, right := [1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } = some { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := rfl
  have h161 : steps tm_15_8 5670 initConfig = some { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5635 35 initConfig _ _ h160 hstep161
  have hstep162 : steps tm_15_8 35 { st := some 3, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := rfl
  have h162 : steps tm_15_8 5705 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5670 35 initConfig _ _ h161 hstep162
  have hstep163 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 2, 1] } = some { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 2, 1, 0, 0, 2, 1] } := rfl
  have h163 : steps tm_15_8 5740 initConfig = some { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 2, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5705 35 initConfig _ _ h162 hstep163
  have hstep164 : steps tm_15_8 35 { st := some 2, left := [1, 1], cur := 0, right := [0, 3, 2, 1, 0, 0, 2, 1] } = some { st := some 7, left := [7, 3, 7, 7, 7], cur := 0, right := [4, 1, 0, 0, 1, 0, 0, 2, 1] } := rfl
  have h164 : steps tm_15_8 5775 initConfig = some { st := some 7, left := [7, 3, 7, 7, 7], cur := 0, right := [4, 1, 0, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5740 35 initConfig _ _ h163 hstep164
  have hstep165 : steps tm_15_8 35 { st := some 7, left := [7, 3, 7, 7, 7], cur := 0, right := [4, 1, 0, 0, 1, 0, 0, 2, 1] } = some { st := some 0, left := [3, 7], cur := 7, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := rfl
  have h165 : steps tm_15_8 5810 initConfig = some { st := some 0, left := [3, 7], cur := 7, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5775 35 initConfig _ _ h164 hstep165
  have hstep166 : steps tm_15_8 35 { st := some 0, left := [3, 7], cur := 7, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [6, 5, 7], cur := 3, right := [1, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := rfl
  have h166 : steps tm_15_8 5845 initConfig = some { st := some 7, left := [6, 5, 7], cur := 3, right := [1, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5810 35 initConfig _ _ h165 hstep166
  have hstep167 : steps tm_15_8 35 { st := some 7, left := [6, 5, 7], cur := 3, right := [1, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } = some { st := some 9, left := [], cur := 1, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := rfl
  have h167 : steps tm_15_8 5880 initConfig = some { st := some 9, left := [], cur := 1, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5845 35 initConfig _ _ h166 hstep167
  have hstep168 : steps tm_15_8 35 { st := some 9, left := [], cur := 1, right := [0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 2, 1] } = some { st := some 5, left := [], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h168 : steps tm_15_8 5915 initConfig = some { st := some 5, left := [], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5880 35 initConfig _ _ h167 hstep168
  have hstep169 : steps tm_15_8 35 { st := some 5, left := [], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [6, 7, 7, 7], cur := 2, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h169 : steps tm_15_8 5950 initConfig = some { st := some 7, left := [6, 7, 7, 7], cur := 2, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5915 35 initConfig _ _ h168 hstep169
  have hstep170 : steps tm_15_8 35 { st := some 7, left := [6, 7, 7, 7], cur := 2, right := [1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [7, 3], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h170 : steps tm_15_8 5985 initConfig = some { st := some 7, left := [7, 3], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5950 35 initConfig _ _ h169 hstep170
  have hstep171 : steps tm_15_8 35 { st := some 7, left := [7, 3], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [6, 5, 6, 7], cur := 2, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h171 : steps tm_15_8 6020 initConfig = some { st := some 7, left := [6, 5, 6, 7], cur := 2, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 5985 35 initConfig _ _ h170 hstep171
  have hstep172 : steps tm_15_8 35 { st := some 7, left := [6, 5, 6, 7], cur := 2, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [7, 3, 1], cur := 0, right := [0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h172 : steps tm_15_8 6055 initConfig = some { st := some 7, left := [7, 3, 1], cur := 0, right := [0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6020 35 initConfig _ _ h171 hstep172
  have hstep173 : steps tm_15_8 35 { st := some 7, left := [7, 3, 1], cur := 0, right := [0, 3, 4, 0, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 0, right := [4, 3, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h173 : steps tm_15_8 6090 initConfig = some { st := some 10, left := [], cur := 0, right := [4, 3, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6055 35 initConfig _ _ h172 hstep173
  have hstep174 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [4, 3, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h174 : steps tm_15_8 6125 initConfig = some { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6090 35 initConfig _ _ h173 hstep174
  have hstep175 : steps tm_15_8 35 { st := some 5, left := [7, 7, 7], cur := 3, right := [0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h175 : steps tm_15_8 6160 initConfig = some { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6125 35 initConfig _ _ h174 hstep175
  have hstep176 : steps tm_15_8 35 { st := some 5, left := [6, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h176 : steps tm_15_8 6195 initConfig = some { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6160 35 initConfig _ _ h175 hstep176
  have hstep177 : steps tm_15_8 35 { st := some 7, left := [5, 6, 6, 5, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h177 : steps tm_15_8 6230 initConfig = some { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6195 35 initConfig _ _ h176 hstep177
  have hstep178 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 10, left := [], cur := 0, right := [1, 1, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h178 : steps tm_15_8 6265 initConfig = some { st := some 10, left := [], cur := 0, right := [1, 1, 4, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6230 35 initConfig _ _ h177 hstep178
  have hstep179 : steps tm_15_8 35 { st := some 10, left := [], cur := 0, right := [1, 1, 4, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h179 : steps tm_15_8 6300 initConfig = some { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6265 35 initConfig _ _ h178 hstep179
  have hstep180 : steps tm_15_8 35 { st := some 7, left := [7, 7], cur := 0, right := [0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h180 : steps tm_15_8 6335 initConfig = some { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6300 35 initConfig _ _ h179 hstep180
  have hstep181 : steps tm_15_8 35 { st := some 5, left := [7, 7], cur := 3, right := [0, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h181 : steps tm_15_8 6370 initConfig = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6335 35 initConfig _ _ h180 hstep181
  have hstep182 : steps tm_15_8 35 { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h182 : steps tm_15_8 6405 initConfig = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6370 35 initConfig _ _ h181 hstep182
  have hstep183 : steps tm_15_8 35 { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := rfl
  have h183 : steps tm_15_8 6440 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } := steps_add tm_15_8 6405 35 initConfig _ _ h182 hstep183
  have hstep184 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 2, 1, 0, 0, 3, 1, 1, 0, 1, 0, 0, 2, 1] } = some { st := some 7, left := [5, 7, 3, 7, 2, 1], cur := 0, right := [0, 2, 1] } := rfl
  have h184 : steps tm_15_8 6475 initConfig = some { st := some 7, left := [5, 7, 3, 7, 2, 1], cur := 0, right := [0, 2, 1] } := steps_add tm_15_8 6440 35 initConfig _ _ h183 hstep184
  have hstep185 : steps tm_15_8 35 { st := some 7, left := [5, 7, 3, 7, 2, 1], cur := 0, right := [0, 2, 1] } = some { st := some 2, left := [2, 0, 1], cur := 1, right := [1, 0, 2, 1] } := rfl
  have h185 : steps tm_15_8 6510 initConfig = some { st := some 2, left := [2, 0, 1], cur := 1, right := [1, 0, 2, 1] } := steps_add tm_15_8 6475 35 initConfig _ _ h184 hstep185
  have hstep186 : steps tm_15_8 35 { st := some 2, left := [2, 0, 1], cur := 1, right := [1, 0, 2, 1] } = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 1, 1, 1] } := rfl
  have h186 : steps tm_15_8 6545 initConfig = some { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 1, 1, 1] } := steps_add tm_15_8 6510 35 initConfig _ _ h185 hstep186
  have hstep187 : steps tm_15_8 35 { st := some 4, left := [7], cur := 0, right := [1, 0, 0, 7, 7, 3, 1, 1, 1] } = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 1, 1, 1] } := rfl
  have h187 : steps tm_15_8 6580 initConfig = some { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 1, 1, 1] } := steps_add tm_15_8 6545 35 initConfig _ _ h186 hstep187
  have hstep188 : steps tm_15_8 35 { st := some 7, left := [6, 6, 7], cur := 0, right := [0, 0, 0, 0, 7, 7, 3, 1, 1, 1] } = some { st := some 7, left := [5, 5, 5, 6, 7, 3, 3, 7], cur := 0, right := [] } := rfl
  have h188 : steps tm_15_8 6615 initConfig = some { st := some 7, left := [5, 5, 5, 6, 7, 3, 3, 7], cur := 0, right := [] } := steps_add tm_15_8 6580 35 initConfig _ _ h187 hstep188
  have hstep189 : steps tm_15_8 35 { st := some 7, left := [5, 5, 5, 6, 7, 3, 3, 7], cur := 0, right := [] } = some { st := some 0, left := [5, 5, 6, 6, 7], cur := 6, right := [] } := rfl
  have h189 : steps tm_15_8 6650 initConfig = some { st := some 0, left := [5, 5, 6, 6, 7], cur := 6, right := [] } := steps_add tm_15_8 6615 35 initConfig _ _ h188 hstep189
  have hstep190 : steps tm_15_8 35 { st := some 0, left := [5, 5, 6, 6, 7], cur := 6, right := [] } = some { st := some 9, left := [], cur := 5, right := [1] } := rfl
  have h190 : steps tm_15_8 6685 initConfig = some { st := some 9, left := [], cur := 5, right := [1] } := steps_add tm_15_8 6650 35 initConfig _ _ h189 hstep190
  have hstep191 : steps tm_15_8 35 { st := some 9, left := [], cur := 5, right := [1] } = some { st := some 3, left := [7], cur := 5, right := [3, 3, 2] } := rfl
  have h191 : steps tm_15_8 6720 initConfig = some { st := some 3, left := [7], cur := 5, right := [3, 3, 2] } := steps_add tm_15_8 6685 35 initConfig _ _ h190 hstep191
  have hstep192 : steps tm_15_8 35 { st := some 3, left := [7], cur := 5, right := [3, 3, 2] } = some { st := some 4, left := [7, 7, 7, 7, 4], cur := 0, right := [] } := rfl
  have h192 : steps tm_15_8 6755 initConfig = some { st := some 4, left := [7, 7, 7, 7, 4], cur := 0, right := [] } := steps_add tm_15_8 6720 35 initConfig _ _ h191 hstep192
  have hstep193 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7, 7, 4], cur := 0, right := [] } = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := rfl
  have h193 : steps tm_15_8 6790 initConfig = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := steps_add tm_15_8 6755 35 initConfig _ _ h192 hstep193
  have hstep194 : steps tm_15_8 35 { st := some 5, left := [], cur := 7, right := [0, 0, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := rfl
  have h194 : steps tm_15_8 6825 initConfig = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := steps_add tm_15_8 6790 35 initConfig _ _ h193 hstep194
  have hstep195 : steps tm_15_8 35 { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := rfl
  have h195 : steps tm_15_8 6860 initConfig = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := steps_add tm_15_8 6825 35 initConfig _ _ h194 hstep195
  have hstep196 : steps tm_15_8 35 { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := rfl
  have h196 : steps tm_15_8 6895 initConfig = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := steps_add tm_15_8 6860 35 initConfig _ _ h195 hstep196
  have hstep197 : steps tm_15_8 35 { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } = some { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := rfl
  have h197 : steps tm_15_8 6930 initConfig = some { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } := steps_add tm_15_8 6895 35 initConfig _ _ h196 hstep197
  have hstep198 : steps tm_15_8 35 { st := some 9, left := [], cur := 2, right := [1, 0, 0, 3, 5, 0, 3, 7, 7, 3, 2, 1] } = some { st := some 12, left := [3, 3, 1, 2, 7, 3, 2, 7, 3, 1, 1], cur := 2, right := [1] } := rfl
  have h198 : steps tm_15_8 6965 initConfig = some { st := some 12, left := [3, 3, 1, 2, 7, 3, 2, 7, 3, 1, 1], cur := 2, right := [1] } := steps_add tm_15_8 6930 35 initConfig _ _ h197 hstep198
  have hstep199 : steps tm_15_8 35 { st := some 12, left := [3, 3, 1, 2, 7, 3, 2, 7, 3, 1, 1], cur := 2, right := [1] } = some { st := some 1, left := [2, 2, 7, 3, 1, 1], cur := 2, right := [3, 1, 3, 3, 1] } := rfl
  have h199 : steps tm_15_8 7000 initConfig = some { st := some 1, left := [2, 2, 7, 3, 1, 1], cur := 2, right := [3, 1, 3, 3, 1] } := steps_add tm_15_8 6965 35 initConfig _ _ h198 hstep199
  have hstep200 : steps tm_15_8 35 { st := some 1, left := [2, 2, 7, 3, 1, 1], cur := 2, right := [3, 1, 3, 3, 1] } = some { st := some 3, left := [5, 6, 5, 5, 6, 5, 7], cur := 6, right := [2] } := rfl
  have h200 : steps tm_15_8 7035 initConfig = some { st := some 3, left := [5, 6, 5, 5, 6, 5, 7], cur := 6, right := [2] } := steps_add tm_15_8 7000 35 initConfig _ _ h199 hstep200
  have hstep201 : steps tm_15_8 35 { st := some 3, left := [5, 6, 5, 5, 6, 5, 7], cur := 6, right := [2] } = some { st := some 7, left := [6, 5, 5, 6, 5, 6, 6, 7], cur := 0, right := [] } := rfl
  have h201 : steps tm_15_8 7070 initConfig = some { st := some 7, left := [6, 5, 5, 6, 5, 6, 6, 7], cur := 0, right := [] } := steps_add tm_15_8 7035 35 initConfig _ _ h200 hstep201
  have hstep202 : steps tm_15_8 35 { st := some 7, left := [6, 5, 5, 6, 5, 6, 6, 7], cur := 0, right := [] } = some { st := some 3, left := [7], cur := 6, right := [3, 3, 2] } := rfl
  have h202 : steps tm_15_8 7105 initConfig = some { st := some 3, left := [7], cur := 6, right := [3, 3, 2] } := steps_add tm_15_8 7070 35 initConfig _ _ h201 hstep202
  have hstep203 : steps tm_15_8 35 { st := some 3, left := [7], cur := 6, right := [3, 3, 2] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 4, 3, 1] } := rfl
  have h203 : steps tm_15_8 7140 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 4, 3, 1] } := steps_add tm_15_8 7105 35 initConfig _ _ h202 hstep203
  have hstep204 : steps tm_15_8 35 { st := some 3, left := [], cur := 0, right := [1, 1, 0, 0, 0, 0, 4, 3, 1] } = some { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := rfl
  have h204 : steps tm_15_8 7175 initConfig = some { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := steps_add tm_15_8 7140 35 initConfig _ _ h203 hstep204
  have hstep205 : steps tm_15_8 35 { st := some 6, left := [7], cur := 7, right := [0, 0, 1, 0, 1, 0, 0, 4, 3, 1] } = some { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := rfl
  have h205 : steps tm_15_8 7210 initConfig = some { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := steps_add tm_15_8 7175 35 initConfig _ _ h204 hstep205
  have hstep206 : steps tm_15_8 35 { st := some 2, left := [7], cur := 2, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := rfl
  have h206 : steps tm_15_8 7245 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } := steps_add tm_15_8 7210 35 initConfig _ _ h205 hstep206
  have hstep207 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 4, 3, 1] } = some { st := some 5, left := [1, 1], cur := 3, right := [4, 3, 1] } := rfl
  have h207 : steps tm_15_8 7280 initConfig = some { st := some 5, left := [1, 1], cur := 3, right := [4, 3, 1] } := steps_add tm_15_8 7245 35 initConfig _ _ h206 hstep207
  have hstep208 : steps tm_15_8 35 { st := some 5, left := [1, 1], cur := 3, right := [4, 3, 1] } = some { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } := rfl
  have h208 : steps tm_15_8 7315 initConfig = some { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7280 35 initConfig _ _ h207 hstep208
  have hstep209 : steps tm_15_8 35 { st := some 7, left := [5, 7], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } = some { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := rfl
  have h209 : steps tm_15_8 7350 initConfig = some { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7315 35 initConfig _ _ h208 hstep209
  have hstep210 : steps tm_15_8 35 { st := some 4, left := [7], cur := 7, right := [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } = some { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := rfl
  have h210 : steps tm_15_8 7385 initConfig = some { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7350 35 initConfig _ _ h209 hstep210
  have hstep211 : steps tm_15_8 35 { st := some 5, left := [6], cur := 0, right := [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } = some { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := rfl
  have h211 : steps tm_15_8 7420 initConfig = some { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7385 35 initConfig _ _ h210 hstep211
  have hstep212 : steps tm_15_8 35 { st := some 3, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 1] } = some { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } := rfl
  have h212 : steps tm_15_8 7455 initConfig = some { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7420 35 initConfig _ _ h211 hstep212
  have hstep213 : steps tm_15_8 35 { st := some 5, left := [6, 1], cur := 0, right := [0, 0, 3, 0, 0, 0, 1, 1] } = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := rfl
  have h213 : steps tm_15_8 7490 initConfig = some { st := some 5, left := [], cur := 7, right := [0, 0, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7455 35 initConfig _ _ h212 hstep213
  have hstep214 : steps tm_15_8 35 { st := some 5, left := [], cur := 7, right := [0, 0, 0, 4, 1, 0, 0, 0, 0, 1, 1] } = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := rfl
  have h214 : steps tm_15_8 7525 initConfig = some { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7490 35 initConfig _ _ h213 hstep214
  have hstep215 : steps tm_15_8 35 { st := some 1, left := [7, 7], cur := 6, right := [1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := rfl
  have h215 : steps tm_15_8 7560 initConfig = some { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7525 35 initConfig _ _ h214 hstep215
  have hstep216 : steps tm_15_8 35 { st := some 1, left := [3, 3, 7], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := rfl
  have h216 : steps tm_15_8 7595 initConfig = some { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7560 35 initConfig _ _ h215 hstep216
  have hstep217 : steps tm_15_8 35 { st := some 6, left := [7], cur := 6, right := [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 1, 1] } = some { st := some 8, left := [], cur := 0, right := [0, 1, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h217 : steps tm_15_8 7630 initConfig = some { st := some 8, left := [], cur := 0, right := [0, 1, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7595 35 initConfig _ _ h216 hstep217
  have hstep218 : steps tm_15_8 35 { st := some 8, left := [], cur := 0, right := [0, 1, 3, 4, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 1, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h218 : steps tm_15_8 7665 initConfig = some { st := some 1, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7630 35 initConfig _ _ h217 hstep218
  have hstep219 : steps tm_15_8 35 { st := some 1, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 7, left := [7, 3, 7], cur := 0, right := [1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h219 : steps tm_15_8 7700 initConfig = some { st := some 7, left := [7, 3, 7], cur := 0, right := [1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7665 35 initConfig _ _ h218 hstep219
  have hstep220 : steps tm_15_8 35 { st := some 7, left := [7, 3, 7], cur := 0, right := [1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 7, left := [5, 7], cur := 3, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h220 : steps tm_15_8 7735 initConfig = some { st := some 7, left := [5, 7], cur := 3, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7700 35 initConfig _ _ h219 hstep220
  have hstep221 : steps tm_15_8 35 { st := some 7, left := [5, 7], cur := 3, right := [3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 9, left := [], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := rfl
  have h221 : steps tm_15_8 7770 initConfig = some { st := some 9, left := [], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7735 35 initConfig _ _ h220 hstep221
  have hstep222 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 0, 0, 1, 1] } = some { st := some 5, left := [7, 3, 1, 1], cur := 6, right := [4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h222 : steps tm_15_8 7805 initConfig = some { st := some 5, left := [7, 3, 1, 1], cur := 6, right := [4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7770 35 initConfig _ _ h221 hstep222
  have hstep223 : steps tm_15_8 35 { st := some 5, left := [7, 3, 1, 1], cur := 6, right := [4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 1, left := [3], cur := 3, right := [0, 0, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h223 : steps tm_15_8 7840 initConfig = some { st := some 1, left := [3], cur := 3, right := [0, 0, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7805 35 initConfig _ _ h222 hstep223
  have hstep224 : steps tm_15_8 35 { st := some 1, left := [3], cur := 3, right := [0, 0, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 1, left := [], cur := 7, right := [3, 2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h224 : steps tm_15_8 7875 initConfig = some { st := some 1, left := [], cur := 7, right := [3, 2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7840 35 initConfig _ _ h223 hstep224
  have hstep225 : steps tm_15_8 35 { st := some 1, left := [], cur := 7, right := [3, 2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 0, left := [3, 3, 7], cur := 7, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h225 : steps tm_15_8 7910 initConfig = some { st := some 0, left := [3, 3, 7], cur := 7, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7875 35 initConfig _ _ h224 hstep225
  have hstep226 : steps tm_15_8 35 { st := some 0, left := [3, 3, 7], cur := 7, right := [0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 8, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h226 : steps tm_15_8 7945 initConfig = some { st := some 8, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7910 35 initConfig _ _ h225 hstep226
  have hstep227 : steps tm_15_8 35 { st := some 8, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 13, left := [], cur := 0, right := [1, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h227 : steps tm_15_8 7980 initConfig = some { st := some 13, left := [], cur := 0, right := [1, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7945 35 initConfig _ _ h226 hstep227
  have hstep228 : steps tm_15_8 35 { st := some 13, left := [], cur := 0, right := [1, 0, 2, 4, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 7, left := [], cur := 0, right := [3, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h228 : steps tm_15_8 8015 initConfig = some { st := some 7, left := [], cur := 0, right := [3, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 7980 35 initConfig _ _ h227 hstep228
  have hstep229 : steps tm_15_8 35 { st := some 7, left := [], cur := 0, right := [3, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 1, left := [], cur := 7, right := [7, 3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h229 : steps tm_15_8 8050 initConfig = some { st := some 1, left := [], cur := 7, right := [7, 3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 8015 35 initConfig _ _ h228 hstep229
  have hstep230 : steps tm_15_8 35 { st := some 1, left := [], cur := 7, right := [7, 3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 7, left := [6, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h230 : steps tm_15_8 8085 initConfig = some { st := some 7, left := [6, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 8050 35 initConfig _ _ h229 hstep230
  have hstep231 : steps tm_15_8 35 { st := some 7, left := [6, 7], cur := 2, right := [1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 3, left := [], cur := 7, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h231 : steps tm_15_8 8120 initConfig = some { st := some 3, left := [], cur := 7, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 8085 35 initConfig _ _ h230 hstep231
  have hstep232 : steps tm_15_8 35 { st := some 3, left := [], cur := 7, right := [1, 3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 11, left := [], cur := 0, right := [1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := rfl
  have h232 : steps tm_15_8 8155 initConfig = some { st := some 11, left := [], cur := 0, right := [1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } := steps_add tm_15_8 8120 35 initConfig _ _ h231 hstep232
  have hstep233 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [1, 0, 0, 0, 3, 1, 1, 0, 0, 0, 1, 1] } = some { st := some 8, left := [], cur := 1, right := [0, 1, 3, 3, 0, 0, 0, 0, 0, 1, 1] } := rfl
  have h233 : steps tm_15_8 8190 initConfig = some { st := some 8, left := [], cur := 1, right := [0, 1, 3, 3, 0, 0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 8155 35 initConfig _ _ h232 hstep233
  have hstep234 : steps tm_15_8 35 { st := some 8, left := [], cur := 1, right := [0, 1, 3, 3, 0, 0, 0, 0, 0, 1, 1] } = some { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := rfl
  have h234 : steps tm_15_8 8225 initConfig = some { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8190 35 initConfig _ _ h233 hstep234
  have hstep235 : steps tm_15_8 35 { st := some 7, left := [7], cur := 1, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } = some { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := rfl
  have h235 : steps tm_15_8 8260 initConfig = some { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8225 35 initConfig _ _ h234 hstep235
  have hstep236 : steps tm_15_8 35 { st := some 6, left := [7, 7], cur := 7, right := [0, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } = some { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := rfl
  have h236 : steps tm_15_8 8295 initConfig = some { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8260 35 initConfig _ _ h235 hstep236
  have hstep237 : steps tm_15_8 35 { st := some 5, left := [], cur := 3, right := [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } = some { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := rfl
  have h237 : steps tm_15_8 8330 initConfig = some { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8295 35 initConfig _ _ h236 hstep237
  have hstep238 : steps tm_15_8 35 { st := some 6, left := [6, 7], cur := 5, right := [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } = some { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := rfl
  have h238 : steps tm_15_8 8365 initConfig = some { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8330 35 initConfig _ _ h237 hstep238
  have hstep239 : steps tm_15_8 35 { st := some 5, left := [1], cur := 3, right := [0, 0, 0, 3, 2, 1, 0, 0, 1, 1] } = some { st := some 0, left := [7], cur := 7, right := [0, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := rfl
  have h239 : steps tm_15_8 8400 initConfig = some { st := some 0, left := [7], cur := 7, right := [0, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8365 35 initConfig _ _ h238 hstep239
  have hstep240 : steps tm_15_8 35 { st := some 0, left := [7], cur := 7, right := [0, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := rfl
  have h240 : steps tm_15_8 8435 initConfig = some { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8400 35 initConfig _ _ h239 hstep240
  have hstep241 : steps tm_15_8 35 { st := some 5, left := [6, 7, 7], cur := 0, right := [0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := rfl
  have h241 : steps tm_15_8 8470 initConfig = some { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8435 35 initConfig _ _ h240 hstep241
  have hstep242 : steps tm_15_8 35 { st := some 1, left := [3, 7], cur := 1, right := [0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := rfl
  have h242 : steps tm_15_8 8505 initConfig = some { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8470 35 initConfig _ _ h241 hstep242
  have hstep243 : steps tm_15_8 35 { st := some 0, left := [6, 7], cur := 6, right := [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 4, 1, 0, 0, 1, 0, 0, 1, 1] } = some { st := some 3, left := [], cur := 1, right := [1, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h243 : steps tm_15_8 8540 initConfig = some { st := some 3, left := [], cur := 1, right := [1, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8505 35 initConfig _ _ h242 hstep243
  have hstep244 : steps tm_15_8 35 { st := some 3, left := [], cur := 1, right := [1, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 4, left := [7, 7, 7], cur := 0, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h244 : steps tm_15_8 8575 initConfig = some { st := some 4, left := [7, 7, 7], cur := 0, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8540 35 initConfig _ _ h243 hstep244
  have hstep245 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7], cur := 0, right := [0, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 1, left := [3, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h245 : steps tm_15_8 8610 initConfig = some { st := some 1, left := [3, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8575 35 initConfig _ _ h244 hstep245
  have hstep246 : steps tm_15_8 35 { st := some 1, left := [3, 7], cur := 0, right := [0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h246 : steps tm_15_8 8645 initConfig = some { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8610 35 initConfig _ _ h245 hstep246
  have hstep247 : steps tm_15_8 35 { st := some 7, left := [7], cur := 1, right := [3, 3, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h247 : steps tm_15_8 8680 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8645 35 initConfig _ _ h246 hstep247
  have hstep248 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 4, 0, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 1, left := [6, 7, 3, 1, 1], cur := 4, right := [1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h248 : steps tm_15_8 8715 initConfig = some { st := some 1, left := [6, 7, 3, 1, 1], cur := 4, right := [1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8680 35 initConfig _ _ h247 hstep248
  have hstep249 : steps tm_15_8 35 { st := some 1, left := [6, 7, 3, 1, 1], cur := 4, right := [1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h249 : steps tm_15_8 8750 initConfig = some { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8715 35 initConfig _ _ h248 hstep249
  have hstep250 : steps tm_15_8 35 { st := some 4, left := [], cur := 0, right := [3, 0, 0, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h250 : steps tm_15_8 8785 initConfig = some { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8750 35 initConfig _ _ h249 hstep250
  have hstep251 : steps tm_15_8 35 { st := some 3, left := [7], cur := 7, right := [2, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h251 : steps tm_15_8 8820 initConfig = some { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8785 35 initConfig _ _ h250 hstep251
  have hstep252 : steps tm_15_8 35 { st := some 7, left := [7, 3, 3, 7], cur := 0, right := [1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h252 : steps tm_15_8 8855 initConfig = some { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8820 35 initConfig _ _ h251 hstep252
  have hstep253 : steps tm_15_8 35 { st := some 8, left := [], cur := 7, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 13, left := [], cur := 0, right := [0, 1, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h253 : steps tm_15_8 8890 initConfig = some { st := some 13, left := [], cur := 0, right := [0, 1, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8855 35 initConfig _ _ h252 hstep253
  have hstep254 : steps tm_15_8 35 { st := some 13, left := [], cur := 0, right := [0, 1, 0, 2, 4, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 14, left := [], cur := 2, right := [1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h254 : steps tm_15_8 8925 initConfig = some { st := some 14, left := [], cur := 2, right := [1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8890 35 initConfig _ _ h253 hstep254
  have hstep255 : steps tm_15_8 35 { st := some 14, left := [], cur := 2, right := [1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 1, left := [7], cur := 7, right := [3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h255 : steps tm_15_8 8960 initConfig = some { st := some 1, left := [7], cur := 7, right := [3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8925 35 initConfig _ _ h254 hstep255
  have hstep256 : steps tm_15_8 35 { st := some 1, left := [7], cur := 7, right := [3, 2, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 7, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h256 : steps tm_15_8 8995 initConfig = some { st := some 7, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8960 35 initConfig _ _ h255 hstep256
  have hstep257 : steps tm_15_8 35 { st := some 7, left := [7], cur := 3, right := [2, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 3, left := [7], cur := 5, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h257 : steps tm_15_8 9030 initConfig = some { st := some 3, left := [7], cur := 5, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 8995 35 initConfig _ _ h256 hstep257
  have hstep258 : steps tm_15_8 35 { st := some 3, left := [7], cur := 5, right := [3, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 11, left := [], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := rfl
  have h258 : steps tm_15_8 9065 initConfig = some { st := some 11, left := [], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 9030 35 initConfig _ _ h257 hstep258
  have hstep259 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [0, 1, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 1, 1] } = some { st := some 3, left := [1], cur := 1, right := [1, 3, 3, 0, 0, 0, 1, 0, 0, 1, 1] } := rfl
  have h259 : steps tm_15_8 9100 initConfig = some { st := some 3, left := [1], cur := 1, right := [1, 3, 3, 0, 0, 0, 1, 0, 0, 1, 1] } := steps_add tm_15_8 9065 35 initConfig _ _ h258 hstep259
  have hstep260 : steps tm_15_8 35 { st := some 3, left := [1], cur := 1, right := [1, 3, 3, 0, 0, 0, 1, 0, 0, 1, 1] } = some { st := some 12, left := [1], cur := 3, right := [0, 0, 0, 0, 1, 1] } := rfl
  have h260 : steps tm_15_8 9135 initConfig = some { st := some 12, left := [1], cur := 3, right := [0, 0, 0, 0, 1, 1] } := steps_add tm_15_8 9100 35 initConfig _ _ h259 hstep260
  have hstep261 : steps tm_15_8 35 { st := some 12, left := [1], cur := 3, right := [0, 0, 0, 0, 1, 1] } = some { st := some 2, left := [2, 2, 2, 7, 7, 7, 7, 1], cur := 1, right := [] } := rfl
  have h261 : steps tm_15_8 9170 initConfig = some { st := some 2, left := [2, 2, 2, 7, 7, 7, 7, 1], cur := 1, right := [] } := steps_add tm_15_8 9135 35 initConfig _ _ h260 hstep261
  have hstep262 : steps tm_15_8 35 { st := some 2, left := [2, 2, 2, 7, 7, 7, 7, 1], cur := 1, right := [] } = some { st := some 1, left := [3, 7], cur := 6, right := [1, 0, 7, 7, 1, 3, 3, 1, 1] } := rfl
  have h262 : steps tm_15_8 9205 initConfig = some { st := some 1, left := [3, 7], cur := 6, right := [1, 0, 7, 7, 1, 3, 3, 1, 1] } := steps_add tm_15_8 9170 35 initConfig _ _ h261 hstep262
  have hstep263 : steps tm_15_8 35 { st := some 1, left := [3, 7], cur := 6, right := [1, 0, 7, 7, 1, 3, 3, 1, 1] } = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1, 1] } := rfl
  have h263 : steps tm_15_8 9240 initConfig = some { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1, 1] } := steps_add tm_15_8 9205 35 initConfig _ _ h262 hstep263
  have hstep264 : steps tm_15_8 35 { st := some 9, left := [], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 7, 7, 1, 3, 3, 1, 1] } = some { st := some 2, left := [3, 3, 7], cur := 7, right := [1, 3, 3] } := rfl
  have h264 : steps tm_15_8 9275 initConfig = some { st := some 2, left := [3, 3, 7], cur := 7, right := [1, 3, 3] } := steps_add tm_15_8 9240 35 initConfig _ _ h263 hstep264
  have hstep265 : steps tm_15_8 35 { st := some 2, left := [3, 3, 7], cur := 7, right := [1, 3, 3] } = some { st := some 13, left := [], cur := 0, right := [5, 3, 0, 5, 3] } := rfl
  have h265 : steps tm_15_8 9310 initConfig = some { st := some 13, left := [], cur := 0, right := [5, 3, 0, 5, 3] } := steps_add tm_15_8 9275 35 initConfig _ _ h264 hstep265
  have hstep266 : steps tm_15_8 35 { st := some 13, left := [], cur := 0, right := [5, 3, 0, 5, 3] } = some { st := some 11, left := [], cur := 0, right := [4, 0, 4, 2, 1, 0, 0, 3] } := rfl
  have h266 : steps tm_15_8 9345 initConfig = some { st := some 11, left := [], cur := 0, right := [4, 0, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9310 35 initConfig _ _ h265 hstep266
  have hstep267 : steps tm_15_8 35 { st := some 11, left := [], cur := 0, right := [4, 0, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7, 7], cur := 3, right := [1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h267 : steps tm_15_8 9380 initConfig = some { st := some 4, left := [7, 7, 7], cur := 3, right := [1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9345 35 initConfig _ _ h266 hstep267
  have hstep268 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7], cur := 3, right := [1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7], cur := 1, right := [4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h268 : steps tm_15_8 9415 initConfig = some { st := some 5, left := [4, 7], cur := 1, right := [4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9380 35 initConfig _ _ h267 hstep268
  have hstep269 : steps tm_15_8 35 { st := some 5, left := [4, 7], cur := 1, right := [4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [], cur := 7, right := [4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h269 : steps tm_15_8 9450 initConfig = some { st := some 5, left := [], cur := 7, right := [4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9415 35 initConfig _ _ h268 hstep269
  have hstep270 : steps tm_15_8 35 { st := some 5, left := [], cur := 7, right := [4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h270 : steps tm_15_8 9485 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9450 35 initConfig _ _ h269 hstep270
  have hstep271 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 1, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h271 : steps tm_15_8 9520 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9485 35 initConfig _ _ h270 hstep271
  have hstep272 : steps tm_15_8 35 { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h272 : steps tm_15_8 9555 initConfig = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9520 35 initConfig _ _ h271 hstep272
  have hstep273 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h273 : steps tm_15_8 9590 initConfig = some { st := some 4, left := [7, 7], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9555 35 initConfig _ _ h272 hstep273
  have hstep274 : steps tm_15_8 35 { st := some 4, left := [7, 7], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h274 : steps tm_15_8 9625 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9590 35 initConfig _ _ h273 hstep274
  have hstep275 : steps tm_15_8 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h275 : steps tm_15_8 9660 initConfig = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9625 35 initConfig _ _ h274 hstep275
  have hstep276 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h276 : steps tm_15_8 9695 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9660 35 initConfig _ _ h275 hstep276
  have hstep277 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h277 : steps tm_15_8 9730 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9695 35 initConfig _ _ h276 hstep277
  have hstep278 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h278 : steps tm_15_8 9765 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9730 35 initConfig _ _ h277 hstep278
  have hstep279 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h279 : steps tm_15_8 9800 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9765 35 initConfig _ _ h278 hstep279
  have hstep280 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h280 : steps tm_15_8 9835 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9800 35 initConfig _ _ h279 hstep280
  have hstep281 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h281 : steps tm_15_8 9870 initConfig = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9835 35 initConfig _ _ h280 hstep281
  have hstep282 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h282 : steps tm_15_8 9905 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9870 35 initConfig _ _ h281 hstep282
  have hstep283 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h283 : steps tm_15_8 9940 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9905 35 initConfig _ _ h282 hstep283
  have hstep284 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h284 : steps tm_15_8 9975 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9940 35 initConfig _ _ h283 hstep284
  have hstep285 : steps tm_15_8 35 { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h285 : steps tm_15_8 10010 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 9975 35 initConfig _ _ h284 hstep285
  have hstep286 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h286 : steps tm_15_8 10045 initConfig = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10010 35 initConfig _ _ h285 hstep286
  have hstep287 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h287 : steps tm_15_8 10080 initConfig = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10045 35 initConfig _ _ h286 hstep287
  have hstep288 : steps tm_15_8 35 { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h288 : steps tm_15_8 10115 initConfig = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10080 35 initConfig _ _ h287 hstep288
  have hstep289 : steps tm_15_8 35 { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h289 : steps tm_15_8 10150 initConfig = some { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10115 35 initConfig _ _ h288 hstep289
  have hstep290 : steps tm_15_8 35 { st := some 1, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h290 : steps tm_15_8 10185 initConfig = some { st := some 1, left := [7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10150 35 initConfig _ _ h289 hstep290
  have hstep291 : steps tm_15_8 35 { st := some 1, left := [7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h291 : steps tm_15_8 10220 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10185 35 initConfig _ _ h290 hstep291
  have hstep292 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h292 : steps tm_15_8 10255 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10220 35 initConfig _ _ h291 hstep292
  have hstep293 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h293 : steps tm_15_8 10290 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10255 35 initConfig _ _ h292 hstep293
  have hstep294 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h294 : steps tm_15_8 10325 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10290 35 initConfig _ _ h293 hstep294
  have hstep295 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h295 : steps tm_15_8 10360 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10325 35 initConfig _ _ h294 hstep295
  have hstep296 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h296 : steps tm_15_8 10395 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10360 35 initConfig _ _ h295 hstep296
  have hstep297 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h297 : steps tm_15_8 10430 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10395 35 initConfig _ _ h296 hstep297
  have hstep298 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h298 : steps tm_15_8 10465 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10430 35 initConfig _ _ h297 hstep298
  have hstep299 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h299 : steps tm_15_8 10500 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10465 35 initConfig _ _ h298 hstep299
  have hstep300 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h300 : steps tm_15_8 10535 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10500 35 initConfig _ _ h299 hstep300
  have hstep301 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h301 : steps tm_15_8 10570 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10535 35 initConfig _ _ h300 hstep301
  have hstep302 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h302 : steps tm_15_8 10605 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10570 35 initConfig _ _ h301 hstep302
  have hstep303 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h303 : steps tm_15_8 10640 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10605 35 initConfig _ _ h302 hstep303
  have hstep304 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h304 : steps tm_15_8 10675 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10640 35 initConfig _ _ h303 hstep304
  have hstep305 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h305 : steps tm_15_8 10710 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10675 35 initConfig _ _ h304 hstep305
  have hstep306 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h306 : steps tm_15_8 10745 initConfig = some { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10710 35 initConfig _ _ h305 hstep306
  have hstep307 : steps tm_15_8 35 { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h307 : steps tm_15_8 10780 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10745 35 initConfig _ _ h306 hstep307
  have hstep308 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h308 : steps tm_15_8 10815 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10780 35 initConfig _ _ h307 hstep308
  have hstep309 : steps tm_15_8 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h309 : steps tm_15_8 10850 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10815 35 initConfig _ _ h308 hstep309
  have hstep310 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h310 : steps tm_15_8 10885 initConfig = some { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10850 35 initConfig _ _ h309 hstep310
  have hstep311 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h311 : steps tm_15_8 10920 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10885 35 initConfig _ _ h310 hstep311
  have hstep312 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h312 : steps tm_15_8 10955 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10920 35 initConfig _ _ h311 hstep312
  have hstep313 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h313 : steps tm_15_8 10990 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10955 35 initConfig _ _ h312 hstep313
  have hstep314 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h314 : steps tm_15_8 11025 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 10990 35 initConfig _ _ h313 hstep314
  have hstep315 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h315 : steps tm_15_8 11060 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11025 35 initConfig _ _ h314 hstep315
  have hstep316 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h316 : steps tm_15_8 11095 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11060 35 initConfig _ _ h315 hstep316
  have hstep317 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h317 : steps tm_15_8 11130 initConfig = some { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11095 35 initConfig _ _ h316 hstep317
  have hstep318 : steps tm_15_8 35 { st := some 6, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h318 : steps tm_15_8 11165 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11130 35 initConfig _ _ h317 hstep318
  have hstep319 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h319 : steps tm_15_8 11200 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11165 35 initConfig _ _ h318 hstep319
  have hstep320 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h320 : steps tm_15_8 11235 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11200 35 initConfig _ _ h319 hstep320
  have hstep321 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h321 : steps tm_15_8 11270 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11235 35 initConfig _ _ h320 hstep321
  have hstep322 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h322 : steps tm_15_8 11305 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11270 35 initConfig _ _ h321 hstep322
  have hstep323 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h323 : steps tm_15_8 11340 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11305 35 initConfig _ _ h322 hstep323
  have hstep324 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h324 : steps tm_15_8 11375 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11340 35 initConfig _ _ h323 hstep324
  have hstep325 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h325 : steps tm_15_8 11410 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11375 35 initConfig _ _ h324 hstep325
  have hstep326 : steps tm_15_8 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h326 : steps tm_15_8 11445 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11410 35 initConfig _ _ h325 hstep326
  have hstep327 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h327 : steps tm_15_8 11480 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11445 35 initConfig _ _ h326 hstep327
  have hstep328 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h328 : steps tm_15_8 11515 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11480 35 initConfig _ _ h327 hstep328
  have hstep329 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h329 : steps tm_15_8 11550 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11515 35 initConfig _ _ h328 hstep329
  have hstep330 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h330 : steps tm_15_8 11585 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11550 35 initConfig _ _ h329 hstep330
  have hstep331 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h331 : steps tm_15_8 11620 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11585 35 initConfig _ _ h330 hstep331
  have hstep332 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h332 : steps tm_15_8 11655 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11620 35 initConfig _ _ h331 hstep332
  have hstep333 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h333 : steps tm_15_8 11690 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11655 35 initConfig _ _ h332 hstep333
  have hstep334 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h334 : steps tm_15_8 11725 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11690 35 initConfig _ _ h333 hstep334
  have hstep335 : steps tm_15_8 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h335 : steps tm_15_8 11760 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11725 35 initConfig _ _ h334 hstep335
  have hstep336 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h336 : steps tm_15_8 11795 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11760 35 initConfig _ _ h335 hstep336
  have hstep337 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h337 : steps tm_15_8 11830 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11795 35 initConfig _ _ h336 hstep337
  have hstep338 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h338 : steps tm_15_8 11865 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11830 35 initConfig _ _ h337 hstep338
  have hstep339 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h339 : steps tm_15_8 11900 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11865 35 initConfig _ _ h338 hstep339
  have hstep340 : steps tm_15_8 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h340 : steps tm_15_8 11935 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11900 35 initConfig _ _ h339 hstep340
  have hstep341 : steps tm_15_8 35 { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h341 : steps tm_15_8 11970 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11935 35 initConfig _ _ h340 hstep341
  have hstep342 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h342 : steps tm_15_8 12005 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 11970 35 initConfig _ _ h341 hstep342
  have hstep343 : steps tm_15_8 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h343 : steps tm_15_8 12040 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12005 35 initConfig _ _ h342 hstep343
  have hstep344 : steps tm_15_8 35 { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h344 : steps tm_15_8 12075 initConfig = some { st := some 4, left := [7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12040 35 initConfig _ _ h343 hstep344
  have hstep345 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h345 : steps tm_15_8 12110 initConfig = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12075 35 initConfig _ _ h344 hstep345
  have hstep346 : steps tm_15_8 35 { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h346 : steps tm_15_8 12145 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12110 35 initConfig _ _ h345 hstep346
  have hstep347 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h347 : steps tm_15_8 12180 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12145 35 initConfig _ _ h346 hstep347
  have hstep348 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h348 : steps tm_15_8 12215 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12180 35 initConfig _ _ h347 hstep348
  have hstep349 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h349 : steps tm_15_8 12250 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12215 35 initConfig _ _ h348 hstep349
  have hstep350 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h350 : steps tm_15_8 12285 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12250 35 initConfig _ _ h349 hstep350
  have hstep351 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h351 : steps tm_15_8 12320 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12285 35 initConfig _ _ h350 hstep351
  have hstep352 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h352 : steps tm_15_8 12355 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12320 35 initConfig _ _ h351 hstep352
  have hstep353 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h353 : steps tm_15_8 12390 initConfig = some { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12355 35 initConfig _ _ h352 hstep353
  have hstep354 : steps tm_15_8 35 { st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 0, left := [2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h354 : steps tm_15_8 12425 initConfig = some { st := some 0, left := [2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12390 35 initConfig _ _ h353 hstep354
  have hstep355 : steps tm_15_8 35 { st := some 0, left := [2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h355 : steps tm_15_8 12460 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12425 35 initConfig _ _ h354 hstep355
  have hstep356 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h356 : steps tm_15_8 12495 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12460 35 initConfig _ _ h355 hstep356
  have hstep357 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h357 : steps tm_15_8 12530 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12495 35 initConfig _ _ h356 hstep357
  have hstep358 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h358 : steps tm_15_8 12565 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12530 35 initConfig _ _ h357 hstep358
  have hstep359 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h359 : steps tm_15_8 12600 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12565 35 initConfig _ _ h358 hstep359
  have hstep360 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h360 : steps tm_15_8 12635 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12600 35 initConfig _ _ h359 hstep360
  have hstep361 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h361 : steps tm_15_8 12670 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12635 35 initConfig _ _ h360 hstep361
  have hstep362 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h362 : steps tm_15_8 12705 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12670 35 initConfig _ _ h361 hstep362
  have hstep363 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h363 : steps tm_15_8 12740 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12705 35 initConfig _ _ h362 hstep363
  have hstep364 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h364 : steps tm_15_8 12775 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12740 35 initConfig _ _ h363 hstep364
  have hstep365 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h365 : steps tm_15_8 12810 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12775 35 initConfig _ _ h364 hstep365
  have hstep366 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h366 : steps tm_15_8 12845 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12810 35 initConfig _ _ h365 hstep366
  have hstep367 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h367 : steps tm_15_8 12880 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12845 35 initConfig _ _ h366 hstep367
  have hstep368 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h368 : steps tm_15_8 12915 initConfig = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12880 35 initConfig _ _ h367 hstep368
  have hstep369 : steps tm_15_8 35 { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h369 : steps tm_15_8 12950 initConfig = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12915 35 initConfig _ _ h368 hstep369
  have hstep370 : steps tm_15_8 35 { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h370 : steps tm_15_8 12985 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12950 35 initConfig _ _ h369 hstep370
  have hstep371 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h371 : steps tm_15_8 13020 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 12985 35 initConfig _ _ h370 hstep371
  have hstep372 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h372 : steps tm_15_8 13055 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13020 35 initConfig _ _ h371 hstep372
  have hstep373 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h373 : steps tm_15_8 13090 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13055 35 initConfig _ _ h372 hstep373
  have hstep374 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h374 : steps tm_15_8 13125 initConfig = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13090 35 initConfig _ _ h373 hstep374
  have hstep375 : steps tm_15_8 35 { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h375 : steps tm_15_8 13160 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13125 35 initConfig _ _ h374 hstep375
  have hstep376 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h376 : steps tm_15_8 13195 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13160 35 initConfig _ _ h375 hstep376
  have hstep377 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h377 : steps tm_15_8 13230 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13195 35 initConfig _ _ h376 hstep377
  have hstep378 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h378 : steps tm_15_8 13265 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13230 35 initConfig _ _ h377 hstep378
  have hstep379 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h379 : steps tm_15_8 13300 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13265 35 initConfig _ _ h378 hstep379
  have hstep380 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h380 : steps tm_15_8 13335 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13300 35 initConfig _ _ h379 hstep380
  have hstep381 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h381 : steps tm_15_8 13370 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13335 35 initConfig _ _ h380 hstep381
  have hstep382 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h382 : steps tm_15_8 13405 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13370 35 initConfig _ _ h381 hstep382
  have hstep383 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h383 : steps tm_15_8 13440 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13405 35 initConfig _ _ h382 hstep383
  have hstep384 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h384 : steps tm_15_8 13475 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13440 35 initConfig _ _ h383 hstep384
  have hstep385 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h385 : steps tm_15_8 13510 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13475 35 initConfig _ _ h384 hstep385
  have hstep386 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h386 : steps tm_15_8 13545 initConfig = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13510 35 initConfig _ _ h385 hstep386
  have hstep387 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h387 : steps tm_15_8 13580 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13545 35 initConfig _ _ h386 hstep387
  have hstep388 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h388 : steps tm_15_8 13615 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13580 35 initConfig _ _ h387 hstep388
  have hstep389 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h389 : steps tm_15_8 13650 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13615 35 initConfig _ _ h388 hstep389
  have hstep390 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h390 : steps tm_15_8 13685 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13650 35 initConfig _ _ h389 hstep390
  have hstep391 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h391 : steps tm_15_8 13720 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13685 35 initConfig _ _ h390 hstep391
  have hstep392 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h392 : steps tm_15_8 13755 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13720 35 initConfig _ _ h391 hstep392
  have hstep393 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h393 : steps tm_15_8 13790 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13755 35 initConfig _ _ h392 hstep393
  have hstep394 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h394 : steps tm_15_8 13825 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13790 35 initConfig _ _ h393 hstep394
  have hstep395 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h395 : steps tm_15_8 13860 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13825 35 initConfig _ _ h394 hstep395
  have hstep396 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h396 : steps tm_15_8 13895 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13860 35 initConfig _ _ h395 hstep396
  have hstep397 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h397 : steps tm_15_8 13930 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13895 35 initConfig _ _ h396 hstep397
  have hstep398 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h398 : steps tm_15_8 13965 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13930 35 initConfig _ _ h397 hstep398
  have hstep399 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h399 : steps tm_15_8 14000 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 13965 35 initConfig _ _ h398 hstep399
  have hstep400 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h400 : steps tm_15_8 14035 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14000 35 initConfig _ _ h399 hstep400
  have hstep401 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h401 : steps tm_15_8 14070 initConfig = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14035 35 initConfig _ _ h400 hstep401
  have hstep402 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h402 : steps tm_15_8 14105 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14070 35 initConfig _ _ h401 hstep402
  have hstep403 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h403 : steps tm_15_8 14140 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14105 35 initConfig _ _ h402 hstep403
  have hstep404 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h404 : steps tm_15_8 14175 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14140 35 initConfig _ _ h403 hstep404
  have hstep405 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h405 : steps tm_15_8 14210 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14175 35 initConfig _ _ h404 hstep405
  have hstep406 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h406 : steps tm_15_8 14245 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14210 35 initConfig _ _ h405 hstep406
  have hstep407 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h407 : steps tm_15_8 14280 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14245 35 initConfig _ _ h406 hstep407
  have hstep408 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h408 : steps tm_15_8 14315 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14280 35 initConfig _ _ h407 hstep408
  have hstep409 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h409 : steps tm_15_8 14350 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14315 35 initConfig _ _ h408 hstep409
  have hstep410 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h410 : steps tm_15_8 14385 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14350 35 initConfig _ _ h409 hstep410
  have hstep411 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h411 : steps tm_15_8 14420 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14385 35 initConfig _ _ h410 hstep411
  have hstep412 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h412 : steps tm_15_8 14455 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14420 35 initConfig _ _ h411 hstep412
  have hstep413 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h413 : steps tm_15_8 14490 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14455 35 initConfig _ _ h412 hstep413
  have hstep414 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h414 : steps tm_15_8 14525 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14490 35 initConfig _ _ h413 hstep414
  have hstep415 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h415 : steps tm_15_8 14560 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14525 35 initConfig _ _ h414 hstep415
  have hstep416 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h416 : steps tm_15_8 14595 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14560 35 initConfig _ _ h415 hstep416
  have hstep417 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h417 : steps tm_15_8 14630 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14595 35 initConfig _ _ h416 hstep417
  have hstep418 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h418 : steps tm_15_8 14665 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14630 35 initConfig _ _ h417 hstep418
  have hstep419 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h419 : steps tm_15_8 14700 initConfig = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14665 35 initConfig _ _ h418 hstep419
  have hstep420 : steps tm_15_8 35 { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h420 : steps tm_15_8 14735 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14700 35 initConfig _ _ h419 hstep420
  have hstep421 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h421 : steps tm_15_8 14770 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14735 35 initConfig _ _ h420 hstep421
  have hstep422 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h422 : steps tm_15_8 14805 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14770 35 initConfig _ _ h421 hstep422
  have hstep423 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h423 : steps tm_15_8 14840 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14805 35 initConfig _ _ h422 hstep423
  have hstep424 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h424 : steps tm_15_8 14875 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14840 35 initConfig _ _ h423 hstep424
  have hstep425 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h425 : steps tm_15_8 14910 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14875 35 initConfig _ _ h424 hstep425
  have hstep426 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h426 : steps tm_15_8 14945 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14910 35 initConfig _ _ h425 hstep426
  have hstep427 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h427 : steps tm_15_8 14980 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14945 35 initConfig _ _ h426 hstep427
  have hstep428 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h428 : steps tm_15_8 15015 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 14980 35 initConfig _ _ h427 hstep428
  have hstep429 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h429 : steps tm_15_8 15050 initConfig = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15015 35 initConfig _ _ h428 hstep429
  have hstep430 : steps tm_15_8 35 { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h430 : steps tm_15_8 15085 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15050 35 initConfig _ _ h429 hstep430
  have hstep431 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h431 : steps tm_15_8 15120 initConfig = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15085 35 initConfig _ _ h430 hstep431
  have hstep432 : steps tm_15_8 35 { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h432 : steps tm_15_8 15155 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15120 35 initConfig _ _ h431 hstep432
  have hstep433 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h433 : steps tm_15_8 15190 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15155 35 initConfig _ _ h432 hstep433
  have hstep434 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h434 : steps tm_15_8 15225 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15190 35 initConfig _ _ h433 hstep434
  have hstep435 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h435 : steps tm_15_8 15260 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15225 35 initConfig _ _ h434 hstep435
  have hstep436 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h436 : steps tm_15_8 15295 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15260 35 initConfig _ _ h435 hstep436
  have hstep437 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h437 : steps tm_15_8 15330 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15295 35 initConfig _ _ h436 hstep437
  have hstep438 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h438 : steps tm_15_8 15365 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15330 35 initConfig _ _ h437 hstep438
  have hstep439 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h439 : steps tm_15_8 15400 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15365 35 initConfig _ _ h438 hstep439
  have hstep440 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h440 : steps tm_15_8 15435 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15400 35 initConfig _ _ h439 hstep440
  have hstep441 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h441 : steps tm_15_8 15470 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15435 35 initConfig _ _ h440 hstep441
  have hstep442 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h442 : steps tm_15_8 15505 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15470 35 initConfig _ _ h441 hstep442
  have hstep443 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h443 : steps tm_15_8 15540 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15505 35 initConfig _ _ h442 hstep443
  have hstep444 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h444 : steps tm_15_8 15575 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15540 35 initConfig _ _ h443 hstep444
  have hstep445 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h445 : steps tm_15_8 15610 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15575 35 initConfig _ _ h444 hstep445
  have hstep446 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h446 : steps tm_15_8 15645 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15610 35 initConfig _ _ h445 hstep446
  have hstep447 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h447 : steps tm_15_8 15680 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15645 35 initConfig _ _ h446 hstep447
  have hstep448 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h448 : steps tm_15_8 15715 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15680 35 initConfig _ _ h447 hstep448
  have hstep449 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h449 : steps tm_15_8 15750 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15715 35 initConfig _ _ h448 hstep449
  have hstep450 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h450 : steps tm_15_8 15785 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15750 35 initConfig _ _ h449 hstep450
  have hstep451 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h451 : steps tm_15_8 15820 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15785 35 initConfig _ _ h450 hstep451
  have hstep452 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h452 : steps tm_15_8 15855 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15820 35 initConfig _ _ h451 hstep452
  have hstep453 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h453 : steps tm_15_8 15890 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15855 35 initConfig _ _ h452 hstep453
  have hstep454 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h454 : steps tm_15_8 15925 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15890 35 initConfig _ _ h453 hstep454
  have hstep455 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h455 : steps tm_15_8 15960 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15925 35 initConfig _ _ h454 hstep455
  have hstep456 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h456 : steps tm_15_8 15995 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15960 35 initConfig _ _ h455 hstep456
  have hstep457 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h457 : steps tm_15_8 16030 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 15995 35 initConfig _ _ h456 hstep457
  have hstep458 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h458 : steps tm_15_8 16065 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16030 35 initConfig _ _ h457 hstep458
  have hstep459 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h459 : steps tm_15_8 16100 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16065 35 initConfig _ _ h458 hstep459
  have hstep460 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h460 : steps tm_15_8 16135 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16100 35 initConfig _ _ h459 hstep460
  have hstep461 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h461 : steps tm_15_8 16170 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16135 35 initConfig _ _ h460 hstep461
  have hstep462 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h462 : steps tm_15_8 16205 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16170 35 initConfig _ _ h461 hstep462
  have hstep463 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h463 : steps tm_15_8 16240 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16205 35 initConfig _ _ h462 hstep463
  have hstep464 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h464 : steps tm_15_8 16275 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16240 35 initConfig _ _ h463 hstep464
  have hstep465 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h465 : steps tm_15_8 16310 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16275 35 initConfig _ _ h464 hstep465
  have hstep466 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h466 : steps tm_15_8 16345 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16310 35 initConfig _ _ h465 hstep466
  have hstep467 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h467 : steps tm_15_8 16380 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16345 35 initConfig _ _ h466 hstep467
  have hstep468 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h468 : steps tm_15_8 16415 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16380 35 initConfig _ _ h467 hstep468
  have hstep469 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h469 : steps tm_15_8 16450 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16415 35 initConfig _ _ h468 hstep469
  have hstep470 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h470 : steps tm_15_8 16485 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16450 35 initConfig _ _ h469 hstep470
  have hstep471 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h471 : steps tm_15_8 16520 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16485 35 initConfig _ _ h470 hstep471
  have hstep472 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h472 : steps tm_15_8 16555 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16520 35 initConfig _ _ h471 hstep472
  have hstep473 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h473 : steps tm_15_8 16590 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16555 35 initConfig _ _ h472 hstep473
  have hstep474 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h474 : steps tm_15_8 16625 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16590 35 initConfig _ _ h473 hstep474
  have hstep475 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h475 : steps tm_15_8 16660 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16625 35 initConfig _ _ h474 hstep475
  have hstep476 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h476 : steps tm_15_8 16695 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16660 35 initConfig _ _ h475 hstep476
  have hstep477 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h477 : steps tm_15_8 16730 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16695 35 initConfig _ _ h476 hstep477
  have hstep478 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h478 : steps tm_15_8 16765 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16730 35 initConfig _ _ h477 hstep478
  have hstep479 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h479 : steps tm_15_8 16800 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16765 35 initConfig _ _ h478 hstep479
  have hstep480 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h480 : steps tm_15_8 16835 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16800 35 initConfig _ _ h479 hstep480
  have hstep481 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h481 : steps tm_15_8 16870 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16835 35 initConfig _ _ h480 hstep481
  have hstep482 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h482 : steps tm_15_8 16905 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16870 35 initConfig _ _ h481 hstep482
  have hstep483 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h483 : steps tm_15_8 16940 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16905 35 initConfig _ _ h482 hstep483
  have hstep484 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h484 : steps tm_15_8 16975 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16940 35 initConfig _ _ h483 hstep484
  have hstep485 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h485 : steps tm_15_8 17010 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 16975 35 initConfig _ _ h484 hstep485
  have hstep486 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h486 : steps tm_15_8 17045 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17010 35 initConfig _ _ h485 hstep486
  have hstep487 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h487 : steps tm_15_8 17080 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17045 35 initConfig _ _ h486 hstep487
  have hstep488 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h488 : steps tm_15_8 17115 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17080 35 initConfig _ _ h487 hstep488
  have hstep489 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h489 : steps tm_15_8 17150 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17115 35 initConfig _ _ h488 hstep489
  have hstep490 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h490 : steps tm_15_8 17185 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17150 35 initConfig _ _ h489 hstep490
  have hstep491 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h491 : steps tm_15_8 17220 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17185 35 initConfig _ _ h490 hstep491
  have hstep492 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h492 : steps tm_15_8 17255 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17220 35 initConfig _ _ h491 hstep492
  have hstep493 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h493 : steps tm_15_8 17290 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17255 35 initConfig _ _ h492 hstep493
  have hstep494 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h494 : steps tm_15_8 17325 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17290 35 initConfig _ _ h493 hstep494
  have hstep495 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h495 : steps tm_15_8 17360 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17325 35 initConfig _ _ h494 hstep495
  have hstep496 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h496 : steps tm_15_8 17395 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17360 35 initConfig _ _ h495 hstep496
  have hstep497 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h497 : steps tm_15_8 17430 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17395 35 initConfig _ _ h496 hstep497
  have hstep498 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h498 : steps tm_15_8 17465 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17430 35 initConfig _ _ h497 hstep498
  have hstep499 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h499 : steps tm_15_8 17500 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17465 35 initConfig _ _ h498 hstep499
  have hstep500 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h500 : steps tm_15_8 17535 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17500 35 initConfig _ _ h499 hstep500
  have hstep501 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h501 : steps tm_15_8 17570 initConfig = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17535 35 initConfig _ _ h500 hstep501
  have hstep502 : steps tm_15_8 35 { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h502 : steps tm_15_8 17605 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17570 35 initConfig _ _ h501 hstep502
  have hstep503 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h503 : steps tm_15_8 17640 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17605 35 initConfig _ _ h502 hstep503
  have hstep504 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h504 : steps tm_15_8 17675 initConfig = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17640 35 initConfig _ _ h503 hstep504
  have hstep505 : steps tm_15_8 35 { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h505 : steps tm_15_8 17710 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17675 35 initConfig _ _ h504 hstep505
  have hstep506 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h506 : steps tm_15_8 17745 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17710 35 initConfig _ _ h505 hstep506
  have hstep507 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h507 : steps tm_15_8 17780 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17745 35 initConfig _ _ h506 hstep507
  have hstep508 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h508 : steps tm_15_8 17815 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17780 35 initConfig _ _ h507 hstep508
  have hstep509 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h509 : steps tm_15_8 17850 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17815 35 initConfig _ _ h508 hstep509
  have hstep510 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h510 : steps tm_15_8 17885 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17850 35 initConfig _ _ h509 hstep510
  have hstep511 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h511 : steps tm_15_8 17920 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17885 35 initConfig _ _ h510 hstep511
  have hstep512 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h512 : steps tm_15_8 17955 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17920 35 initConfig _ _ h511 hstep512
  have hstep513 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h513 : steps tm_15_8 17990 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17955 35 initConfig _ _ h512 hstep513
  have hstep514 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h514 : steps tm_15_8 18025 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 17990 35 initConfig _ _ h513 hstep514
  have hstep515 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h515 : steps tm_15_8 18060 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18025 35 initConfig _ _ h514 hstep515
  have hstep516 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h516 : steps tm_15_8 18095 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18060 35 initConfig _ _ h515 hstep516
  have hstep517 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h517 : steps tm_15_8 18130 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18095 35 initConfig _ _ h516 hstep517
  have hstep518 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h518 : steps tm_15_8 18165 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18130 35 initConfig _ _ h517 hstep518
  have hstep519 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h519 : steps tm_15_8 18200 initConfig = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18165 35 initConfig _ _ h518 hstep519
  have hstep520 : steps tm_15_8 35 { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h520 : steps tm_15_8 18235 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18200 35 initConfig _ _ h519 hstep520
  have hstep521 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h521 : steps tm_15_8 18270 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18235 35 initConfig _ _ h520 hstep521
  have hstep522 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h522 : steps tm_15_8 18305 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18270 35 initConfig _ _ h521 hstep522
  have hstep523 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h523 : steps tm_15_8 18340 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18305 35 initConfig _ _ h522 hstep523
  have hstep524 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h524 : steps tm_15_8 18375 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18340 35 initConfig _ _ h523 hstep524
  have hstep525 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h525 : steps tm_15_8 18410 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18375 35 initConfig _ _ h524 hstep525
  have hstep526 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h526 : steps tm_15_8 18445 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18410 35 initConfig _ _ h525 hstep526
  have hstep527 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h527 : steps tm_15_8 18480 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18445 35 initConfig _ _ h526 hstep527
  have hstep528 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h528 : steps tm_15_8 18515 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18480 35 initConfig _ _ h527 hstep528
  have hstep529 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h529 : steps tm_15_8 18550 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18515 35 initConfig _ _ h528 hstep529
  have hstep530 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h530 : steps tm_15_8 18585 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18550 35 initConfig _ _ h529 hstep530
  have hstep531 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h531 : steps tm_15_8 18620 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18585 35 initConfig _ _ h530 hstep531
  have hstep532 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h532 : steps tm_15_8 18655 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18620 35 initConfig _ _ h531 hstep532
  have hstep533 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h533 : steps tm_15_8 18690 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18655 35 initConfig _ _ h532 hstep533
  have hstep534 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h534 : steps tm_15_8 18725 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18690 35 initConfig _ _ h533 hstep534
  have hstep535 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h535 : steps tm_15_8 18760 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18725 35 initConfig _ _ h534 hstep535
  have hstep536 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h536 : steps tm_15_8 18795 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18760 35 initConfig _ _ h535 hstep536
  have hstep537 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h537 : steps tm_15_8 18830 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18795 35 initConfig _ _ h536 hstep537
  have hstep538 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h538 : steps tm_15_8 18865 initConfig = some { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18830 35 initConfig _ _ h537 hstep538
  have hstep539 : steps tm_15_8 35 { st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h539 : steps tm_15_8 18900 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18865 35 initConfig _ _ h538 hstep539
  have hstep540 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h540 : steps tm_15_8 18935 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18900 35 initConfig _ _ h539 hstep540
  have hstep541 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h541 : steps tm_15_8 18970 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18935 35 initConfig _ _ h540 hstep541
  have hstep542 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h542 : steps tm_15_8 19005 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 18970 35 initConfig _ _ h541 hstep542
  have hstep543 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h543 : steps tm_15_8 19040 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19005 35 initConfig _ _ h542 hstep543
  have hstep544 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h544 : steps tm_15_8 19075 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19040 35 initConfig _ _ h543 hstep544
  have hstep545 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h545 : steps tm_15_8 19110 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19075 35 initConfig _ _ h544 hstep545
  have hstep546 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h546 : steps tm_15_8 19145 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19110 35 initConfig _ _ h545 hstep546
  have hstep547 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h547 : steps tm_15_8 19180 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19145 35 initConfig _ _ h546 hstep547
  have hstep548 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h548 : steps tm_15_8 19215 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19180 35 initConfig _ _ h547 hstep548
  have hstep549 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h549 : steps tm_15_8 19250 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19215 35 initConfig _ _ h548 hstep549
  have hstep550 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h550 : steps tm_15_8 19285 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19250 35 initConfig _ _ h549 hstep550
  have hstep551 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h551 : steps tm_15_8 19320 initConfig = some { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19285 35 initConfig _ _ h550 hstep551
  have hstep552 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h552 : steps tm_15_8 19355 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19320 35 initConfig _ _ h551 hstep552
  have hstep553 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h553 : steps tm_15_8 19390 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19355 35 initConfig _ _ h552 hstep553
  have hstep554 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h554 : steps tm_15_8 19425 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19390 35 initConfig _ _ h553 hstep554
  have hstep555 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h555 : steps tm_15_8 19460 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19425 35 initConfig _ _ h554 hstep555
  have hstep556 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h556 : steps tm_15_8 19495 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19460 35 initConfig _ _ h555 hstep556
  have hstep557 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h557 : steps tm_15_8 19530 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19495 35 initConfig _ _ h556 hstep557
  have hstep558 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h558 : steps tm_15_8 19565 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19530 35 initConfig _ _ h557 hstep558
  have hstep559 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h559 : steps tm_15_8 19600 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19565 35 initConfig _ _ h558 hstep559
  have hstep560 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h560 : steps tm_15_8 19635 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19600 35 initConfig _ _ h559 hstep560
  have hstep561 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h561 : steps tm_15_8 19670 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19635 35 initConfig _ _ h560 hstep561
  have hstep562 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h562 : steps tm_15_8 19705 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19670 35 initConfig _ _ h561 hstep562
  have hstep563 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h563 : steps tm_15_8 19740 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19705 35 initConfig _ _ h562 hstep563
  have hstep564 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h564 : steps tm_15_8 19775 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19740 35 initConfig _ _ h563 hstep564
  have hstep565 : steps tm_15_8 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h565 : steps tm_15_8 19810 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19775 35 initConfig _ _ h564 hstep565
  have hstep566 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h566 : steps tm_15_8 19845 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19810 35 initConfig _ _ h565 hstep566
  have hstep567 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h567 : steps tm_15_8 19880 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19845 35 initConfig _ _ h566 hstep567
  have hstep568 : steps tm_15_8 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := rfl
  have h568 : steps tm_15_8 19915 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19880 35 initConfig _ _ h567 hstep568
  have hstep569 : steps tm_15_8 10 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 0, 0, 3] } = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 1, 0, 0, 3] } := rfl
  have h569 : steps tm_15_8 19925 initConfig = some { st := some 0, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 1, 0, 0, 3] } := steps_add tm_15_8 19915 10 initConfig _ _ h568 hstep569
  exact h569

/-! ### 16x8 — fwpw7_8 @ step 236 -/
def tm_16_8 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 15⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨0, Dir.L, some 4⟩
  | 0, 6 => some ⟨0, Dir.L, some 10⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 9⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 4⟩
  | 4, 5 => some ⟨1, Dir.R, some 15⟩
  | 4, 6 => some ⟨0, Dir.L, some 9⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.R, some 3⟩
  | 6, 5 => some ⟨0, Dir.L, some 8⟩
  | 6, 6 => some ⟨0, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 0⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨2, Dir.R, some 12⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.R, some 0⟩
  | 8, 5 => some ⟨0, Dir.L, some 0⟩
  | 8, 6 => some ⟨1, Dir.L, some 2⟩
  | 8, 7 => some ⟨1, Dir.L, some 0⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨1, Dir.L, some 13⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => none
  | 9, 5 => some ⟨4, Dir.L, some 10⟩
  | 9, 6 => none
  | 9, 7 => some ⟨1, Dir.L, some 10⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨0, Dir.L, some 12⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨2, Dir.L, some 13⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => none
  | 10, 7 => some ⟨4, Dir.L, some 8⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨1, Dir.L, some 14⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => none
  | 11, 5 => none
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => none
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => none
  | 12, 2 => some ⟨5, Dir.L, some 15⟩
  | 12, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 4 => none
  | 12, 5 => some ⟨6, Dir.L, some 14⟩
  | 12, 6 => some ⟨7, Dir.L, some 13⟩
  | 12, 7 => some ⟨6, Dir.L, some 11⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 1 => some ⟨2, Dir.L, some 0⟩
  | 13, 2 => some ⟨7, Dir.L, some 13⟩
  | 13, 3 => some ⟨7, Dir.L, some 13⟩
  | 13, 4 => none
  | 13, 5 => none
  | 13, 6 => some ⟨2, Dir.R, some 14⟩
  | 13, 7 => some ⟨2, Dir.R, some 7⟩
  | 14, 0 => some ⟨3, Dir.R, some 13⟩
  | 14, 1 => some ⟨0, Dir.L, some 0⟩
  | 14, 2 => some ⟨6, Dir.L, some 14⟩
  | 14, 3 => some ⟨6, Dir.L, some 14⟩
  | 14, 4 => none
  | 14, 5 => some ⟨2, Dir.R, some 15⟩
  | 14, 6 => some ⟨2, Dir.R, some 12⟩
  | 14, 7 => none
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 1 => some ⟨0, Dir.R, some 9⟩
  | 15, 2 => some ⟨5, Dir.L, some 15⟩
  | 15, 3 => some ⟨5, Dir.L, some 15⟩
  | 15, 4 => none
  | 15, 5 => some ⟨2, Dir.R, some 12⟩
  | 15, 6 => some ⟨0, Dir.R, some 3⟩
  | 15, 7 => some ⟨0, Dir.R, some 7⟩
  | _, _ => none

theorem valid_16_8 : ValidTM 16 8 tm_16_8 := by
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
      | 0 => exact ⟨by decide, by decide⟩
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
    | 6 =>
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
    | 7 =>
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
    | 8 =>
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
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 | 6 => trivial
      | _ + 8 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 6 => trivial
      | _ + 8 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 4 | 5 | 7 => trivial
      | _ + 8 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 1 | 4 => trivial
      | _ + 8 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 | 5 => trivial
      | _ + 8 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 4 | 7 => trivial
      | _ + 8 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 => trivial
      | _ + 8 => omega
    | _ + 16 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 16 => rfl

def landmark_16_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 2] }
theorem reaches_landmark_16_8 : steps tm_16_8 236 initConfig = some landmark_16_8 := by
  have h0 : steps tm_16_8 35 initConfig = some { st := some 5, left := [6], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_16_8 35 { st := some 5, left := [6], cur := 0, right := [] } = some { st := some 2, left := [2, 7], cur := 1, right := [1] } := rfl
  have h1 : steps tm_16_8 70 initConfig = some { st := some 2, left := [2, 7], cur := 1, right := [1] } := steps_add tm_16_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_8 35 { st := some 2, left := [2, 7], cur := 1, right := [1] } = some { st := some 6, left := [0, 0, 2, 3], cur := 6, right := [] } := rfl
  have h2 : steps tm_16_8 105 initConfig = some { st := some 6, left := [0, 0, 2, 3], cur := 6, right := [] } := steps_add tm_16_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_8 35 { st := some 6, left := [0, 0, 2, 3], cur := 6, right := [] } = some { st := some 6, left := [3, 0, 2, 3], cur := 6, right := [] } := rfl
  have h3 : steps tm_16_8 140 initConfig = some { st := some 6, left := [3, 0, 2, 3], cur := 6, right := [] } := steps_add tm_16_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_8 35 { st := some 6, left := [3, 0, 2, 3], cur := 6, right := [] } = some { st := some 0, left := [5, 5, 6, 7, 3, 3, 3], cur := 0, right := [] } := rfl
  have h4 : steps tm_16_8 175 initConfig = some { st := some 0, left := [5, 5, 6, 7, 3, 3, 3], cur := 0, right := [] } := steps_add tm_16_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_8 35 { st := some 0, left := [5, 5, 6, 7, 3, 3, 3], cur := 0, right := [] } = some { st := some 13, left := [], cur := 0, right := [7, 7, 7, 7, 7, 2] } := rfl
  have h5 : steps tm_16_8 210 initConfig = some { st := some 13, left := [], cur := 0, right := [7, 7, 7, 7, 7, 2] } := steps_add tm_16_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_16_8 26 { st := some 13, left := [], cur := 0, right := [7, 7, 7, 7, 7, 2] } = some { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 2] } := rfl
  have h6 : steps tm_16_8 236 initConfig = some { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 2] } := steps_add tm_16_8 210 26 initConfig _ _ h5 hstep6
  exact h6

/-! ### 19x8 — fe1_8 @ step 218 -/
def tm_19_8 : TM
  | 0, 0 => some ⟨6, Dir.L, some 11⟩
  | 0, 1 => none
  | 0, 2 => some ⟨0, Dir.R, some 5⟩
  | 0, 3 => some ⟨0, Dir.R, some 3⟩
  | 0, 4 => some ⟨1, Dir.L, some 13⟩
  | 0, 5 => some ⟨6, Dir.R, some 5⟩
  | 0, 6 => none
  | 0, 7 => none
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 1⟩
  | 1, 2 => some ⟨2, Dir.L, some 2⟩
  | 1, 3 => some ⟨5, Dir.L, some 10⟩
  | 1, 4 => some ⟨1, Dir.R, some 1⟩
  | 1, 5 => some ⟨5, Dir.L, some 2⟩
  | 1, 6 => some ⟨7, Dir.L, some 10⟩
  | 1, 7 => none
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 2⟩
  | 2, 3 => some ⟨3, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 2⟩
  | 2, 5 => some ⟨5, Dir.R, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 2, 7 => some ⟨5, Dir.R, some 2⟩
  | 3, 0 => some ⟨1, Dir.L, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨6, Dir.R, some 5⟩
  | 3, 5 => some ⟨5, Dir.R, some 3⟩
  | 3, 6 => some ⟨6, Dir.L, some 9⟩
  | 3, 7 => some ⟨7, Dir.R, some 16⟩
  | 4, 0 => some ⟨3, Dir.L, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => none
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => none
  | 4, 7 => some ⟨6, Dir.L, some 13⟩
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨6, Dir.L, some 9⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => none
  | 5, 7 => none
  | 6, 0 => some ⟨0, Dir.R, some 8⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨1, Dir.L, some 17⟩
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 6, 4 => none
  | 6, 5 => some ⟨5, Dir.R, some 15⟩
  | 6, 6 => some ⟨6, Dir.R, some 8⟩
  | 6, 7 => none
  | 7, 0 => some ⟨2, Dir.L, some 0⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.L, some 7⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨7, Dir.L, some 15⟩
  | 7, 5 => some ⟨5, Dir.L, some 7⟩
  | 7, 6 => some ⟨5, Dir.L, some 0⟩
  | 7, 7 => none
  | 8, 0 => some ⟨3, Dir.R, some 15⟩
  | 8, 1 => none
  | 8, 2 => some ⟨0, Dir.L, some 0⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 5⟩
  | 8, 5 => some ⟨2, Dir.L, some 17⟩
  | 8, 6 => none
  | 8, 7 => none
  | 9, 0 => some ⟨2, Dir.R, some 14⟩
  | 9, 1 => some ⟨5, Dir.R, some 14⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => none
  | 9, 5 => some ⟨5, Dir.L, some 9⟩
  | 9, 6 => some ⟨1, Dir.R, some 5⟩
  | 9, 7 => some ⟨6, Dir.R, some 6⟩
  | 10, 0 => some ⟨2, Dir.L, some 11⟩
  | 10, 1 => some ⟨7, Dir.R, some 3⟩
  | 10, 2 => some ⟨2, Dir.R, some 10⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 10⟩
  | 10, 5 => some ⟨5, Dir.R, some 10⟩
  | 10, 6 => some ⟨6, Dir.R, some 10⟩
  | 10, 7 => none
  | 11, 0 => some ⟨3, Dir.R, some 14⟩
  | 11, 1 => some ⟨2, Dir.R, some 14⟩
  | 11, 2 => some ⟨2, Dir.L, some 11⟩
  | 11, 3 => some ⟨3, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 11⟩
  | 11, 5 => some ⟨5, Dir.L, some 11⟩
  | 11, 6 => some ⟨6, Dir.L, some 11⟩
  | 11, 7 => some ⟨5, Dir.R, some 14⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 1 => some ⟨4, Dir.R, some 14⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.R, some 12⟩
  | 12, 5 => some ⟨5, Dir.R, some 12⟩
  | 12, 6 => some ⟨6, Dir.R, some 12⟩
  | 12, 7 => none
  | 13, 0 => some ⟨1, Dir.R, some 1⟩
  | 13, 1 => some ⟨1, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 4 => some ⟨1, Dir.L, some 14⟩
  | 13, 5 => some ⟨5, Dir.L, some 13⟩
  | 13, 6 => some ⟨7, Dir.R, some 4⟩
  | 13, 7 => some ⟨4, Dir.L, some 5⟩
  | 14, 0 => some ⟨1, Dir.R, some 1⟩
  | 14, 1 => some ⟨4, Dir.R, some 15⟩
  | 14, 2 => some ⟨1, Dir.R, some 10⟩
  | 14, 3 => some ⟨0, Dir.R, some 12⟩
  | 14, 4 => some ⟨4, Dir.L, some 13⟩
  | 14, 5 => some ⟨7, Dir.R, some 16⟩
  | 14, 6 => some ⟨6, Dir.L, some 13⟩
  | 14, 7 => some ⟨1, Dir.L, some 1⟩
  | 15, 0 => some ⟨4, Dir.L, some 9⟩
  | 15, 1 => some ⟨1, Dir.R, some 15⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨3, Dir.R, some 15⟩
  | 15, 4 => some ⟨0, Dir.R, some 15⟩
  | 15, 5 => some ⟨5, Dir.R, some 15⟩
  | 15, 6 => some ⟨6, Dir.R, some 15⟩
  | 15, 7 => some ⟨7, Dir.L, some 12⟩
  | 16, 0 => some ⟨5, Dir.L, some 11⟩
  | 16, 1 => none
  | 16, 2 => some ⟨2, Dir.R, some 16⟩
  | 16, 3 => some ⟨3, Dir.R, some 16⟩
  | 16, 4 => some ⟨4, Dir.R, some 16⟩
  | 16, 5 => some ⟨5, Dir.R, some 16⟩
  | 16, 6 => some ⟨6, Dir.R, some 16⟩
  | 16, 7 => none
  | 17, 0 => some ⟨1, Dir.R, some 1⟩
  | 17, 1 => some ⟨4, Dir.R, some 18⟩
  | 17, 2 => some ⟨2, Dir.L, some 17⟩
  | 17, 3 => some ⟨3, Dir.L, some 17⟩
  | 17, 4 => some ⟨4, Dir.L, some 17⟩
  | 17, 5 => some ⟨5, Dir.L, some 17⟩
  | 17, 6 => some ⟨7, Dir.L, some 17⟩
  | 17, 7 => some ⟨4, Dir.L, some 13⟩
  | 18, 0 => some ⟨2, Dir.L, some 17⟩
  | 18, 1 => none
  | 18, 2 => some ⟨2, Dir.R, some 18⟩
  | 18, 3 => some ⟨3, Dir.R, some 18⟩
  | 18, 4 => some ⟨4, Dir.R, some 18⟩
  | 18, 5 => some ⟨5, Dir.R, some 18⟩
  | 18, 6 => none
  | 18, 7 => none
  | _, _ => none

theorem valid_19_8 : ValidTM 19 8 tm_19_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 6 | 7 => trivial
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
      | 7 => trivial
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
      | 5 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 | 6 => trivial
      | _ + 8 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 | 7 => trivial
      | _ + 8 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 4 | 7 => trivial
      | _ + 8 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => trivial
      | _ + 8 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 6 | 7 => trivial
      | _ + 8 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 => trivial
      | _ + 8 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => trivial
      | _ + 8 => omega
    | 11 =>
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
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => trivial
      | _ + 8 => omega
    | 13 =>
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
    | 14 =>
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
    | 15 =>
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
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 | 7 => trivial
      | _ + 8 => omega
    | 17 =>
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
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 6 | 7 => trivial
      | _ + 8 => omega
    | _ + 19 => omega
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
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
      | _ + 8 => rfl
    | _ + 19 => rfl

def landmark_19_8 : Config := { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_19_8 : steps tm_19_8 218 initConfig = some landmark_19_8 := by
  have h0 : steps tm_19_8 35 initConfig = some { st := some 14, left := [5, 7], cur := 5, right := [5, 6, 5] } := rfl
  have hstep1 : steps tm_19_8 35 { st := some 14, left := [5, 7], cur := 5, right := [5, 6, 5] } = some { st := some 9, left := [5, 5, 6, 5, 5, 5, 0, 3], cur := 5, right := [4] } := rfl
  have h1 : steps tm_19_8 70 initConfig = some { st := some 9, left := [5, 5, 6, 5, 5, 5, 0, 3], cur := 5, right := [4] } := steps_add tm_19_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_19_8 35 { st := some 9, left := [5, 5, 6, 5, 5, 5, 0, 3], cur := 5, right := [4] } = some { st := some 11, left := [5, 6, 7, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } := rfl
  have h2 : steps tm_19_8 105 initConfig = some { st := some 11, left := [5, 6, 7, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } := steps_add tm_19_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_19_8 35 { st := some 11, left := [5, 6, 7, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } = some { st := some 17, left := [5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 2] } := rfl
  have h3 : steps tm_19_8 140 initConfig = some { st := some 17, left := [5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 2] } := steps_add tm_19_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_19_8 35 { st := some 17, left := [5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 2] } = some { st := some 17, left := [], cur := 7, right := [5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1] } := rfl
  have h4 : steps tm_19_8 175 initConfig = some { st := some 17, left := [], cur := 7, right := [5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1] } := steps_add tm_19_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_19_8 35 { st := some 17, left := [], cur := 7, right := [5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1] } = some { st := some 7, left := [4, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h5 : steps tm_19_8 210 initConfig = some { st := some 7, left := [4, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_19_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_19_8 8 { st := some 7, left := [4, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h6 : steps tm_19_8 218 initConfig = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_19_8 210 8 initConfig _ _ h5 hstep6
  exact h6

end BB.Landmarks2026_11_23.S8
