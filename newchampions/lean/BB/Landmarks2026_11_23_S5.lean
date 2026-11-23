/-
  BB/Landmarks2026_11_23_S5.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs
  for 25 5-symbol landmark machines (2026-11-23 sweep).
-/
import BB.TM

namespace BB.Landmarks2026_11_23.S5
open BB

/-! ### 3x5 — fw_4 @ step 263 -/
def tm_3_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨2, Dir.L, some 1⟩
  | 1, 0 => some ⟨4, Dir.L, some 2⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨2, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 1⟩
  | _, _ => none

theorem valid_3_5 : ValidTM 3 5 tm_3_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 3 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 3 => rfl

def landmark_3_5 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] }
theorem reaches_landmark_3_5 : steps tm_3_5 263 initConfig = some landmark_3_5 := by
  have h0 : steps tm_3_5 35 initConfig = some { st := some 2, left := [2, 3], cur := 1, right := [1, 3] } := rfl
  have hstep1 : steps tm_3_5 35 { st := some 2, left := [2, 3], cur := 1, right := [1, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_3_5 70 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := steps_add tm_3_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_3_5 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 4, right := [] } := rfl
  have h2 : steps tm_3_5 105 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 4, right := [] } := steps_add tm_3_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_3_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 4, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 4] } := rfl
  have h3 : steps tm_3_5 140 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 4] } := steps_add tm_3_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_3_5 35 { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 4] } = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 0, right := [] } := rfl
  have h4 : steps tm_3_5 175 initConfig = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 0, right := [] } := steps_add tm_3_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_3_5 35 { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 1, 2] } := rfl
  have h5 : steps tm_3_5 210 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 1, 2] } := steps_add tm_3_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_3_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 1, 2] } = some { st := some 2, left := [2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2] } := rfl
  have h6 : steps tm_3_5 245 initConfig = some { st := some 2, left := [2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2] } := steps_add tm_3_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_3_5 18 { st := some 2, left := [2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := rfl
  have h7 : steps tm_3_5 263 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := steps_add tm_3_5 245 18 initConfig _ _ h6 hstep7
  exact h7

/-! ### 4x5 — fw1_4 @ step 308 -/
def tm_4_5 : TM
  | 0, 0 => some ⟨4, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨0, Dir.L, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨1, Dir.R, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨4, Dir.R, some 3⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨2, Dir.L, some 3⟩
  | _, _ => none

theorem valid_4_5 : ValidTM 4 5 tm_4_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 4 => rfl

def landmark_4_5 : Config := { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2, 2] }
theorem reaches_landmark_4_5 : steps tm_4_5 308 initConfig = some landmark_4_5 := by
  have h0 : steps tm_4_5 35 initConfig = some { st := some 0, left := [3], cur := 3, right := [1, 1, 3, 1, 4] } := rfl
  have hstep1 : steps tm_4_5 35 { st := some 0, left := [3], cur := 3, right := [1, 1, 3, 1, 4] } = some { st := some 2, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 3, 4] } := rfl
  have h1 : steps tm_4_5 70 initConfig = some { st := some 2, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 3, 4] } := steps_add tm_4_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_5 35 { st := some 2, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 3, 4] } = some { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 3, 4] } := rfl
  have h2 : steps tm_4_5 105 initConfig = some { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 3, 4] } := steps_add tm_4_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_5 35 { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 3, 4] } = some { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 4] } := rfl
  have h3 : steps tm_4_5 140 initConfig = some { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 4] } := steps_add tm_4_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_5 35 { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 4] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 3, 4] } := rfl
  have h4 : steps tm_4_5 175 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 3, 4] } := steps_add tm_4_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_5 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 3, 4] } = some { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 4] } := rfl
  have h5 : steps tm_4_5 210 initConfig = some { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 4] } := steps_add tm_4_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_5 35 { st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 4] } = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4] } := rfl
  have h6 : steps tm_4_5 245 initConfig = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4] } := steps_add tm_4_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_5 35 { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 2, 2, 2] } := rfl
  have h7 : steps tm_4_5 280 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 2, 2, 2] } := steps_add tm_4_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_4_5 28 { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 2, 2, 2] } = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2, 2] } := rfl
  have h8 : steps tm_4_5 308 initConfig = some { st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2, 2, 2] } := steps_add tm_4_5 280 28 initConfig _ _ h7 hstep8
  exact h8

/-! ### 4x5 — fw_4 @ step 248 -/
def tm_4_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 3⟩
  | 3, 0 => some ⟨0, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 1⟩
  | 3, 2 => some ⟨4, Dir.L, some 2⟩
  | 3, 3 => some ⟨1, Dir.R, some 1⟩
  | 3, 4 => some ⟨2, Dir.L, some 1⟩
  | _, _ => none

theorem valid_4_5_1 : ValidTM 4 5 tm_4_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 4 => rfl

def landmark_4_5_1 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] }
theorem reaches_landmark_4_5_1 : steps tm_4_5_1 248 initConfig = some landmark_4_5_1 := by
  have h0 : steps tm_4_5_1 35 initConfig = some { st := some 2, left := [2], cur := 3, right := [1] } := rfl
  have hstep1 : steps tm_4_5_1 35 { st := some 2, left := [2], cur := 3, right := [1] } = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [] } := rfl
  have h1 : steps tm_4_5_1 70 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [] } := steps_add tm_4_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [] } = some { st := some 2, left := [2, 2, 2, 3, 3, 3, 3], cur := 0, right := [] } := rfl
  have h2 : steps tm_4_5_1 105 initConfig = some { st := some 2, left := [2, 2, 2, 3, 3, 3, 3], cur := 0, right := [] } := steps_add tm_4_5_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_5_1 35 { st := some 2, left := [2, 2, 2, 3, 3, 3, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4] } := rfl
  have h3 : steps tm_4_5_1 140 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4] } := steps_add tm_4_5_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_5_1 35 { st := some 2, left := [2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4] } = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 1, right := [] } := rfl
  have h4 : steps tm_4_5_1 175 initConfig = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 1, right := [] } := steps_add tm_4_5_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_5_1 35 { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 1, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 2] } := rfl
  have h5 : steps tm_4_5_1 210 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 2] } := steps_add tm_4_5_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 1, 1, 2] } := rfl
  have h6 : steps tm_4_5_1 245 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 1, 1, 2] } := steps_add tm_4_5_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_5_1 3 { st := some 0, left := [2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 1, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := rfl
  have h7 : steps tm_4_5_1 248 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := steps_add tm_4_5_1 245 3 initConfig _ _ h6 hstep7
  exact h7

/-! ### 5x5 — fw1_4 @ step 89 -/
def tm_5_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨0, Dir.L, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 3⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨4, Dir.R, some 3⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.R, some 0⟩
  | 4, 0 => some ⟨0, Dir.L, some 2⟩
  | 4, 1 => some ⟨2, Dir.R, some 0⟩
  | 4, 2 => some ⟨4, Dir.L, some 2⟩
  | 4, 3 => some ⟨1, Dir.R, some 0⟩
  | 4, 4 => some ⟨2, Dir.L, some 4⟩
  | _, _ => none

theorem valid_5_5 : ValidTM 5 5 tm_5_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 5 => rfl

def landmark_5_5 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2] }
theorem reaches_landmark_5_5 : steps tm_5_5 89 initConfig = some landmark_5_5 := by
  have h0 : steps tm_5_5 35 initConfig = some { st := some 4, left := [3, 3], cur := 2, right := [] } := rfl
  have hstep1 : steps tm_5_5 35 { st := some 4, left := [3, 3], cur := 2, right := [] } = some { st := some 2, left := [4, 4, 2], cur := 4, right := [4] } := rfl
  have h1 : steps tm_5_5 70 initConfig = some { st := some 2, left := [4, 4, 2], cur := 4, right := [4] } := steps_add tm_5_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_5 19 { st := some 2, left := [4, 4, 2], cur := 4, right := [4] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2] } := rfl
  have h2 : steps tm_5_5 89 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2] } := steps_add tm_5_5 70 19 initConfig _ _ h1 hstep2
  exact h2

/-! ### 5x5 — fw1_5 @ step 2541 -/
def tm_5_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨2, Dir.L, some 2⟩
  | 3, 2 => some ⟨4, Dir.L, some 2⟩
  | 3, 3 => some ⟨1, Dir.L, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 4, 0 => some ⟨0, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.L, some 4⟩
  | 4, 2 => some ⟨4, Dir.L, some 1⟩
  | 4, 3 => some ⟨1, Dir.R, some 1⟩
  | 4, 4 => some ⟨3, Dir.L, some 2⟩
  | _, _ => none

theorem valid_5_5_1 : ValidTM 5 5 tm_5_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 5 => rfl

def landmark_5_5_1 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 4] }
theorem reaches_landmark_5_5_1 : steps tm_5_5_1 2541 initConfig = some landmark_5_5_1 := by
  have h0 : steps tm_5_5_1 35 initConfig = some { st := some 1, left := [3, 3, 3], cur := 4, right := [1] } := rfl
  have hstep1 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3], cur := 4, right := [1] } = some { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 2] } := rfl
  have h1 : steps tm_5_5_1 70 initConfig = some { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 2] } := steps_add tm_5_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_5_1 35 { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 2] } := rfl
  have h2 : steps tm_5_5_1 105 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 2] } := steps_add tm_5_5_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 2] } = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 2] } := rfl
  have h3 : steps tm_5_5_1 140 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_5_1 35 { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 2] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2] } := rfl
  have h4 : steps tm_5_5_1 175 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_5_1 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2] } = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2] } := rfl
  have h5 : steps tm_5_5_1 210 initConfig = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_5_1 35 { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2] } := rfl
  have h6 : steps tm_5_5_1 245 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2] } := steps_add tm_5_5_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_5_1 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 2] } := rfl
  have h7 : steps tm_5_5_1 280 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 2] } := steps_add tm_5_5_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 2] } := rfl
  have h8 : steps tm_5_5_1 315 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 2] } := steps_add tm_5_5_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h9 : steps tm_5_5_1 350 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h10 : steps tm_5_5_1 385 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_5_5_1 35 { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h11 : steps tm_5_5_1 420 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_5_5_1 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h12 : steps tm_5_5_1 455 initConfig = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_5_5_1 35 { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h13 : steps tm_5_5_1 490 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_5_5_1 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h14 : steps tm_5_5_1 525 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h15 : steps tm_5_5_1 560 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h16 : steps tm_5_5_1 595 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_5_5_1 35 { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h17 : steps tm_5_5_1 630 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h18 : steps tm_5_5_1 665 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h19 : steps tm_5_5_1 700 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h20 : steps tm_5_5_1 735 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } := rfl
  have h21 : steps tm_5_5_1 770 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } := rfl
  have h22 : steps tm_5_5_1 805 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_5_5_1 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 2] } := rfl
  have h23 : steps tm_5_5_1 840 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } := rfl
  have h24 : steps tm_5_5_1 875 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } := rfl
  have h25 : steps tm_5_5_1 910 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } := rfl
  have h26 : steps tm_5_5_1 945 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } := steps_add tm_5_5_1 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } := rfl
  have h27 : steps tm_5_5_1 980 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } := steps_add tm_5_5_1 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 2] } := rfl
  have h28 : steps tm_5_5_1 1015 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 2] } := steps_add tm_5_5_1 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } := rfl
  have h29 : steps tm_5_5_1 1050 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } := steps_add tm_5_5_1 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } := rfl
  have h30 : steps tm_5_5_1 1085 initConfig = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } := steps_add tm_5_5_1 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 2] } := rfl
  have h31 : steps tm_5_5_1 1120 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 2] } := steps_add tm_5_5_1 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := rfl
  have h32 : steps tm_5_5_1 1155 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := rfl
  have h33 : steps tm_5_5_1 1190 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_5_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := rfl
  have h34 : steps tm_5_5_1 1225 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } := steps_add tm_5_5_1 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h35 : steps tm_5_5_1 1260 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_5_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h36 : steps tm_5_5_1 1295 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := rfl
  have h37 : steps tm_5_5_1 1330 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } := steps_add tm_5_5_1 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_5_5_1 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4] } := rfl
  have h38 : steps tm_5_5_1 1365 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4] } := steps_add tm_5_5_1 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := rfl
  have h39 : steps tm_5_5_1 1400 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := steps_add tm_5_5_1 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } := rfl
  have h40 : steps tm_5_5_1 1435 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } := rfl
  have h41 : steps tm_5_5_1 1470 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } := steps_add tm_5_5_1 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h42 : steps tm_5_5_1 1505 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := rfl
  have h43 : steps tm_5_5_1 1540 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := steps_add tm_5_5_1 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } := rfl
  have h44 : steps tm_5_5_1 1575 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h45 : steps tm_5_5_1 1610 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h46 : steps tm_5_5_1 1645 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h47 : steps tm_5_5_1 1680 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h48 : steps tm_5_5_1 1715 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h49 : steps tm_5_5_1 1750 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } := rfl
  have h50 : steps tm_5_5_1 1785 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := rfl
  have h51 : steps tm_5_5_1 1820 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } := steps_add tm_5_5_1 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h52 : steps tm_5_5_1 1855 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h53 : steps tm_5_5_1 1890 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h54 : steps tm_5_5_1 1925 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } := rfl
  have h55 : steps tm_5_5_1 1960 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } := steps_add tm_5_5_1 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h56 : steps tm_5_5_1 1995 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h57 : steps tm_5_5_1 2030 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } := rfl
  have h58 : steps tm_5_5_1 2065 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h59 : steps tm_5_5_1 2100 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h60 : steps tm_5_5_1 2135 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [4, 4] } := rfl
  have h61 : steps tm_5_5_1 2170 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [4, 4] } := steps_add tm_5_5_1 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h62 : steps tm_5_5_1 2205 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h63 : steps tm_5_5_1 2240 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h64 : steps tm_5_5_1 2275 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h65 : steps tm_5_5_1 2310 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 4, 4] } := rfl
  have h66 : steps tm_5_5_1 2345 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 4, 4] } = some { st := some 2, left := [2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := rfl
  have h67 : steps tm_5_5_1 2380 initConfig = some { st := some 2, left := [2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } := steps_add tm_5_5_1 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_5_5_1 35 { st := some 2, left := [2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4] } := rfl
  have h68 : steps tm_5_5_1 2415 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4] } := steps_add tm_5_5_1 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_5_5_1 35 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4] } = some { st := some 2, left := [2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 4] } := rfl
  have h69 : steps tm_5_5_1 2450 initConfig = some { st := some 2, left := [2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 4] } := steps_add tm_5_5_1 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 4] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 1, 4, 4] } := rfl
  have h70 : steps tm_5_5_1 2485 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 1, 4, 4] } := steps_add tm_5_5_1 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_5_5_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 1, 4, 4] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 4] } := rfl
  have h71 : steps tm_5_5_1 2520 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 4] } := steps_add tm_5_5_1 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_5_5_1 21 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 4] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := rfl
  have h72 : steps tm_5_5_1 2541 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := steps_add tm_5_5_1 2520 21 initConfig _ _ h71 hstep72
  exact h72

/-! ### 5x5 — fw2_5 @ step 50 -/
def tm_5_5_2 : TM
  | 0, 0 => some ⟨4, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨2, Dir.L, some 4⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨0, Dir.L, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨4, Dir.R, some 4⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨1, Dir.R, some 4⟩
  | 4, 0 => some ⟨2, Dir.R, some 2⟩
  | 4, 1 => some ⟨4, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.L, some 4⟩
  | 4, 4 => some ⟨1, Dir.R, some 3⟩
  | _, _ => none

theorem valid_5_5_2 : ValidTM 5 5 tm_5_5_2 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 5 => rfl

def landmark_5_5_2 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] }
theorem reaches_landmark_5_5_2 : steps tm_5_5_2 50 initConfig = some landmark_5_5_2 := by
  have h0 : steps tm_5_5_2 35 initConfig = some { st := some 4, left := [2, 3], cur := 2, right := [2, 4, 4, 4] } := rfl
  have hstep1 : steps tm_5_5_2 15 { st := some 4, left := [2, 3], cur := 2, right := [2, 4, 4, 4] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] } := rfl
  have h1 : steps tm_5_5_2 50 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] } := steps_add tm_5_5_2 35 15 initConfig _ _ h0 hstep1
  exact h1

/-! ### 6x5 — fw1_4 @ step 685 -/
def tm_6_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨1, Dir.L, some 5⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨1, Dir.R, some 3⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨4, Dir.R, some 3⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨2, Dir.L, some 5⟩
  | 4, 0 => some ⟨0, Dir.L, some 2⟩
  | 4, 1 => some ⟨1, Dir.L, some 5⟩
  | 4, 2 => some ⟨2, Dir.R, some 2⟩
  | 4, 3 => some ⟨0, Dir.L, some 5⟩
  | 4, 4 => some ⟨4, Dir.L, some 0⟩
  | 5, 0 => some ⟨1, Dir.L, some 2⟩
  | 5, 1 => some ⟨2, Dir.R, some 0⟩
  | 5, 2 => some ⟨4, Dir.L, some 2⟩
  | 5, 3 => some ⟨1, Dir.R, some 0⟩
  | 5, 4 => some ⟨4, Dir.L, some 4⟩
  | _, _ => none

theorem valid_6_5 : ValidTM 6 5 tm_6_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 6 => rfl

def landmark_6_5 : Config := { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_6_5 : steps tm_6_5 685 initConfig = some landmark_6_5 := by
  have h0 : steps tm_6_5 35 initConfig = some { st := some 2, left := [1, 3], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_6_5 35 { st := some 2, left := [1, 3], cur := 0, right := [] } = some { st := some 5, left := [], cur := 2, right := [1, 4] } := rfl
  have h1 : steps tm_6_5 70 initConfig = some { st := some 5, left := [], cur := 2, right := [1, 4] } := steps_add tm_6_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_5 35 { st := some 5, left := [], cur := 2, right := [1, 4] } = some { st := some 4, left := [1, 2, 2, 3], cur := 3, right := [] } := rfl
  have h2 : steps tm_6_5 105 initConfig = some { st := some 4, left := [1, 2, 2, 3], cur := 3, right := [] } := steps_add tm_6_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_5 35 { st := some 4, left := [1, 2, 2, 3], cur := 3, right := [] } = some { st := some 2, left := [], cur := 3, right := [3, 3, 4, 1] } := rfl
  have h3 : steps tm_6_5 140 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 3, 4, 1] } := steps_add tm_6_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_5 35 { st := some 2, left := [], cur := 3, right := [3, 3, 4, 1] } = some { st := some 4, left := [4, 4, 1, 3, 2, 2], cur := 3, right := [] } := rfl
  have h4 : steps tm_6_5 175 initConfig = some { st := some 4, left := [4, 4, 1, 3, 2, 2], cur := 3, right := [] } := steps_add tm_6_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_6_5 35 { st := some 4, left := [4, 4, 1, 3, 2, 2], cur := 3, right := [] } = some { st := some 2, left := [], cur := 2, right := [1, 1, 3, 1, 3, 4] } := rfl
  have h5 : steps tm_6_5 210 initConfig = some { st := some 2, left := [], cur := 2, right := [1, 1, 3, 1, 3, 4] } := steps_add tm_6_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_6_5 35 { st := some 2, left := [], cur := 2, right := [1, 1, 3, 1, 3, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 1, right := [3, 3, 4] } := rfl
  have h6 : steps tm_6_5 245 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 1, right := [3, 3, 4] } := steps_add tm_6_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_6_5 35 { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 1, right := [3, 3, 4] } = some { st := some 0, left := [3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 3, 3, 4] } := rfl
  have h7 : steps tm_6_5 280 initConfig = some { st := some 0, left := [3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 3, 3, 4] } := steps_add tm_6_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_6_5 35 { st := some 0, left := [3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 3, 3, 4] } = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4] } := rfl
  have h8 : steps tm_6_5 315 initConfig = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4] } := steps_add tm_6_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_6_5 35 { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 3, 3, 4] } := rfl
  have h9 : steps tm_6_5 350 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 3, 3, 4] } := steps_add tm_6_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_6_5 35 { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 3, 3, 4] } = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4] } := rfl
  have h10 : steps tm_6_5 385 initConfig = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4] } := steps_add tm_6_5 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_6_5 35 { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4] } = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4] } := rfl
  have h11 : steps tm_6_5 420 initConfig = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4] } := steps_add tm_6_5 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_6_5 35 { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4] } = some { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := rfl
  have h12 : steps tm_6_5 455 initConfig = some { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := steps_add tm_6_5 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_6_5 35 { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } = some { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [2, 2] } := rfl
  have h13 : steps tm_6_5 490 initConfig = some { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [2, 2] } := steps_add tm_6_5 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_6_5 35 { st := some 3, left := [4, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [2, 2] } = some { st := some 4, left := [2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 2, 2, 2, 2, 2] } := rfl
  have h14 : steps tm_6_5 525 initConfig = some { st := some 4, left := [2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_6_5 35 { st := some 4, left := [2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 2, 2, 2, 2, 2, 2] } = some { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h15 : steps tm_6_5 560 initConfig = some { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_6_5 35 { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2] } = some { st := some 2, left := [], cur := 0, right := [3, 3, 4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h16 : steps tm_6_5 595 initConfig = some { st := some 2, left := [], cur := 0, right := [3, 3, 4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_6_5 35 { st := some 2, left := [], cur := 0, right := [3, 3, 4, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } = some { st := some 2, left := [], cur := 0, right := [3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h17 : steps tm_6_5 630 initConfig = some { st := some 2, left := [], cur := 0, right := [3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_6_5 35 { st := some 2, left := [], cur := 0, right := [3, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h18 : steps tm_6_5 665 initConfig = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_6_5 20 { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } = some { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h19 : steps tm_6_5 685 initConfig = some { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_6_5 665 20 initConfig _ _ h18 hstep19
  exact h19

/-! ### 6x5 — fw2_4 @ step 1693 -/
def tm_6_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨0, Dir.L, some 2⟩
  | 1, 0 => some ⟨2, Dir.R, some 4⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨0, Dir.R, some 5⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨0, Dir.L, some 5⟩
  | 4, 0 => some ⟨0, Dir.L, some 4⟩
  | 4, 1 => some ⟨1, Dir.R, none⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.L, some 5⟩
  | 4, 4 => some ⟨1, Dir.R, some 5⟩
  | 5, 0 => some ⟨2, Dir.R, some 2⟩
  | 5, 1 => some ⟨4, Dir.L, some 0⟩
  | 5, 2 => some ⟨1, Dir.R, some 1⟩
  | 5, 3 => some ⟨2, Dir.L, some 5⟩
  | 5, 4 => some ⟨4, Dir.R, some 3⟩
  | _, _ => none

theorem valid_6_5_1 : ValidTM 6 5 tm_6_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 6 => rfl

def landmark_6_5_1 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] }
theorem reaches_landmark_6_5_1 : steps tm_6_5_1 1693 initConfig = some landmark_6_5_1 := by
  have h0 : steps tm_6_5_1 35 initConfig = some { st := some 0, left := [1], cur := 2, right := [4, 0, 4] } := rfl
  have hstep1 : steps tm_6_5_1 35 { st := some 0, left := [1], cur := 2, right := [4, 0, 4] } = some { st := some 2, left := [], cur := 0, right := [3, 3, 1, 1, 0, 4, 0, 4] } := rfl
  have h1 : steps tm_6_5_1 70 initConfig = some { st := some 2, left := [], cur := 0, right := [3, 3, 1, 1, 0, 4, 0, 4] } := steps_add tm_6_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_5_1 35 { st := some 2, left := [], cur := 0, right := [3, 3, 1, 1, 0, 4, 0, 4] } = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 3, 3, 1, 0, 4, 0, 4] } := rfl
  have h2 : steps tm_6_5_1 105 initConfig = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 3, 3, 1, 0, 4, 0, 4] } := steps_add tm_6_5_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_5_1 35 { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 3, 3, 1, 0, 4, 0, 4] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 0, 4, 0, 4] } := rfl
  have h3 : steps tm_6_5_1 140 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 0, 4, 0, 4] } := steps_add tm_6_5_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_5_1 35 { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 0, 4, 0, 4] } = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 0, 4, 0, 4] } := rfl
  have h4 : steps tm_6_5_1 175 initConfig = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 0, 4, 0, 4] } := steps_add tm_6_5_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 3, 0, 4, 0, 4] } = some { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 0, 4, 0, 4] } := rfl
  have h5 : steps tm_6_5_1 210 initConfig = some { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 0, 4, 0, 4] } := steps_add tm_6_5_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_6_5_1 35 { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 0, 4, 0, 4] } = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 0, 4, 0, 4] } := rfl
  have h6 : steps tm_6_5_1 245 initConfig = some { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 0, 4, 0, 4] } := steps_add tm_6_5_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 3, 0, 4, 0, 4] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 3, 0, 4, 0, 4] } := rfl
  have h7 : steps tm_6_5_1 280 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 3, 0, 4, 0, 4] } := steps_add tm_6_5_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 3, 0, 4, 0, 4] } = some { st := some 1, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [4, 0, 4] } := rfl
  have h8 : steps tm_6_5_1 315 initConfig = some { st := some 1, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [4, 0, 4] } := steps_add tm_6_5_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_6_5_1 35 { st := some 1, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [4, 0, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 4, 0, 1] } := rfl
  have h9 : steps tm_6_5_1 350 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_6_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h10 : steps tm_6_5_1 385 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_6_5_1 35 { st := some 2, left := [2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3], cur := 1, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h11 : steps tm_6_5_1 420 initConfig = some { st := some 2, left := [2, 3], cur := 1, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_6_5_1 35 { st := some 2, left := [2, 3], cur := 1, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h12 : steps tm_6_5_1 455 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h13 : steps tm_6_5_1 490 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h14 : steps tm_6_5_1 525 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h15 : steps tm_6_5_1 560 initConfig = some { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_6_5_1 35 { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h16 : steps tm_6_5_1 595 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h17 : steps tm_6_5_1 630 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h18 : steps tm_6_5_1 665 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h19 : steps tm_6_5_1 700 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h20 : steps tm_6_5_1 735 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h21 : steps tm_6_5_1 770 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h22 : steps tm_6_5_1 805 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h23 : steps tm_6_5_1 840 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h24 : steps tm_6_5_1 875 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h25 : steps tm_6_5_1 910 initConfig = some { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h26 : steps tm_6_5_1 945 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h27 : steps tm_6_5_1 980 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } := rfl
  have h28 : steps tm_6_5_1 1015 initConfig = some { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_6_5_1 35 { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 4, 0, 1] } := rfl
  have h29 : steps tm_6_5_1 1050 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } := rfl
  have h30 : steps tm_6_5_1 1085 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } := rfl
  have h31 : steps tm_6_5_1 1120 initConfig = some { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_6_5_1 35 { st := some 0, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 0, 1] } := rfl
  have h32 : steps tm_6_5_1 1155 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } := rfl
  have h33 : steps tm_6_5_1 1190 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } := rfl
  have h34 : steps tm_6_5_1 1225 initConfig = some { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } := steps_add tm_6_5_1 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_6_5_1 35 { st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 4, 0, 1] } := rfl
  have h35 : steps tm_6_5_1 1260 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 4, 0, 1] } := steps_add tm_6_5_1 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 1, 4, 0, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := rfl
  have h36 : steps tm_6_5_1 1295 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := steps_add tm_6_5_1 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := rfl
  have h37 : steps tm_6_5_1 1330 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := steps_add tm_6_5_1 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := rfl
  have h38 : steps tm_6_5_1 1365 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } := steps_add tm_6_5_1 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 0, 1] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := rfl
  have h39 : steps tm_6_5_1 1400 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := steps_add tm_6_5_1 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_6_5_1 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := rfl
  have h40 : steps tm_6_5_1 1435 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := steps_add tm_6_5_1 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } = some { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := rfl
  have h41 : steps tm_6_5_1 1470 initConfig = some { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } := steps_add tm_6_5_1 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_6_5_1 35 { st := some 2, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 0, 1] } := rfl
  have h42 : steps tm_6_5_1 1505 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 0, 1] } := steps_add tm_6_5_1 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := rfl
  have h43 : steps tm_6_5_1 1540 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := steps_add tm_6_5_1 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := rfl
  have h44 : steps tm_6_5_1 1575 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := steps_add tm_6_5_1 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_6_5_1 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } = some { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := rfl
  have h45 : steps tm_6_5_1 1610 initConfig = some { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } := steps_add tm_6_5_1 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_6_5_1 35 { st := some 2, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [0, 1] } := rfl
  have h46 : steps tm_6_5_1 1645 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [0, 1] } := steps_add tm_6_5_1 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_6_5_1 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 0, right := [0, 1] } = some { st := some 5, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] } := rfl
  have h47 : steps tm_6_5_1 1680 initConfig = some { st := some 5, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] } := steps_add tm_6_5_1 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_6_5_1 13 { st := some 5, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] } := rfl
  have h48 : steps tm_6_5_1 1693 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1] } := steps_add tm_6_5_1 1680 13 initConfig _ _ h47 hstep48
  exact h48

/-! ### 6x5 — fw3_5 @ step 98 -/
def tm_6_5_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, some 5⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨3, Dir.L, some 5⟩
  | 3, 2 => some ⟨0, Dir.R, some 1⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.L, some 0⟩
  | 4, 2 => some ⟨0, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.L, some 4⟩
  | 4, 4 => some ⟨3, Dir.L, some 2⟩
  | 5, 0 => some ⟨4, Dir.L, some 2⟩
  | 5, 1 => some ⟨0, Dir.R, some 4⟩
  | 5, 2 => some ⟨2, Dir.L, some 5⟩
  | 5, 3 => some ⟨3, Dir.L, some 5⟩
  | 5, 4 => some ⟨3, Dir.L, some 5⟩
  | _, _ => none

theorem valid_6_5_2 : ValidTM 6 5 tm_6_5_2 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 6 => rfl

def landmark_6_5_2 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 1, 1] }
theorem reaches_landmark_6_5_2 : steps tm_6_5_2 98 initConfig = some landmark_6_5_2 := by
  have h0 : steps tm_6_5_2 35 initConfig = some { st := some 0, left := [2, 3, 3], cur := 4, right := [2] } := rfl
  have hstep1 : steps tm_6_5_2 35 { st := some 0, left := [2, 3, 3], cur := 4, right := [2] } = some { st := some 5, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 1, 1] } := rfl
  have h1 : steps tm_6_5_2 70 initConfig = some { st := some 5, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 1, 1] } := steps_add tm_6_5_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_5_2 28 { st := some 5, left := [], cur := 0, right := [3, 3, 3, 3, 3, 3, 1, 1] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 1, 1] } := rfl
  have h2 : steps tm_6_5_2 98 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 1, 1] } := steps_add tm_6_5_2 70 28 initConfig _ _ h1 hstep2
  exact h2

/-! ### 6x5 — fwm2_5 @ step 131 -/
def tm_6_5_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨2, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨2, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨4, Dir.L, some 3⟩
  | 3, 2 => some ⟨1, Dir.L, some 4⟩
  | 3, 3 => some ⟨2, Dir.R, some 3⟩
  | 3, 4 => some ⟨2, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 5⟩
  | 4, 1 => some ⟨1, Dir.L, some 3⟩
  | 4, 2 => some ⟨3, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.R, some 4⟩
  | 4, 4 => some ⟨2, Dir.R, some 1⟩
  | 5, 0 => some ⟨4, Dir.L, some 4⟩
  | 5, 1 => some ⟨3, Dir.R, some 5⟩
  | 5, 2 => some ⟨1, Dir.L, some 0⟩
  | 5, 3 => some ⟨2, Dir.R, some 3⟩
  | 5, 4 => some ⟨4, Dir.L, some 2⟩
  | _, _ => none

theorem valid_6_5_3 : ValidTM 6 5 tm_6_5_3 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 6 => rfl

def landmark_6_5_3 : Config := { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] }
theorem reaches_landmark_6_5_3 : steps tm_6_5_3 131 initConfig = some landmark_6_5_3 := by
  have h0 : steps tm_6_5_3 35 initConfig = some { st := some 4, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 2] } := rfl
  have hstep1 : steps tm_6_5_3 35 { st := some 4, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 2] } = some { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } := rfl
  have h1 : steps tm_6_5_3 70 initConfig = some { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } := steps_add tm_6_5_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_5_3 35 { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } = some { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } := rfl
  have h2 : steps tm_6_5_3 105 initConfig = some { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } := steps_add tm_6_5_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_5_3 26 { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] } := rfl
  have h3 : steps tm_6_5_3 131 initConfig = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] } := steps_add tm_6_5_3 105 26 initConfig _ _ h2 hstep3
  exact h3

/-! ### 7x5 — fw1_5 @ step 108 -/
def tm_7_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨2, Dir.R, some 1⟩
  | 3, 2 => some ⟨4, Dir.R, some 6⟩
  | 3, 3 => some ⟨2, Dir.R, some 5⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 4, 0 => some ⟨0, Dir.L, some 2⟩
  | 4, 1 => some ⟨1, Dir.L, some 6⟩
  | 4, 2 => some ⟨2, Dir.R, some 2⟩
  | 4, 3 => some ⟨0, Dir.L, some 5⟩
  | 4, 4 => some ⟨3, Dir.L, some 2⟩
  | 5, 0 => some ⟨1, Dir.L, some 2⟩
  | 5, 1 => some ⟨1, Dir.R, some 6⟩
  | 5, 2 => some ⟨2, Dir.R, some 6⟩
  | 5, 3 => some ⟨0, Dir.L, some 6⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨1, Dir.L, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 3⟩
  | 6, 2 => some ⟨4, Dir.L, some 0⟩
  | 6, 3 => some ⟨1, Dir.R, some 1⟩
  | 6, 4 => some ⟨1, Dir.L, some 3⟩
  | _, _ => none

theorem valid_7_5 : ValidTM 7 5 tm_7_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4] }
theorem reaches_landmark_7_5 : steps tm_7_5 108 initConfig = some landmark_7_5 := by
  have h0 : steps tm_7_5 35 initConfig = some { st := some 6, left := [], cur := 3, right := [1] } := rfl
  have hstep1 : steps tm_7_5 35 { st := some 6, left := [], cur := 3, right := [1] } = some { st := some 5, left := [4, 3, 3, 3], cur := 2, right := [1] } := rfl
  have h1 : steps tm_7_5 70 initConfig = some { st := some 5, left := [4, 3, 3, 3], cur := 2, right := [1] } := steps_add tm_7_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_5 35 { st := some 5, left := [4, 3, 3, 3], cur := 2, right := [1] } = some { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4] } := rfl
  have h2 : steps tm_7_5 105 initConfig = some { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4] } := steps_add tm_7_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_5 3 { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4] } := rfl
  have h3 : steps tm_7_5 108 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4] } := steps_add tm_7_5 105 3 initConfig _ _ h2 hstep3
  exact h3

/-! ### 7x5 — fw2_4 @ step 87 -/
def tm_7_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨0, Dir.L, some 6⟩
  | 1, 0 => some ⟨2, Dir.R, some 4⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨3, Dir.L, some 6⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.R, some 0⟩
  | 4, 0 => some ⟨0, Dir.L, some 4⟩
  | 4, 1 => some ⟨1, Dir.R, none⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.L, some 5⟩
  | 4, 4 => some ⟨4, Dir.L, some 0⟩
  | 5, 0 => some ⟨2, Dir.R, some 2⟩
  | 5, 1 => some ⟨1, Dir.R, some 3⟩
  | 5, 2 => some ⟨0, Dir.L, some 6⟩
  | 5, 3 => some ⟨2, Dir.L, some 5⟩
  | 5, 4 => some ⟨4, Dir.R, some 5⟩
  | 6, 0 => some ⟨0, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.R, some 0⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨4, Dir.L, some 0⟩
  | 6, 4 => some ⟨0, Dir.L, some 4⟩
  | _, _ => none

theorem valid_7_5_1 : ValidTM 7 5 tm_7_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5_1 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 0, 0, 0, 1] }
theorem reaches_landmark_7_5_1 : steps tm_7_5_1 87 initConfig = some landmark_7_5_1 := by
  have h0 : steps tm_7_5_1 35 initConfig = some { st := some 0, left := [3], cur := 3, right := [4, 0, 0, 1] } := rfl
  have hstep1 : steps tm_7_5_1 35 { st := some 0, left := [3], cur := 3, right := [4, 0, 0, 1] } = some { st := some 6, left := [2, 2, 3, 3], cur := 4, right := [0, 0, 1] } := rfl
  have h1 : steps tm_7_5_1 70 initConfig = some { st := some 6, left := [2, 2, 3, 3], cur := 4, right := [0, 0, 1] } := steps_add tm_7_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_5_1 17 { st := some 6, left := [2, 2, 3, 3], cur := 4, right := [0, 0, 1] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 0, 0, 0, 1] } := rfl
  have h2 : steps tm_7_5_1 87 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 0, 0, 0, 1] } := steps_add tm_7_5_1 70 17 initConfig _ _ h1 hstep2
  exact h2

/-! ### 7x5 — fw2_5 @ step 138 -/
def tm_7_5_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨2, Dir.L, some 4⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 3⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨4, Dir.L, some 4⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 4, 0 => some ⟨2, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.R, some 0⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.L, some 4⟩
  | 4, 4 => some ⟨1, Dir.L, some 5⟩
  | 5, 0 => some ⟨0, Dir.L, some 2⟩
  | 5, 1 => some ⟨1, Dir.L, some 6⟩
  | 5, 2 => some ⟨4, Dir.L, some 2⟩
  | 5, 3 => some ⟨0, Dir.L, some 6⟩
  | 5, 4 => some ⟨4, Dir.R, some 4⟩
  | 6, 0 => some ⟨0, Dir.L, some 4⟩
  | 6, 1 => some ⟨1, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 2⟩
  | 6, 3 => some ⟨1, Dir.R, some 0⟩
  | 6, 4 => some ⟨4, Dir.R, some 0⟩
  | _, _ => none

theorem valid_7_5_2 : ValidTM 7 5 tm_7_5_2 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5_2 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 4, 4, 4] }
theorem reaches_landmark_7_5_2 : steps tm_7_5_2 138 initConfig = some landmark_7_5_2 := by
  have h0 : steps tm_7_5_2 35 initConfig = some { st := some 5, left := [3], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_7_5_2 35 { st := some 5, left := [3], cur := 1, right := [] } = some { st := some 4, left := [2], cur := 4, right := [4] } := rfl
  have h1 : steps tm_7_5_2 70 initConfig = some { st := some 4, left := [2], cur := 4, right := [4] } := steps_add tm_7_5_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_5_2 35 { st := some 4, left := [2], cur := 4, right := [4] } = some { st := some 3, left := [4, 2, 3], cur := 1, right := [4] } := rfl
  have h2 : steps tm_7_5_2 105 initConfig = some { st := some 3, left := [4, 2, 3], cur := 1, right := [4] } := steps_add tm_7_5_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_5_2 33 { st := some 3, left := [4, 2, 3], cur := 1, right := [4] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 4, 4, 4] } := rfl
  have h3 : steps tm_7_5_2 138 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 4, 4, 4] } := steps_add tm_7_5_2 105 33 initConfig _ _ h2 hstep3
  exact h3

/-! ### 7x5 — fw3_5 @ step 184 -/
def tm_7_5_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨3, Dir.L, some 5⟩
  | 3, 2 => some ⟨0, Dir.L, some 4⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨1, Dir.R, some 6⟩
  | 4, 2 => some ⟨0, Dir.L, some 5⟩
  | 4, 3 => some ⟨4, Dir.L, some 4⟩
  | 4, 4 => some ⟨3, Dir.L, some 2⟩
  | 5, 0 => some ⟨4, Dir.L, some 2⟩
  | 5, 1 => some ⟨4, Dir.R, some 4⟩
  | 5, 2 => some ⟨1, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.L, some 5⟩
  | 5, 4 => some ⟨3, Dir.L, some 5⟩
  | 6, 0 => some ⟨0, Dir.L, some 2⟩
  | 6, 1 => some ⟨2, Dir.L, some 4⟩
  | 6, 2 => some ⟨0, Dir.R, some 2⟩
  | 6, 3 => some ⟨1, Dir.R, some 1⟩
  | 6, 4 => some ⟨1, Dir.L, some 5⟩
  | _, _ => none

theorem valid_7_5_3 : ValidTM 7 5 tm_7_5_3 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5_3 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] }
theorem reaches_landmark_7_5_3 : steps tm_7_5_3 184 initConfig = some landmark_7_5_3 := by
  have h0 : steps tm_7_5_3 35 initConfig = some { st := some 1, left := [2, 3], cur := 2, right := [4, 2] } := rfl
  have hstep1 : steps tm_7_5_3 35 { st := some 1, left := [2, 3], cur := 2, right := [4, 2] } = some { st := some 0, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [2] } := rfl
  have h1 : steps tm_7_5_3 70 initConfig = some { st := some 0, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [2] } := steps_add tm_7_5_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_5_3 35 { st := some 0, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [2] } = some { st := some 5, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [0, 2] } := rfl
  have h2 : steps tm_7_5_3 105 initConfig = some { st := some 5, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [0, 2] } := steps_add tm_7_5_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_5_3 35 { st := some 5, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [0, 2] } = some { st := some 6, left := [0, 1, 4, 4, 3, 3, 3, 3, 3], cur := 1, right := [] } := rfl
  have h3 : steps tm_7_5_3 140 initConfig = some { st := some 6, left := [0, 1, 4, 4, 3, 3, 3, 3, 3], cur := 1, right := [] } := steps_add tm_7_5_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_5_3 35 { st := some 6, left := [0, 1, 4, 4, 3, 3, 3, 3, 3], cur := 1, right := [] } = some { st := some 1, left := [2, 3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] } := rfl
  have h4 : steps tm_7_5_3 175 initConfig = some { st := some 1, left := [2, 3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] } := steps_add tm_7_5_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_5_3 9 { st := some 1, left := [2, 3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] } := rfl
  have h5 : steps tm_7_5_3 184 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 3, 3, 3, 3, 3, 3, 3, 1, 1] } := steps_add tm_7_5_3 175 9 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x5 — fwm2fw_5 @ step 20 -/
def tm_7_5_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨2, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, none⟩
  | 3, 1 => some ⟨4, Dir.L, some 3⟩
  | 3, 2 => some ⟨1, Dir.L, some 4⟩
  | 3, 3 => some ⟨2, Dir.R, some 3⟩
  | 3, 4 => some ⟨2, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 5⟩
  | 4, 1 => some ⟨1, Dir.L, some 3⟩
  | 4, 2 => some ⟨3, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.R, some 4⟩
  | 4, 4 => some ⟨3, Dir.L, some 5⟩
  | 5, 0 => some ⟨0, Dir.L, some 1⟩
  | 5, 1 => some ⟨3, Dir.R, some 5⟩
  | 5, 2 => some ⟨4, Dir.L, some 4⟩
  | 5, 3 => some ⟨2, Dir.R, some 3⟩
  | 5, 4 => some ⟨4, Dir.L, some 2⟩
  | 6, 0 => some ⟨0, Dir.R, some 6⟩
  | 6, 1 => some ⟨0, Dir.L, some 2⟩
  | 6, 2 => some ⟨4, Dir.R, some 2⟩
  | 6, 3 => some ⟨2, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 1⟩
  | _, _ => none

theorem valid_7_5_4 : ValidTM 7 5 tm_7_5_4 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5_4 : Config := { st := some 0, left := [2, 3], cur := 1, right := [] }
theorem reaches_landmark_7_5_4 : steps tm_7_5_4 20 initConfig = some landmark_7_5_4 := by
  have h0 : steps tm_7_5_4 20 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [] } := rfl
  exact h0

/-! ### 8x5 — dfwm2_5 @ step 110 -/
def tm_8_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨2, Dir.L, some 5⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.L, some 7⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨2, Dir.L, some 1⟩
  | 4, 0 => some ⟨0, Dir.L, some 5⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 7⟩
  | 4, 4 => some ⟨1, Dir.R, none⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨3, Dir.L, some 6⟩
  | 5, 2 => some ⟨0, Dir.L, some 4⟩
  | 5, 3 => some ⟨2, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨1, Dir.R, some 0⟩
  | 6, 1 => some ⟨3, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 7⟩
  | 6, 3 => some ⟨2, Dir.R, some 5⟩
  | 6, 4 => some ⟨2, Dir.R, some 0⟩
  | 7, 0 => some ⟨3, Dir.R, some 6⟩
  | 7, 1 => some ⟨1, Dir.L, some 6⟩
  | 7, 2 => some ⟨3, Dir.L, some 7⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | _, _ => none

theorem valid_8_5 : ValidTM 8 5 tm_8_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, trivial⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 8 => rfl

def landmark_8_5 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 2] }
theorem reaches_landmark_8_5 : steps tm_8_5 110 initConfig = some landmark_8_5 := by
  have h0 : steps tm_8_5 35 initConfig = some { st := some 5, left := [2, 3, 3, 3], cur := 2, right := [] } := rfl
  have hstep1 : steps tm_8_5 35 { st := some 5, left := [2, 3, 3, 3], cur := 2, right := [] } = some { st := some 7, left := [2, 3], cur := 1, right := [0, 3, 4] } := rfl
  have h1 : steps tm_8_5 70 initConfig = some { st := some 7, left := [2, 3], cur := 1, right := [0, 3, 4] } := steps_add tm_8_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_5 35 { st := some 7, left := [2, 3], cur := 1, right := [0, 3, 4] } = some { st := some 2, left := [2, 2], cur := 1, right := [1, 1, 1, 2] } := rfl
  have h2 : steps tm_8_5 105 initConfig = some { st := some 2, left := [2, 2], cur := 1, right := [1, 1, 1, 2] } := steps_add tm_8_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_8_5 5 { st := some 2, left := [2, 2], cur := 1, right := [1, 1, 1, 2] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 2] } := rfl
  have h3 : steps tm_8_5 110 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 1, 1, 1, 2] } := steps_add tm_8_5 105 5 initConfig _ _ h2 hstep3
  exact h3

/-! ### 8x5 — fwm21_5 @ step 82 -/
def tm_8_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨4, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.L, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.L, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨3, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 5⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 7⟩
  | 4, 3 => some ⟨4, Dir.L, some 7⟩
  | 4, 4 => some ⟨4, Dir.R, some 1⟩
  | 5, 0 => some ⟨0, Dir.L, some 4⟩
  | 5, 1 => some ⟨3, Dir.L, some 6⟩
  | 5, 2 => some ⟨1, Dir.R, some 0⟩
  | 5, 3 => some ⟨2, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.L, some 5⟩
  | 6, 1 => some ⟨3, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 7⟩
  | 6, 3 => some ⟨2, Dir.R, some 5⟩
  | 6, 4 => some ⟨2, Dir.R, some 0⟩
  | 7, 0 => some ⟨3, Dir.R, some 6⟩
  | 7, 1 => some ⟨1, Dir.L, some 6⟩
  | 7, 2 => some ⟨3, Dir.L, some 7⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | _, _ => none

theorem valid_8_5_1 : ValidTM 8 5 tm_8_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 8 => rfl

def landmark_8_5_1 : Config := { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] }
theorem reaches_landmark_8_5_1 : steps tm_8_5_1 82 initConfig = some landmark_8_5_1 := by
  have h0 : steps tm_8_5_1 35 initConfig = some { st := some 4, left := [3, 3, 3], cur := 4, right := [4, 4] } := rfl
  have hstep1 : steps tm_8_5_1 35 { st := some 4, left := [3, 3, 3], cur := 4, right := [4, 4] } = some { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } := rfl
  have h1 : steps tm_8_5_1 70 initConfig = some { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } := steps_add tm_8_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_5_1 12 { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := rfl
  have h2 : steps tm_8_5_1 82 initConfig = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := steps_add tm_8_5_1 70 12 initConfig _ _ h1 hstep2
  exact h2

/-! ### 9x5 — fwm21_5 @ step 124 -/
def tm_9_5 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨4, Dir.L, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 6⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨3, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 5⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 7⟩
  | 4, 4 => some ⟨4, Dir.R, some 1⟩
  | 5, 0 => some ⟨0, Dir.L, some 4⟩
  | 5, 1 => some ⟨3, Dir.L, some 6⟩
  | 5, 2 => some ⟨0, Dir.L, some 8⟩
  | 5, 3 => some ⟨2, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨0, Dir.L, some 8⟩
  | 6, 1 => some ⟨3, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 7⟩
  | 6, 3 => some ⟨2, Dir.R, some 5⟩
  | 6, 4 => some ⟨2, Dir.R, some 0⟩
  | 7, 0 => some ⟨3, Dir.R, some 6⟩
  | 7, 1 => some ⟨1, Dir.L, some 6⟩
  | 7, 2 => some ⟨3, Dir.L, some 7⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨0, Dir.L, some 7⟩
  | 8, 1 => some ⟨2, Dir.L, some 5⟩
  | 8, 2 => some ⟨4, Dir.R, some 6⟩
  | 8, 3 => some ⟨1, Dir.L, some 2⟩
  | 8, 4 => some ⟨4, Dir.R, some 7⟩
  | _, _ => none

theorem valid_9_5 : ValidTM 9 5 tm_9_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 9 => rfl

def landmark_9_5 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 4] }
theorem reaches_landmark_9_5 : steps tm_9_5 124 initConfig = some landmark_9_5 := by
  have h0 : steps tm_9_5 35 initConfig = some { st := some 3, left := [], cur := 3, right := [1, 4, 1] } := rfl
  have hstep1 : steps tm_9_5 35 { st := some 3, left := [], cur := 3, right := [1, 4, 1] } = some { st := some 2, left := [2, 3, 3], cur := 3, right := [3, 4] } := rfl
  have h1 : steps tm_9_5 70 initConfig = some { st := some 2, left := [2, 3, 3], cur := 3, right := [3, 4] } := steps_add tm_9_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_9_5 35 { st := some 2, left := [2, 3, 3], cur := 3, right := [3, 4] } = some { st := some 2, left := [2, 2, 3], cur := 2, right := [3, 1, 4] } := rfl
  have h2 : steps tm_9_5 105 initConfig = some { st := some 2, left := [2, 2, 3], cur := 2, right := [3, 1, 4] } := steps_add tm_9_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_9_5 19 { st := some 2, left := [2, 2, 3], cur := 2, right := [3, 1, 4] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 4] } := rfl
  have h3 : steps tm_9_5 124 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 4] } := steps_add tm_9_5 105 19 initConfig _ _ h2 hstep3
  exact h3

/-! ### 10x5 — fwp21_5 @ step 210 -/
def tm_10_5 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 0, 4 => some ⟨4, Dir.R, some 8⟩
  | 1, 0 => some ⟨0, Dir.L, some 9⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 1, 4 => some ⟨4, Dir.R, some 0⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 2, 4 => some ⟨0, Dir.R, some 9⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨4, Dir.R, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨0, Dir.R, some 4⟩
  | 5, 0 => some ⟨3, Dir.L, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨0, Dir.R, some 9⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.L, some 1⟩
  | 8, 0 => some ⟨0, Dir.R, some 2⟩
  | 8, 1 => some ⟨3, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 8⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.R, some 9⟩
  | 9, 0 => some ⟨0, Dir.L, some 4⟩
  | 9, 1 => some ⟨0, Dir.L, some 1⟩
  | 9, 2 => some ⟨0, Dir.L, some 9⟩
  | 9, 3 => some ⟨4, Dir.L, some 0⟩
  | 9, 4 => some ⟨3, Dir.R, some 4⟩
  | _, _ => none

theorem valid_10_5 : ValidTM 10 5 tm_10_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, trivial⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 10 => rfl

def landmark_10_5 : Config := { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 0, 4] }
theorem reaches_landmark_10_5 : steps tm_10_5 210 initConfig = some landmark_10_5 := by
  have h0 : steps tm_10_5 35 initConfig = some { st := some 0, left := [], cur := 2, right := [4] } := rfl
  have hstep1 : steps tm_10_5 35 { st := some 0, left := [], cur := 2, right := [4] } = some { st := some 8, left := [2, 1], cur := 4, right := [3, 4] } := rfl
  have h1 : steps tm_10_5 70 initConfig = some { st := some 8, left := [2, 1], cur := 4, right := [3, 4] } := steps_add tm_10_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_10_5 35 { st := some 8, left := [2, 1], cur := 4, right := [3, 4] } = some { st := some 3, left := [3, 4, 4, 2, 1], cur := 1, right := [4] } := rfl
  have h2 : steps tm_10_5 105 initConfig = some { st := some 3, left := [3, 4, 4, 2, 1], cur := 1, right := [4] } := steps_add tm_10_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_10_5 35 { st := some 3, left := [3, 4, 4, 2, 1], cur := 1, right := [4] } = some { st := some 4, left := [4, 4, 2, 1], cur := 3, right := [1, 4] } := rfl
  have h3 : steps tm_10_5 140 initConfig = some { st := some 4, left := [4, 4, 2, 1], cur := 3, right := [1, 4] } := steps_add tm_10_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_10_5 35 { st := some 4, left := [4, 4, 2, 1], cur := 3, right := [1, 4] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [4, 2, 4] } := rfl
  have h4 : steps tm_10_5 175 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [4, 2, 4] } := steps_add tm_10_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_10_5 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [4, 2, 4] } = some { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 0, 4] } := rfl
  have h5 : steps tm_10_5 210 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 0, 4] } := steps_add tm_10_5 175 35 initConfig _ _ h4 hstep5
  exact h5

/-! ### 10x5 — fwp22_5_sw @ step 51 -/
def tm_10_5_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨2, Dir.L, some 7⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 5⟩
  | 0, 4 => some ⟨2, Dir.R, some 3⟩
  | 1, 0 => some ⟨1, Dir.L, some 3⟩
  | 1, 1 => some ⟨2, Dir.R, some 6⟩
  | 1, 2 => some ⟨2, Dir.L, some 1⟩
  | 1, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 4 => some ⟨3, Dir.L, some 6⟩
  | 2, 0 => some ⟨0, Dir.L, some 9⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 0⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 2, 4 => some ⟨1, Dir.R, none⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨0, Dir.L, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨3, Dir.L, some 5⟩
  | 5, 0 => some ⟨4, Dir.R, some 2⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨3, Dir.L, some 8⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨1, Dir.L, some 5⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 1⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.R, some 8⟩
  | 8, 0 => some ⟨0, Dir.R, some 2⟩
  | 8, 1 => some ⟨3, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 8⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.R, some 3⟩
  | 9, 0 => some ⟨3, Dir.R, some 1⟩
  | 9, 1 => some ⟨4, Dir.L, some 9⟩
  | 9, 2 => some ⟨4, Dir.L, some 9⟩
  | 9, 3 => some ⟨4, Dir.L, some 9⟩
  | 9, 4 => some ⟨2, Dir.L, some 5⟩
  | _, _ => none

theorem valid_10_5_1 : ValidTM 10 5 tm_10_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, trivial⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 10 => rfl

def landmark_10_5_1 : Config := { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] }
theorem reaches_landmark_10_5_1 : steps tm_10_5_1 51 initConfig = some landmark_10_5_1 := by
  have h0 : steps tm_10_5_1 35 initConfig = some { st := some 3, left := [], cur := 4, right := [1, 1, 0, 4] } := rfl
  have hstep1 : steps tm_10_5_1 16 { st := some 3, left := [], cur := 4, right := [1, 1, 0, 4] } = some { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] } := rfl
  have h1 : steps tm_10_5_1 51 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] } := steps_add tm_10_5_1 35 16 initConfig _ _ h0 hstep1
  exact h1

/-! ### 11x5 — fwp21_5 @ step 156 -/
def tm_11_5 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 0, 4 => some ⟨4, Dir.L, some 10⟩
  | 1, 0 => some ⟨0, Dir.L, some 9⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 1, 4 => some ⟨4, Dir.L, some 10⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 2, 4 => some ⟨2, Dir.R, some 4⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨1, Dir.L, some 10⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨4, Dir.R, some 0⟩
  | 5, 0 => some ⟨3, Dir.L, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 4⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.R, some 10⟩
  | 8, 0 => some ⟨0, Dir.R, some 2⟩
  | 8, 1 => some ⟨3, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 8⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.R, some 1⟩
  | 9, 0 => some ⟨0, Dir.L, some 4⟩
  | 9, 1 => some ⟨0, Dir.L, some 1⟩
  | 9, 2 => some ⟨0, Dir.L, some 9⟩
  | 9, 3 => some ⟨0, Dir.L, some 10⟩
  | 9, 4 => some ⟨4, Dir.L, some 9⟩
  | 10, 0 => some ⟨1, Dir.R, some 4⟩
  | 10, 1 => some ⟨2, Dir.L, some 9⟩
  | 10, 2 => some ⟨4, Dir.L, some 0⟩
  | 10, 3 => some ⟨2, Dir.R, some 4⟩
  | 10, 4 => some ⟨0, Dir.R, some 8⟩
  | _, _ => none

theorem valid_11_5 : ValidTM 11 5 tm_11_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, trivial⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 11 => rfl

def landmark_11_5 : Config := { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 4] }
theorem reaches_landmark_11_5 : steps tm_11_5 156 initConfig = some landmark_11_5 := by
  have h0 : steps tm_11_5 35 initConfig = some { st := some 2, left := [0, 3, 3], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_11_5 35 { st := some 2, left := [0, 3, 3], cur := 0, right := [] } = some { st := some 0, left := [], cur := 1, right := [4, 4] } := rfl
  have h1 : steps tm_11_5 70 initConfig = some { st := some 0, left := [], cur := 1, right := [4, 4] } := steps_add tm_11_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_11_5 35 { st := some 0, left := [], cur := 1, right := [4, 4] } = some { st := some 7, left := [0, 2, 2], cur := 4, right := [2, 1] } := rfl
  have h2 : steps tm_11_5 105 initConfig = some { st := some 7, left := [0, 2, 2], cur := 4, right := [2, 1] } := steps_add tm_11_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_11_5 35 { st := some 7, left := [0, 2, 2], cur := 4, right := [2, 1] } = some { st := some 4, left := [], cur := 0, right := [1, 2, 2, 2, 2, 0, 4] } := rfl
  have h3 : steps tm_11_5 140 initConfig = some { st := some 4, left := [], cur := 0, right := [1, 2, 2, 2, 2, 0, 4] } := steps_add tm_11_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_11_5 16 { st := some 4, left := [], cur := 0, right := [1, 2, 2, 2, 2, 0, 4] } = some { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 4] } := rfl
  have h4 : steps tm_11_5 156 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 0, 0, 0, 0, 0, 4] } := steps_add tm_11_5 140 16 initConfig _ _ h3 hstep4
  exact h4

/-! ### 12x5 — dfwpw_5 @ step 571 -/
def tm_12_5 : TM
  | 0, 0 => some ⟨4, Dir.R, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 0 => some ⟨2, Dir.L, some 2⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 7⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.R, some 10⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨0, Dir.L, some 5⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 6⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨0, Dir.L, some 1⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨3, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 3⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨0, Dir.R, some 0⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.R, some 9⟩
  | _, _ => none

theorem valid_12_5 : ValidTM 12 5 tm_12_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 12 => rfl

def landmark_12_5 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [4, 3] }
theorem reaches_landmark_12_5 : steps tm_12_5 571 initConfig = some landmark_12_5 := by
  have h0 : steps tm_12_5 35 initConfig = some { st := some 3, left := [0, 1, 2, 3, 2, 2, 2, 2], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_12_5 35 { st := some 3, left := [0, 1, 2, 3, 2, 2, 2, 2], cur := 0, right := [] } = some { st := some 9, left := [2, 2, 1, 3, 2, 3, 2, 2, 2, 2], cur := 2, right := [1, 4, 2] } := rfl
  have h1 : steps tm_12_5 70 initConfig = some { st := some 9, left := [2, 2, 1, 3, 2, 3, 2, 2, 2, 2], cur := 2, right := [1, 4, 2] } := steps_add tm_12_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_5 35 { st := some 9, left := [2, 2, 1, 3, 2, 3, 2, 2, 2, 2], cur := 2, right := [1, 4, 2] } = some { st := some 0, left := [2, 3, 3, 1, 2, 3, 2, 2, 2, 2], cur := 1, right := [4, 0, 4, 3] } := rfl
  have h2 : steps tm_12_5 105 initConfig = some { st := some 0, left := [2, 3, 3, 1, 2, 3, 2, 2, 2, 2], cur := 1, right := [4, 0, 4, 3] } := steps_add tm_12_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_5 35 { st := some 0, left := [2, 3, 3, 1, 2, 3, 2, 2, 2, 2], cur := 1, right := [4, 0, 4, 3] } = some { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 1, 3, 4, 0, 4, 3] } := rfl
  have h3 : steps tm_12_5 140 initConfig = some { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 1, 3, 4, 0, 4, 3] } := steps_add tm_12_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_12_5 35 { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 1, 3, 4, 0, 4, 3] } = some { st := some 10, left := [0, 0, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 3, 4, 0, 4, 3] } := rfl
  have h4 : steps tm_12_5 175 initConfig = some { st := some 10, left := [0, 0, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 3, 4, 0, 4, 3] } := steps_add tm_12_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_12_5 35 { st := some 10, left := [0, 0, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 3, 4, 0, 4, 3] } = some { st := some 9, left := [1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 0, 3, 4, 0, 4, 3] } := rfl
  have h5 : steps tm_12_5 210 initConfig = some { st := some 9, left := [1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 0, 3, 4, 0, 4, 3] } := steps_add tm_12_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_12_5 35 { st := some 9, left := [1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 0, right := [1, 0, 3, 4, 0, 4, 3] } = some { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 0, 2, 1, 4, 0, 4, 1, 4, 3] } := rfl
  have h6 : steps tm_12_5 245 initConfig = some { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 0, 2, 1, 4, 0, 4, 1, 4, 3] } := steps_add tm_12_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_12_5 35 { st := some 6, left := [], cur := 2, right := [2, 2, 3, 2, 3, 2, 1, 0, 1, 0, 2, 1, 4, 0, 4, 1, 4, 3] } = some { st := some 6, left := [2, 2], cur := 2, right := [3, 2, 3, 2, 1, 0, 3, 0, 1, 1, 3, 4, 0, 4, 1, 4, 3] } := rfl
  have h7 : steps tm_12_5 280 initConfig = some { st := some 6, left := [2, 2], cur := 2, right := [3, 2, 3, 2, 1, 0, 3, 0, 1, 1, 3, 4, 0, 4, 1, 4, 3] } := steps_add tm_12_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_12_5 35 { st := some 6, left := [2, 2], cur := 2, right := [3, 2, 3, 2, 1, 0, 3, 0, 1, 1, 3, 4, 0, 4, 1, 4, 3] } = some { st := some 11, left := [3, 3, 3, 3, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 3, right := [1, 3, 0, 1, 4, 3] } := rfl
  have h8 : steps tm_12_5 315 initConfig = some { st := some 11, left := [3, 3, 3, 3, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 3, right := [1, 3, 0, 1, 4, 3] } := steps_add tm_12_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_12_5 35 { st := some 11, left := [3, 3, 3, 3, 3, 1, 2, 3, 2, 3, 2, 2, 2, 2], cur := 3, right := [1, 3, 0, 1, 4, 3] } = some { st := some 1, left := [3, 4, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [3] } := rfl
  have h9 : steps tm_12_5 350 initConfig = some { st := some 1, left := [3, 4, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [3] } := steps_add tm_12_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_12_5 35 { st := some 1, left := [3, 4, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 0, 3, 4, 1, 4, 2] } := rfl
  have h10 : steps tm_12_5 385 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 0, 3, 4, 1, 4, 2] } := steps_add tm_12_5 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_12_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 0, 3, 4, 1, 4, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 0, 3, 4, 1, 4, 2] } := rfl
  have h11 : steps tm_12_5 420 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 0, 3, 4, 1, 4, 2] } := steps_add tm_12_5 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_12_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 0, 3, 4, 1, 4, 2] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 4, 1, 4, 2] } := rfl
  have h12 : steps tm_12_5 455 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 4, 1, 4, 2] } := steps_add tm_12_5 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_12_5 35 { st := some 0, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 4, 1, 4, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 2, 3, 3, 1, 4, 3] } := rfl
  have h13 : steps tm_12_5 490 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 2, 3, 3, 1, 4, 3] } := steps_add tm_12_5 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_12_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 2, 3, 3, 1, 4, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [2, 3, 3, 1, 4, 3] } := rfl
  have h14 : steps tm_12_5 525 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [2, 3, 3, 1, 4, 3] } := steps_add tm_12_5 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_12_5 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [2, 3, 3, 1, 4, 3] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 3] } := rfl
  have h15 : steps tm_12_5 560 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 3] } := steps_add tm_12_5 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_12_5 11 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 3] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [4, 3] } := rfl
  have h16 : steps tm_12_5 571 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [4, 3] } := steps_add tm_12_5 560 11 initConfig _ _ h15 hstep16
  exact h16

/-! ### 12x5 — fwp23_4 @ step 378 -/
def tm_12_5_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 0, 4 => some ⟨4, Dir.R, some 4⟩
  | 1, 0 => some ⟨4, Dir.L, some 0⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 1, 4 => some ⟨0, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 2, 4 => some ⟨3, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨4, Dir.R, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨4, Dir.R, some 8⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨4, Dir.R, some 0⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨0, Dir.L, some 1⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.R, some 0⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨1, Dir.R, none⟩
  | 8, 4 => some ⟨3, Dir.L, some 11⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => some ⟨0, Dir.R, some 1⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 1⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨2, Dir.L, some 11⟩
  | _, _ => none

theorem valid_12_5_1 : ValidTM 12 5 tm_12_5_1 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, trivial⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 12 => rfl

def landmark_12_5_1 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3] }
theorem reaches_landmark_12_5_1 : steps tm_12_5_1 378 initConfig = some landmark_12_5_1 := by
  have h0 : steps tm_12_5_1 35 initConfig = some { st := some 7, left := [1], cur := 1, right := [2, 1, 3, 4] } := rfl
  have hstep1 : steps tm_12_5_1 35 { st := some 7, left := [1], cur := 1, right := [2, 1, 3, 4] } = some { st := some 7, left := [1], cur := 2, right := [2, 1, 2, 1, 2, 3, 4] } := rfl
  have h1 : steps tm_12_5_1 70 initConfig = some { st := some 7, left := [1], cur := 2, right := [2, 1, 2, 1, 2, 3, 4] } := steps_add tm_12_5_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_5_1 35 { st := some 7, left := [1], cur := 2, right := [2, 1, 2, 1, 2, 3, 4] } = some { st := some 6, left := [2, 2, 1, 1, 1, 1], cur := 1, right := [2, 2, 3, 4] } := rfl
  have h2 : steps tm_12_5_1 105 initConfig = some { st := some 6, left := [2, 2, 1, 1, 1, 1], cur := 1, right := [2, 2, 3, 4] } := steps_add tm_12_5_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_5_1 35 { st := some 6, left := [2, 2, 1, 1, 1, 1], cur := 1, right := [2, 2, 3, 4] } = some { st := some 2, left := [1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4] } := rfl
  have h3 : steps tm_12_5_1 140 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4] } := steps_add tm_12_5_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_12_5_1 35 { st := some 2, left := [1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4] } = some { st := some 7, left := [1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4] } := rfl
  have h4 : steps tm_12_5_1 175 initConfig = some { st := some 7, left := [1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4] } := steps_add tm_12_5_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_12_5_1 35 { st := some 7, left := [1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4] } = some { st := some 6, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4] } := rfl
  have h5 : steps tm_12_5_1 210 initConfig = some { st := some 6, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4] } := steps_add tm_12_5_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_12_5_1 35 { st := some 6, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4] } = some { st := some 6, left := [2, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4] } := rfl
  have h6 : steps tm_12_5_1 245 initConfig = some { st := some 6, left := [2, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4] } := steps_add tm_12_5_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_12_5_1 35 { st := some 6, left := [2, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4] } = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 2, 2, 3, 4] } := rfl
  have h7 : steps tm_12_5_1 280 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 2, 2, 3, 4] } := steps_add tm_12_5_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_12_5_1 35 { st := some 7, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 2, 2, 3, 4] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 2, 3, 4] } := rfl
  have h8 : steps tm_12_5_1 315 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 2, 3, 4] } := steps_add tm_12_5_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_12_5_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 2, 3, 4] } = some { st := some 4, left := [4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 4, right := [4] } := rfl
  have h9 : steps tm_12_5_1 350 initConfig = some { st := some 4, left := [4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 4, right := [4] } := steps_add tm_12_5_1 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_12_5_1 28 { st := some 4, left := [4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 4, right := [4] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3] } := rfl
  have h10 : steps tm_12_5_1 378 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3] } := steps_add tm_12_5_1 350 28 initConfig _ _ h9 hstep10
  exact h10

/-! ### 12x5 — fwpw_5 @ step 125 -/
def tm_12_5_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.L, some 5⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.R, some 2⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨0, Dir.R, some 5⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨4, Dir.R, some 1⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨4, Dir.L, some 4⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨4, Dir.L, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.L, some 3⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨0, Dir.L, some 3⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 11⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨0, Dir.L, some 5⟩
  | _, _ => none

theorem valid_12_5_2 : ValidTM 12 5 tm_12_5_2 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 12 => rfl

def landmark_12_5_2 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] }
theorem reaches_landmark_12_5_2 : steps tm_12_5_2 125 initConfig = some landmark_12_5_2 := by
  have h0 : steps tm_12_5_2 35 initConfig = some { st := some 2, left := [3, 2], cur := 2, right := [4, 2, 1, 1] } := rfl
  have hstep1 : steps tm_12_5_2 35 { st := some 2, left := [3, 2], cur := 2, right := [4, 2, 1, 1] } = some { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } := rfl
  have h1 : steps tm_12_5_2 70 initConfig = some { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } := steps_add tm_12_5_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_5_2 35 { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } = some { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } := rfl
  have h2 : steps tm_12_5_2 105 initConfig = some { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } := steps_add tm_12_5_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_5_2 20 { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] } := rfl
  have h3 : steps tm_12_5_2 125 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] } := steps_add tm_12_5_2 105 20 initConfig _ _ h2 hstep3
  exact h3

/-! ### 14x5 — fwp23_4 @ step 136 -/
def tm_14_5 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 0, 4 => some ⟨4, Dir.L, some 13⟩
  | 1, 0 => some ⟨0, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 1, 4 => some ⟨4, Dir.L, some 13⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 2, 4 => some ⟨2, Dir.R, some 4⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨1, Dir.L, some 13⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨4, Dir.R, some 0⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨4, Dir.L, some 5⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨2, Dir.R, some 4⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.R, some 8⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨1, Dir.R, none⟩
  | 8, 4 => some ⟨4, Dir.R, some 1⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => some ⟨2, Dir.L, some 11⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 1⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.R, some 6⟩
  | 12, 0 => some ⟨0, Dir.L, some 4⟩
  | 12, 1 => some ⟨0, Dir.L, some 1⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | 12, 3 => some ⟨0, Dir.L, some 13⟩
  | 12, 4 => some ⟨4, Dir.R, some 5⟩
  | 13, 0 => some ⟨1, Dir.R, some 4⟩
  | 13, 1 => some ⟨2, Dir.L, some 12⟩
  | 13, 2 => some ⟨4, Dir.L, some 0⟩
  | 13, 3 => some ⟨2, Dir.R, some 4⟩
  | 13, 4 => some ⟨0, Dir.R, some 5⟩
  | _, _ => none

theorem valid_14_5 : ValidTM 14 5 tm_14_5 := by
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
      | _ + 5 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, trivial⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | _ + 5 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 => omega
      | _ + 5 => rfl
    | _ + 14 => rfl

def landmark_14_5 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 2, 3] }
theorem reaches_landmark_14_5 : steps tm_14_5 136 initConfig = some landmark_14_5 := by
  have h0 : steps tm_14_5 35 initConfig = some { st := some 2, left := [0, 3, 3], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_14_5 35 { st := some 2, left := [0, 3, 3], cur := 0, right := [] } = some { st := some 0, left := [], cur := 1, right := [4, 4] } := rfl
  have h1 : steps tm_14_5 70 initConfig = some { st := some 0, left := [], cur := 1, right := [4, 4] } := steps_add tm_14_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_5 35 { st := some 0, left := [], cur := 1, right := [4, 4] } = some { st := some 8, left := [1, 2, 2], cur := 4, right := [1, 1] } := rfl
  have h2 : steps tm_14_5 105 initConfig = some { st := some 8, left := [1, 2, 2], cur := 4, right := [1, 1] } := steps_add tm_14_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_5 31 { st := some 8, left := [1, 2, 2], cur := 4, right := [1, 1] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 2, 3] } := rfl
  have h3 : steps tm_14_5 136 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 1, 1, 2, 3] } := steps_add tm_14_5 105 31 initConfig _ _ h2 hstep3
  exact h3

end BB.Landmarks2026_11_23.S5
