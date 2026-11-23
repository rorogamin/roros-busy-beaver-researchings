/-
  BB/Landmarks2026_11_23_S4.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs
  for 27 4-symbol landmark machines (2026-11-23 sweep).
-/
import BB.TM

namespace BB.Landmarks2026_11_23.S4
open BB

/-! ### 3x4 — fw_4 @ step 241 -/
def tm_3_4 : TM
  | 0, 0 => some ⟨1, Dir.R, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨2, Dir.L, some 2⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | _, _ => none

theorem valid_3_4 : ValidTM 3 4 tm_3_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 3 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 3 => rfl

def landmark_3_4 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 1, 2] }
theorem reaches_landmark_3_4 : steps tm_3_4 241 initConfig = some landmark_3_4 := by
  have h0 : steps tm_3_4 35 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 2, right := [3] } := rfl
  have hstep1 : steps tm_3_4 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 2, right := [3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3] } := rfl
  have h1 : steps tm_3_4 70 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3] } := steps_add tm_3_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_3_4 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [3, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3] } := rfl
  have h2 : steps tm_3_4 105 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3] } := steps_add tm_3_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_3_4 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3] } := rfl
  have h3 : steps tm_3_4 140 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3] } := steps_add tm_3_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_3_4 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 1, 2] } := rfl
  have h4 : steps tm_3_4 175 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 1, 2] } := steps_add tm_3_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_3_4 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 1, 1, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 1, 1, 1, 2] } := rfl
  have h5 : steps tm_3_4 210 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 1, 1, 1, 2] } := steps_add tm_3_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_3_4 31 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 1, 1, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 1, 2] } := rfl
  have h6 : steps tm_3_4 241 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 1, 2] } := steps_add tm_3_4 210 31 initConfig _ _ h5 hstep6
  exact h6

/-! ### 4x4 — fw_4 @ step 374 -/
def tm_4_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨2, Dir.R, some 2⟩
  | 3, 1 => some ⟨2, Dir.L, some 1⟩
  | 3, 2 => some ⟨1, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | _, _ => none

theorem valid_4_4 : ValidTM 4 4 tm_4_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 4 => rfl

def landmark_4_4 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [2, 3] }
theorem reaches_landmark_4_4 : steps tm_4_4 374 initConfig = some landmark_4_4 := by
  have h0 : steps tm_4_4 35 initConfig = some { st := some 1, left := [3], cur := 2, right := [1, 1, 3, 3] } := rfl
  have hstep1 : steps tm_4_4 35 { st := some 1, left := [3], cur := 2, right := [1, 1, 3, 3] } = some { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 1, 1] } := rfl
  have h1 : steps tm_4_4 70 initConfig = some { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 1, 1] } := steps_add tm_4_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_4 35 { st := some 2, left := [2], cur := 3, right := [1, 1, 1, 1, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1] } := rfl
  have h2 : steps tm_4_4 105 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1] } := steps_add tm_4_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_4 35 { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1] } = some { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 3, 1, 1] } := rfl
  have h3 : steps tm_4_4 140 initConfig = some { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 3, 1, 1] } := steps_add tm_4_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_4 35 { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 3, 1, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1] } := rfl
  have h4 : steps tm_4_4 175 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1] } := steps_add tm_4_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_4 35 { st := some 2, left := [2, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 1] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3] } := rfl
  have h5 : steps tm_4_4 210 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3] } := steps_add tm_4_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_4 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3] } := rfl
  have h6 : steps tm_4_4 245 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3] } := steps_add tm_4_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_4 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 3] } = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } := rfl
  have h7 : steps tm_4_4 280 initConfig = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } := steps_add tm_4_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_4_4 35 { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3] } := rfl
  have h8 : steps tm_4_4 315 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3] } := steps_add tm_4_4 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_4_4 35 { st := some 3, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 2, 3] } := rfl
  have h9 : steps tm_4_4 350 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 2, 3] } := steps_add tm_4_4 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_4_4 24 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 1, 2, 3] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [2, 3] } := rfl
  have h10 : steps tm_4_4 374 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [2, 3] } := steps_add tm_4_4 350 24 initConfig _ _ h9 hstep10
  exact h10

/-! ### 5x4 — fw1_4 @ step 236 -/
def tm_5_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 0⟩
  | 4, 1 => some ⟨1, Dir.R, some 3⟩
  | 4, 2 => some ⟨2, Dir.L, some 2⟩
  | 4, 3 => some ⟨2, Dir.L, some 4⟩
  | _, _ => none

theorem valid_5_4 : ValidTM 5 4 tm_5_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 5 => rfl

def landmark_5_4 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_5_4 : steps tm_5_4 236 initConfig = some landmark_5_4 := by
  have h0 : steps tm_5_4 35 initConfig = some { st := some 0, left := [3, 3, 3], cur := 1, right := [1] } := rfl
  have hstep1 : steps tm_5_4 35 { st := some 0, left := [3, 3, 3], cur := 1, right := [1] } = some { st := some 0, left := [3, 3, 1], cur := 1, right := [1, 1, 1, 2, 2, 2] } := rfl
  have h1 : steps tm_5_4 70 initConfig = some { st := some 0, left := [3, 3, 1], cur := 1, right := [1, 1, 1, 2, 2, 2] } := steps_add tm_5_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_4 35 { st := some 0, left := [3, 3, 1], cur := 1, right := [1, 1, 1, 2, 2, 2] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 1], cur := 1, right := [1, 2, 2] } := rfl
  have h2 : steps tm_5_4 105 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 1], cur := 1, right := [1, 2, 2] } := steps_add tm_5_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_4 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 1], cur := 1, right := [1, 2, 2] } = some { st := some 3, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } := rfl
  have h3 : steps tm_5_4 140 initConfig = some { st := some 3, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } := steps_add tm_5_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_4 35 { st := some 3, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } = some { st := some 2, left := [2, 3, 3, 3, 3, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } := rfl
  have h4 : steps tm_5_4 175 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } := steps_add tm_5_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_4 35 { st := some 2, left := [2, 3, 3, 3, 3, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } = some { st := some 4, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1], cur := 3, right := [] } := rfl
  have h5 : steps tm_5_4 210 initConfig = some { st := some 4, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1], cur := 3, right := [] } := steps_add tm_5_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_4 26 { st := some 4, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1], cur := 3, right := [] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := rfl
  have h6 : steps tm_5_4 236 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] } := steps_add tm_5_4 210 26 initConfig _ _ h5 hstep6
  exact h6

/-! ### 5x4 — fw1fw_4 @ step 25 -/
def tm_5_4_1 : TM
  | 0, 0 => some ⟨1, Dir.R, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 2⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨2, Dir.R, some 2⟩
  | 1, 1 => some ⟨1, Dir.R, none⟩
  | 1, 2 => some ⟨2, Dir.L, some 1⟩
  | 1, 3 => some ⟨2, Dir.L, some 1⟩
  | 2, 0 => some ⟨1, Dir.L, some 3⟩
  | 2, 1 => some ⟨3, Dir.R, some 2⟩
  | 2, 2 => some ⟨1, Dir.L, some 4⟩
  | 2, 3 => some ⟨2, Dir.R, some 0⟩
  | 3, 0 => some ⟨3, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 1⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 2⟩
  | 4, 1 => some ⟨1, Dir.L, some 2⟩
  | 4, 2 => some ⟨3, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.R, some 4⟩
  | _, _ => none

theorem valid_5_4_1 : ValidTM 5 4 tm_5_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 5 => rfl

def landmark_5_4_1 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 3], cur := 1, right := [] }
theorem reaches_landmark_5_4_1 : steps tm_5_4_1 25 initConfig = some landmark_5_4_1 := by
  have h0 : steps tm_5_4_1 25 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 3], cur := 1, right := [] } := rfl
  exact h0

/-! ### 6x4 — fw1_4 @ step 210 -/
def tm_6_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 0⟩
  | 3, 1 => some ⟨2, Dir.L, some 4⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 3⟩
  | 4, 0 => some ⟨0, Dir.L, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 2⟩
  | 4, 2 => some ⟨1, Dir.L, some 5⟩
  | 4, 3 => some ⟨0, Dir.L, some 5⟩
  | 5, 0 => some ⟨1, Dir.L, some 2⟩
  | 5, 1 => some ⟨1, Dir.L, some 5⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨1, Dir.R, some 3⟩
  | _, _ => none

theorem valid_6_4 : ValidTM 6 4 tm_6_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 6 => rfl

def landmark_6_4 : Config := { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 2] }
theorem reaches_landmark_6_4 : steps tm_6_4 210 initConfig = some landmark_6_4 := by
  have h0 : steps tm_6_4 35 initConfig = some { st := some 5, left := [2], cur := 2, right := [] } := rfl
  have hstep1 : steps tm_6_4 35 { st := some 5, left := [2], cur := 2, right := [] } = some { st := some 0, left := [3, 2, 2, 3, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_6_4 70 initConfig = some { st := some 0, left := [3, 2, 2, 3, 3], cur := 0, right := [] } := steps_add tm_6_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_4 35 { st := some 0, left := [3, 2, 2, 3, 3], cur := 0, right := [] } = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 2] } := rfl
  have h2 : steps tm_6_4 105 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 2] } := steps_add tm_6_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_4 35 { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 2] } = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] } := rfl
  have h3 : steps tm_6_4 140 initConfig = some { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] } := steps_add tm_6_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_4 35 { st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] } = some { st := some 5, left := [2, 2, 2, 3, 3, 3], cur := 2, right := [] } := rfl
  have h4 : steps tm_6_4 175 initConfig = some { st := some 5, left := [2, 2, 2, 3, 3, 3], cur := 2, right := [] } := steps_add tm_6_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_6_4 35 { st := some 5, left := [2, 2, 2, 3, 3, 3], cur := 2, right := [] } = some { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 2] } := rfl
  have h5 : steps tm_6_4 210 initConfig = some { st := some 1, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 2] } := steps_add tm_6_4 175 35 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x4 — fw1_3 @ step 182 -/
def tm_7_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨1, Dir.R, some 3⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨0, Dir.L, some 3⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 2⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 5⟩
  | 3, 2 => some ⟨3, Dir.L, some 0⟩
  | 3, 3 => some ⟨3, Dir.R, some 2⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.R, some 6⟩
  | 5, 0 => some ⟨0, Dir.L, some 3⟩
  | 5, 1 => some ⟨0, Dir.L, some 0⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨3, Dir.R, some 1⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 5⟩
  | _, _ => none

theorem valid_7_4 : ValidTM 7 4 tm_7_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 7 => rfl

def landmark_7_4 : Config := { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3] }
theorem reaches_landmark_7_4 : steps tm_7_4 182 initConfig = some landmark_7_4 := by
  have h0 : steps tm_7_4 35 initConfig = some { st := some 0, left := [1, 1], cur := 1, right := [3] } := rfl
  have hstep1 : steps tm_7_4 35 { st := some 0, left := [1, 1], cur := 1, right := [3] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 2, 2, 3] } := rfl
  have h1 : steps tm_7_4 70 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 2, 2, 3] } := steps_add tm_7_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_4 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 2, 2, 3] } = some { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3] } := rfl
  have h2 : steps tm_7_4 105 initConfig = some { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3] } := steps_add tm_7_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_4 35 { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 0, 3] } := rfl
  have h3 : steps tm_7_4 140 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 0, 3] } := steps_add tm_7_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_4 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 0, 3] } = some { st := some 3, left := [0, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := rfl
  have h4 : steps tm_7_4 175 initConfig = some { st := some 3, left := [0, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := steps_add tm_7_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_4 7 { st := some 3, left := [0, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3] } := rfl
  have h5 : steps tm_7_4 182 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3] } := steps_add tm_7_4 175 7 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x4 — fw2_3 @ step 8674 -/
def tm_7_4_1 : TM
  | 0, 0 => some ⟨2, Dir.R, some 6⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨3, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.R, some 0⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 0⟩
  | 3, 3 => some ⟨0, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.L, some 3⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨0, Dir.R, some 3⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨0, Dir.L, some 0⟩
  | _, _ => none

theorem valid_7_4_1 : ValidTM 7 4 tm_7_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 7 => rfl

def landmark_7_4_1 : Config := { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] }
set_option maxHeartbeats 800000 in
theorem reaches_landmark_7_4_1 : steps tm_7_4_1 8674 initConfig = some landmark_7_4_1 := by
  have h0 : steps tm_7_4_1 35 initConfig = some { st := some 1, left := [], cur := 2, right := [3, 3, 0, 1] } := rfl
  have hstep1 : steps tm_7_4_1 35 { st := some 1, left := [], cur := 2, right := [3, 3, 0, 1] } = some { st := some 1, left := [2, 1], cur := 2, right := [2, 2, 3, 0, 1] } := rfl
  have h1 : steps tm_7_4_1 70 initConfig = some { st := some 1, left := [2, 1], cur := 2, right := [2, 2, 3, 0, 1] } := steps_add tm_7_4_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_4_1 35 { st := some 1, left := [2, 1], cur := 2, right := [2, 2, 3, 0, 1] } = some { st := some 2, left := [1, 1], cur := 3, right := [0, 3, 0, 3, 0, 1] } := rfl
  have h2 : steps tm_7_4_1 105 initConfig = some { st := some 2, left := [1, 1], cur := 3, right := [0, 3, 0, 3, 0, 1] } := steps_add tm_7_4_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_4_1 35 { st := some 2, left := [1, 1], cur := 3, right := [0, 3, 0, 3, 0, 1] } = some { st := some 3, left := [3, 3, 3, 2, 2, 1], cur := 3, right := [3, 0, 1] } := rfl
  have h3 : steps tm_7_4_1 140 initConfig = some { st := some 3, left := [3, 3, 3, 2, 2, 1], cur := 3, right := [3, 0, 1] } := steps_add tm_7_4_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_4_1 35 { st := some 3, left := [3, 3, 3, 2, 2, 1], cur := 3, right := [3, 0, 1] } = some { st := some 4, left := [], cur := 0, right := [2, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h4 : steps tm_7_4_1 175 initConfig = some { st := some 4, left := [], cur := 0, right := [2, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_4_1 35 { st := some 4, left := [], cur := 0, right := [2, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h5 : steps tm_7_4_1 210 initConfig = some { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_4_1 35 { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h6 : steps tm_7_4_1 245 initConfig = some { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_4_1 35 { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h7 : steps tm_7_4_1 280 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h8 : steps tm_7_4_1 315 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h9 : steps tm_7_4_1 350 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h10 : steps tm_7_4_1 385 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h11 : steps tm_7_4_1 420 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_7_4_1 35 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h12 : steps tm_7_4_1 455 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := rfl
  have h13 : steps tm_7_4_1 490 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } := steps_add tm_7_4_1 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 0, 3, 0, 0, 0, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h14 : steps tm_7_4_1 525 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h15 : steps tm_7_4_1 560 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h16 : steps tm_7_4_1 595 initConfig = some { st := some 6, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_7_4_1 35 { st := some 6, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h17 : steps tm_7_4_1 630 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_7_4_1 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h18 : steps tm_7_4_1 665 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h19 : steps tm_7_4_1 700 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h20 : steps tm_7_4_1 735 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h21 : steps tm_7_4_1 770 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_7_4_1 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h22 : steps tm_7_4_1 805 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h23 : steps tm_7_4_1 840 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h24 : steps tm_7_4_1 875 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h25 : steps tm_7_4_1 910 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h26 : steps tm_7_4_1 945 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h27 : steps tm_7_4_1 980 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h28 : steps tm_7_4_1 1015 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h29 : steps tm_7_4_1 1050 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_7_4_1 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h30 : steps tm_7_4_1 1085 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h31 : steps tm_7_4_1 1120 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h32 : steps tm_7_4_1 1155 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h33 : steps tm_7_4_1 1190 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h34 : steps tm_7_4_1 1225 initConfig = some { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h35 : steps tm_7_4_1 1260 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h36 : steps tm_7_4_1 1295 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h37 : steps tm_7_4_1 1330 initConfig = some { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h38 : steps tm_7_4_1 1365 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h39 : steps tm_7_4_1 1400 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h40 : steps tm_7_4_1 1435 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h41 : steps tm_7_4_1 1470 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h42 : steps tm_7_4_1 1505 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h43 : steps tm_7_4_1 1540 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h44 : steps tm_7_4_1 1575 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_7_4_1 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3, 0, 1] } := rfl
  have h45 : steps tm_7_4_1 1610 initConfig = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_7_4_1 35 { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h46 : steps tm_7_4_1 1645 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h47 : steps tm_7_4_1 1680 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h48 : steps tm_7_4_1 1715 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2, 0, 3, 0, 1] } := rfl
  have h49 : steps tm_7_4_1 1750 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := rfl
  have h50 : steps tm_7_4_1 1785 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := rfl
  have h51 : steps tm_7_4_1 1820 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := rfl
  have h52 : steps tm_7_4_1 1855 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2, 0, 3, 0, 1] } := rfl
  have h53 : steps tm_7_4_1 1890 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := rfl
  have h54 : steps tm_7_4_1 1925 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := rfl
  have h55 : steps tm_7_4_1 1960 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := rfl
  have h56 : steps tm_7_4_1 1995 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 0, 3, 0, 1] } := rfl
  have h57 : steps tm_7_4_1 2030 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 0, 3, 0, 1] } := steps_add tm_7_4_1 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h58 : steps tm_7_4_1 2065 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h59 : steps tm_7_4_1 2100 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h60 : steps tm_7_4_1 2135 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h61 : steps tm_7_4_1 2170 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h62 : steps tm_7_4_1 2205 initConfig = some { st := some 6, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_7_4_1 35 { st := some 6, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h63 : steps tm_7_4_1 2240 initConfig = some { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_7_4_1 35 { st := some 0, left := [2], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h64 : steps tm_7_4_1 2275 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h65 : steps tm_7_4_1 2310 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h66 : steps tm_7_4_1 2345 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_7_4_1 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h67 : steps tm_7_4_1 2380 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h68 : steps tm_7_4_1 2415 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h69 : steps tm_7_4_1 2450 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_7_4_1 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h70 : steps tm_7_4_1 2485 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h71 : steps tm_7_4_1 2520 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h72 : steps tm_7_4_1 2555 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2520 35 initConfig _ _ h71 hstep72
  have hstep73 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h73 : steps tm_7_4_1 2590 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2555 35 initConfig _ _ h72 hstep73
  have hstep74 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h74 : steps tm_7_4_1 2625 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2590 35 initConfig _ _ h73 hstep74
  have hstep75 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h75 : steps tm_7_4_1 2660 initConfig = some { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2625 35 initConfig _ _ h74 hstep75
  have hstep76 : steps tm_7_4_1 35 { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h76 : steps tm_7_4_1 2695 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2660 35 initConfig _ _ h75 hstep76
  have hstep77 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h77 : steps tm_7_4_1 2730 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2695 35 initConfig _ _ h76 hstep77
  have hstep78 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h78 : steps tm_7_4_1 2765 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2730 35 initConfig _ _ h77 hstep78
  have hstep79 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h79 : steps tm_7_4_1 2800 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2765 35 initConfig _ _ h78 hstep79
  have hstep80 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h80 : steps tm_7_4_1 2835 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2800 35 initConfig _ _ h79 hstep80
  have hstep81 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h81 : steps tm_7_4_1 2870 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2835 35 initConfig _ _ h80 hstep81
  have hstep82 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h82 : steps tm_7_4_1 2905 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2870 35 initConfig _ _ h81 hstep82
  have hstep83 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h83 : steps tm_7_4_1 2940 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2905 35 initConfig _ _ h82 hstep83
  have hstep84 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h84 : steps tm_7_4_1 2975 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2940 35 initConfig _ _ h83 hstep84
  have hstep85 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h85 : steps tm_7_4_1 3010 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 2975 35 initConfig _ _ h84 hstep85
  have hstep86 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h86 : steps tm_7_4_1 3045 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3010 35 initConfig _ _ h85 hstep86
  have hstep87 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h87 : steps tm_7_4_1 3080 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3045 35 initConfig _ _ h86 hstep87
  have hstep88 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h88 : steps tm_7_4_1 3115 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3080 35 initConfig _ _ h87 hstep88
  have hstep89 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h89 : steps tm_7_4_1 3150 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3115 35 initConfig _ _ h88 hstep89
  have hstep90 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h90 : steps tm_7_4_1 3185 initConfig = some { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3150 35 initConfig _ _ h89 hstep90
  have hstep91 : steps tm_7_4_1 35 { st := some 6, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h91 : steps tm_7_4_1 3220 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3185 35 initConfig _ _ h90 hstep91
  have hstep92 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h92 : steps tm_7_4_1 3255 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3220 35 initConfig _ _ h91 hstep92
  have hstep93 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h93 : steps tm_7_4_1 3290 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3255 35 initConfig _ _ h92 hstep93
  have hstep94 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h94 : steps tm_7_4_1 3325 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3290 35 initConfig _ _ h93 hstep94
  have hstep95 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h95 : steps tm_7_4_1 3360 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3325 35 initConfig _ _ h94 hstep95
  have hstep96 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h96 : steps tm_7_4_1 3395 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3360 35 initConfig _ _ h95 hstep96
  have hstep97 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h97 : steps tm_7_4_1 3430 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3395 35 initConfig _ _ h96 hstep97
  have hstep98 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h98 : steps tm_7_4_1 3465 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3430 35 initConfig _ _ h97 hstep98
  have hstep99 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h99 : steps tm_7_4_1 3500 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3465 35 initConfig _ _ h98 hstep99
  have hstep100 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h100 : steps tm_7_4_1 3535 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3500 35 initConfig _ _ h99 hstep100
  have hstep101 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h101 : steps tm_7_4_1 3570 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3535 35 initConfig _ _ h100 hstep101
  have hstep102 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h102 : steps tm_7_4_1 3605 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3570 35 initConfig _ _ h101 hstep102
  have hstep103 : steps tm_7_4_1 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h103 : steps tm_7_4_1 3640 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3605 35 initConfig _ _ h102 hstep103
  have hstep104 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h104 : steps tm_7_4_1 3675 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3640 35 initConfig _ _ h103 hstep104
  have hstep105 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h105 : steps tm_7_4_1 3710 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3675 35 initConfig _ _ h104 hstep105
  have hstep106 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h106 : steps tm_7_4_1 3745 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3710 35 initConfig _ _ h105 hstep106
  have hstep107 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h107 : steps tm_7_4_1 3780 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3745 35 initConfig _ _ h106 hstep107
  have hstep108 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h108 : steps tm_7_4_1 3815 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3780 35 initConfig _ _ h107 hstep108
  have hstep109 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h109 : steps tm_7_4_1 3850 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3815 35 initConfig _ _ h108 hstep109
  have hstep110 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h110 : steps tm_7_4_1 3885 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3850 35 initConfig _ _ h109 hstep110
  have hstep111 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h111 : steps tm_7_4_1 3920 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3885 35 initConfig _ _ h110 hstep111
  have hstep112 : steps tm_7_4_1 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h112 : steps tm_7_4_1 3955 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3920 35 initConfig _ _ h111 hstep112
  have hstep113 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h113 : steps tm_7_4_1 3990 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3955 35 initConfig _ _ h112 hstep113
  have hstep114 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h114 : steps tm_7_4_1 4025 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 3990 35 initConfig _ _ h113 hstep114
  have hstep115 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h115 : steps tm_7_4_1 4060 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4025 35 initConfig _ _ h114 hstep115
  have hstep116 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h116 : steps tm_7_4_1 4095 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4060 35 initConfig _ _ h115 hstep116
  have hstep117 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h117 : steps tm_7_4_1 4130 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4095 35 initConfig _ _ h116 hstep117
  have hstep118 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h118 : steps tm_7_4_1 4165 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4130 35 initConfig _ _ h117 hstep118
  have hstep119 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h119 : steps tm_7_4_1 4200 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4165 35 initConfig _ _ h118 hstep119
  have hstep120 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h120 : steps tm_7_4_1 4235 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4200 35 initConfig _ _ h119 hstep120
  have hstep121 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h121 : steps tm_7_4_1 4270 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4235 35 initConfig _ _ h120 hstep121
  have hstep122 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h122 : steps tm_7_4_1 4305 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4270 35 initConfig _ _ h121 hstep122
  have hstep123 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h123 : steps tm_7_4_1 4340 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4305 35 initConfig _ _ h122 hstep123
  have hstep124 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h124 : steps tm_7_4_1 4375 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4340 35 initConfig _ _ h123 hstep124
  have hstep125 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h125 : steps tm_7_4_1 4410 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4375 35 initConfig _ _ h124 hstep125
  have hstep126 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h126 : steps tm_7_4_1 4445 initConfig = some { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4410 35 initConfig _ _ h125 hstep126
  have hstep127 : steps tm_7_4_1 35 { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h127 : steps tm_7_4_1 4480 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4445 35 initConfig _ _ h126 hstep127
  have hstep128 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h128 : steps tm_7_4_1 4515 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4480 35 initConfig _ _ h127 hstep128
  have hstep129 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h129 : steps tm_7_4_1 4550 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4515 35 initConfig _ _ h128 hstep129
  have hstep130 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h130 : steps tm_7_4_1 4585 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4550 35 initConfig _ _ h129 hstep130
  have hstep131 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h131 : steps tm_7_4_1 4620 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4585 35 initConfig _ _ h130 hstep131
  have hstep132 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h132 : steps tm_7_4_1 4655 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4620 35 initConfig _ _ h131 hstep132
  have hstep133 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h133 : steps tm_7_4_1 4690 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4655 35 initConfig _ _ h132 hstep133
  have hstep134 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h134 : steps tm_7_4_1 4725 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4690 35 initConfig _ _ h133 hstep134
  have hstep135 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h135 : steps tm_7_4_1 4760 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4725 35 initConfig _ _ h134 hstep135
  have hstep136 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h136 : steps tm_7_4_1 4795 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4760 35 initConfig _ _ h135 hstep136
  have hstep137 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h137 : steps tm_7_4_1 4830 initConfig = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4795 35 initConfig _ _ h136 hstep137
  have hstep138 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h138 : steps tm_7_4_1 4865 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4830 35 initConfig _ _ h137 hstep138
  have hstep139 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h139 : steps tm_7_4_1 4900 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4865 35 initConfig _ _ h138 hstep139
  have hstep140 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h140 : steps tm_7_4_1 4935 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4900 35 initConfig _ _ h139 hstep140
  have hstep141 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h141 : steps tm_7_4_1 4970 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4935 35 initConfig _ _ h140 hstep141
  have hstep142 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h142 : steps tm_7_4_1 5005 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 4970 35 initConfig _ _ h141 hstep142
  have hstep143 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h143 : steps tm_7_4_1 5040 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5005 35 initConfig _ _ h142 hstep143
  have hstep144 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h144 : steps tm_7_4_1 5075 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5040 35 initConfig _ _ h143 hstep144
  have hstep145 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h145 : steps tm_7_4_1 5110 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5075 35 initConfig _ _ h144 hstep145
  have hstep146 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h146 : steps tm_7_4_1 5145 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5110 35 initConfig _ _ h145 hstep146
  have hstep147 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h147 : steps tm_7_4_1 5180 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5145 35 initConfig _ _ h146 hstep147
  have hstep148 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h148 : steps tm_7_4_1 5215 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5180 35 initConfig _ _ h147 hstep148
  have hstep149 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h149 : steps tm_7_4_1 5250 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5215 35 initConfig _ _ h148 hstep149
  have hstep150 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h150 : steps tm_7_4_1 5285 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5250 35 initConfig _ _ h149 hstep150
  have hstep151 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h151 : steps tm_7_4_1 5320 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5285 35 initConfig _ _ h150 hstep151
  have hstep152 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h152 : steps tm_7_4_1 5355 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5320 35 initConfig _ _ h151 hstep152
  have hstep153 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h153 : steps tm_7_4_1 5390 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5355 35 initConfig _ _ h152 hstep153
  have hstep154 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h154 : steps tm_7_4_1 5425 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5390 35 initConfig _ _ h153 hstep154
  have hstep155 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h155 : steps tm_7_4_1 5460 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5425 35 initConfig _ _ h154 hstep155
  have hstep156 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h156 : steps tm_7_4_1 5495 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5460 35 initConfig _ _ h155 hstep156
  have hstep157 : steps tm_7_4_1 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h157 : steps tm_7_4_1 5530 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5495 35 initConfig _ _ h156 hstep157
  have hstep158 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h158 : steps tm_7_4_1 5565 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5530 35 initConfig _ _ h157 hstep158
  have hstep159 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h159 : steps tm_7_4_1 5600 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5565 35 initConfig _ _ h158 hstep159
  have hstep160 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h160 : steps tm_7_4_1 5635 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5600 35 initConfig _ _ h159 hstep160
  have hstep161 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h161 : steps tm_7_4_1 5670 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5635 35 initConfig _ _ h160 hstep161
  have hstep162 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h162 : steps tm_7_4_1 5705 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5670 35 initConfig _ _ h161 hstep162
  have hstep163 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h163 : steps tm_7_4_1 5740 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5705 35 initConfig _ _ h162 hstep163
  have hstep164 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h164 : steps tm_7_4_1 5775 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5740 35 initConfig _ _ h163 hstep164
  have hstep165 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h165 : steps tm_7_4_1 5810 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5775 35 initConfig _ _ h164 hstep165
  have hstep166 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h166 : steps tm_7_4_1 5845 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5810 35 initConfig _ _ h165 hstep166
  have hstep167 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h167 : steps tm_7_4_1 5880 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5845 35 initConfig _ _ h166 hstep167
  have hstep168 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h168 : steps tm_7_4_1 5915 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5880 35 initConfig _ _ h167 hstep168
  have hstep169 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h169 : steps tm_7_4_1 5950 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5915 35 initConfig _ _ h168 hstep169
  have hstep170 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h170 : steps tm_7_4_1 5985 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5950 35 initConfig _ _ h169 hstep170
  have hstep171 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h171 : steps tm_7_4_1 6020 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 5985 35 initConfig _ _ h170 hstep171
  have hstep172 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h172 : steps tm_7_4_1 6055 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6020 35 initConfig _ _ h171 hstep172
  have hstep173 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h173 : steps tm_7_4_1 6090 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6055 35 initConfig _ _ h172 hstep173
  have hstep174 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h174 : steps tm_7_4_1 6125 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6090 35 initConfig _ _ h173 hstep174
  have hstep175 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h175 : steps tm_7_4_1 6160 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6125 35 initConfig _ _ h174 hstep175
  have hstep176 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h176 : steps tm_7_4_1 6195 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6160 35 initConfig _ _ h175 hstep176
  have hstep177 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h177 : steps tm_7_4_1 6230 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6195 35 initConfig _ _ h176 hstep177
  have hstep178 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h178 : steps tm_7_4_1 6265 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6230 35 initConfig _ _ h177 hstep178
  have hstep179 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h179 : steps tm_7_4_1 6300 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6265 35 initConfig _ _ h178 hstep179
  have hstep180 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h180 : steps tm_7_4_1 6335 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6300 35 initConfig _ _ h179 hstep180
  have hstep181 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h181 : steps tm_7_4_1 6370 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6335 35 initConfig _ _ h180 hstep181
  have hstep182 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h182 : steps tm_7_4_1 6405 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6370 35 initConfig _ _ h181 hstep182
  have hstep183 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h183 : steps tm_7_4_1 6440 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6405 35 initConfig _ _ h182 hstep183
  have hstep184 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h184 : steps tm_7_4_1 6475 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6440 35 initConfig _ _ h183 hstep184
  have hstep185 : steps tm_7_4_1 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h185 : steps tm_7_4_1 6510 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6475 35 initConfig _ _ h184 hstep185
  have hstep186 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h186 : steps tm_7_4_1 6545 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6510 35 initConfig _ _ h185 hstep186
  have hstep187 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h187 : steps tm_7_4_1 6580 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6545 35 initConfig _ _ h186 hstep187
  have hstep188 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h188 : steps tm_7_4_1 6615 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6580 35 initConfig _ _ h187 hstep188
  have hstep189 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h189 : steps tm_7_4_1 6650 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6615 35 initConfig _ _ h188 hstep189
  have hstep190 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h190 : steps tm_7_4_1 6685 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6650 35 initConfig _ _ h189 hstep190
  have hstep191 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h191 : steps tm_7_4_1 6720 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6685 35 initConfig _ _ h190 hstep191
  have hstep192 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h192 : steps tm_7_4_1 6755 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6720 35 initConfig _ _ h191 hstep192
  have hstep193 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h193 : steps tm_7_4_1 6790 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6755 35 initConfig _ _ h192 hstep193
  have hstep194 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h194 : steps tm_7_4_1 6825 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6790 35 initConfig _ _ h193 hstep194
  have hstep195 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h195 : steps tm_7_4_1 6860 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6825 35 initConfig _ _ h194 hstep195
  have hstep196 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h196 : steps tm_7_4_1 6895 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6860 35 initConfig _ _ h195 hstep196
  have hstep197 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h197 : steps tm_7_4_1 6930 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6895 35 initConfig _ _ h196 hstep197
  have hstep198 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h198 : steps tm_7_4_1 6965 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6930 35 initConfig _ _ h197 hstep198
  have hstep199 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h199 : steps tm_7_4_1 7000 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 6965 35 initConfig _ _ h198 hstep199
  have hstep200 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h200 : steps tm_7_4_1 7035 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7000 35 initConfig _ _ h199 hstep200
  have hstep201 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h201 : steps tm_7_4_1 7070 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7035 35 initConfig _ _ h200 hstep201
  have hstep202 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h202 : steps tm_7_4_1 7105 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7070 35 initConfig _ _ h201 hstep202
  have hstep203 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h203 : steps tm_7_4_1 7140 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7105 35 initConfig _ _ h202 hstep203
  have hstep204 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h204 : steps tm_7_4_1 7175 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7140 35 initConfig _ _ h203 hstep204
  have hstep205 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h205 : steps tm_7_4_1 7210 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7175 35 initConfig _ _ h204 hstep205
  have hstep206 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h206 : steps tm_7_4_1 7245 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7210 35 initConfig _ _ h205 hstep206
  have hstep207 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h207 : steps tm_7_4_1 7280 initConfig = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7245 35 initConfig _ _ h206 hstep207
  have hstep208 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h208 : steps tm_7_4_1 7315 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7280 35 initConfig _ _ h207 hstep208
  have hstep209 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h209 : steps tm_7_4_1 7350 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7315 35 initConfig _ _ h208 hstep209
  have hstep210 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h210 : steps tm_7_4_1 7385 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7350 35 initConfig _ _ h209 hstep210
  have hstep211 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h211 : steps tm_7_4_1 7420 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7385 35 initConfig _ _ h210 hstep211
  have hstep212 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h212 : steps tm_7_4_1 7455 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7420 35 initConfig _ _ h211 hstep212
  have hstep213 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h213 : steps tm_7_4_1 7490 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7455 35 initConfig _ _ h212 hstep213
  have hstep214 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h214 : steps tm_7_4_1 7525 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7490 35 initConfig _ _ h213 hstep214
  have hstep215 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h215 : steps tm_7_4_1 7560 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7525 35 initConfig _ _ h214 hstep215
  have hstep216 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h216 : steps tm_7_4_1 7595 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7560 35 initConfig _ _ h215 hstep216
  have hstep217 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := rfl
  have h217 : steps tm_7_4_1 7630 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7595 35 initConfig _ _ h216 hstep217
  have hstep218 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h218 : steps tm_7_4_1 7665 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7630 35 initConfig _ _ h217 hstep218
  have hstep219 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h219 : steps tm_7_4_1 7700 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7665 35 initConfig _ _ h218 hstep219
  have hstep220 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h220 : steps tm_7_4_1 7735 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7700 35 initConfig _ _ h219 hstep220
  have hstep221 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h221 : steps tm_7_4_1 7770 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7735 35 initConfig _ _ h220 hstep221
  have hstep222 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h222 : steps tm_7_4_1 7805 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7770 35 initConfig _ _ h221 hstep222
  have hstep223 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h223 : steps tm_7_4_1 7840 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7805 35 initConfig _ _ h222 hstep223
  have hstep224 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h224 : steps tm_7_4_1 7875 initConfig = some { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7840 35 initConfig _ _ h223 hstep224
  have hstep225 : steps tm_7_4_1 35 { st := some 0, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h225 : steps tm_7_4_1 7910 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7875 35 initConfig _ _ h224 hstep225
  have hstep226 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := rfl
  have h226 : steps tm_7_4_1 7945 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 7910 35 initConfig _ _ h225 hstep226
  have hstep227 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h227 : steps tm_7_4_1 7980 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 7945 35 initConfig _ _ h226 hstep227
  have hstep228 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h228 : steps tm_7_4_1 8015 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 7980 35 initConfig _ _ h227 hstep228
  have hstep229 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h229 : steps tm_7_4_1 8050 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8015 35 initConfig _ _ h228 hstep229
  have hstep230 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h230 : steps tm_7_4_1 8085 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8050 35 initConfig _ _ h229 hstep230
  have hstep231 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h231 : steps tm_7_4_1 8120 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8085 35 initConfig _ _ h230 hstep231
  have hstep232 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h232 : steps tm_7_4_1 8155 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8120 35 initConfig _ _ h231 hstep232
  have hstep233 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h233 : steps tm_7_4_1 8190 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8155 35 initConfig _ _ h232 hstep233
  have hstep234 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := rfl
  have h234 : steps tm_7_4_1 8225 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8190 35 initConfig _ _ h233 hstep234
  have hstep235 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 0, 3, 0, 1] } := rfl
  have h235 : steps tm_7_4_1 8260 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 0, 3, 0, 1] } := steps_add tm_7_4_1 8225 35 initConfig _ _ h234 hstep235
  have hstep236 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h236 : steps tm_7_4_1 8295 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8260 35 initConfig _ _ h235 hstep236
  have hstep237 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h237 : steps tm_7_4_1 8330 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8295 35 initConfig _ _ h236 hstep237
  have hstep238 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h238 : steps tm_7_4_1 8365 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8330 35 initConfig _ _ h237 hstep238
  have hstep239 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h239 : steps tm_7_4_1 8400 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8365 35 initConfig _ _ h238 hstep239
  have hstep240 : steps tm_7_4_1 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h240 : steps tm_7_4_1 8435 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8400 35 initConfig _ _ h239 hstep240
  have hstep241 : steps tm_7_4_1 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h241 : steps tm_7_4_1 8470 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8435 35 initConfig _ _ h240 hstep241
  have hstep242 : steps tm_7_4_1 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h242 : steps tm_7_4_1 8505 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8470 35 initConfig _ _ h241 hstep242
  have hstep243 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := rfl
  have h243 : steps tm_7_4_1 8540 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } := steps_add tm_7_4_1 8505 35 initConfig _ _ h242 hstep243
  have hstep244 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 0, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 3, 0, 1] } := rfl
  have h244 : steps tm_7_4_1 8575 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 3, 0, 1] } := steps_add tm_7_4_1 8540 35 initConfig _ _ h243 hstep244
  have hstep245 : steps tm_7_4_1 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 3, 0, 1] } = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h245 : steps tm_7_4_1 8610 initConfig = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_7_4_1 8575 35 initConfig _ _ h244 hstep245
  have hstep246 : steps tm_7_4_1 35 { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h246 : steps tm_7_4_1 8645 initConfig = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_7_4_1 8610 35 initConfig _ _ h245 hstep246
  have hstep247 : steps tm_7_4_1 29 { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h247 : steps tm_7_4_1 8674 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_7_4_1 8645 29 initConfig _ _ h246 hstep247
  exact h247

/-! ### 7x4 — fw3_4 @ step 68 -/
def tm_7_4_2 : TM
  | 0, 0 => some ⟨2, Dir.R, some 6⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨1, Dir.L, some 5⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨3, Dir.R, some 0⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 0⟩
  | 3, 3 => some ⟨0, Dir.R, some 0⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.R, some 3⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨0, Dir.L, some 0⟩
  | _, _ => none

theorem valid_7_4_2 : ValidTM 7 4 tm_7_4_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, trivial⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 7 => rfl

def landmark_7_4_2 : Config := { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] }
theorem reaches_landmark_7_4_2 : steps tm_7_4_2 68 initConfig = some landmark_7_4_2 := by
  have h0 : steps tm_7_4_2 35 initConfig = some { st := some 6, left := [2, 2, 1], cur := 0, right := [2, 3, 1, 1] } := rfl
  have hstep1 : steps tm_7_4_2 33 { st := some 6, left := [2, 2, 1], cur := 0, right := [2, 3, 1, 1] } = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] } := rfl
  have h1 : steps tm_7_4_2 68 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] } := steps_add tm_7_4_2 35 33 initConfig _ _ h0 hstep1
  exact h1

/-! ### 7x4 — fw_3 @ step 509 -/
def tm_7_4_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨0, Dir.L, some 6⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 6⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.L, some 6⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 4, 3 => some ⟨1, Dir.L, some 0⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 6⟩
  | 5, 3 => some ⟨2, Dir.L, some 3⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨2, Dir.L, some 5⟩
  | 6, 2 => some ⟨3, Dir.L, some 0⟩
  | 6, 3 => some ⟨3, Dir.R, some 4⟩
  | _, _ => none

theorem valid_7_4_3 : ValidTM 7 4 tm_7_4_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 7 => rfl

def landmark_7_4_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 2] }
theorem reaches_landmark_7_4_3 : steps tm_7_4_3 509 initConfig = some landmark_7_4_3 := by
  have h0 : steps tm_7_4_3 35 initConfig = some { st := some 0, left := [1, 1], cur := 2, right := [2, 0, 2] } := rfl
  have hstep1 : steps tm_7_4_3 35 { st := some 0, left := [1, 1], cur := 2, right := [2, 0, 2] } = some { st := some 3, left := [], cur := 2, right := [1, 1, 2, 3, 0, 2, 0, 2] } := rfl
  have h1 : steps tm_7_4_3 70 initConfig = some { st := some 3, left := [], cur := 2, right := [1, 1, 2, 3, 0, 2, 0, 2] } := steps_add tm_7_4_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_4_3 35 { st := some 3, left := [], cur := 2, right := [1, 1, 2, 3, 0, 2, 0, 2] } = some { st := some 1, left := [2, 1, 1, 1, 1, 1], cur := 2, right := [3, 0, 2, 0, 2] } := rfl
  have h2 : steps tm_7_4_3 105 initConfig = some { st := some 1, left := [2, 1, 1, 1, 1, 1], cur := 2, right := [3, 0, 2, 0, 2] } := steps_add tm_7_4_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_4_3 35 { st := some 1, left := [2, 1, 1, 1, 1, 1], cur := 2, right := [3, 0, 2, 0, 2] } = some { st := some 3, left := [], cur := 1, right := [2, 2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h3 : steps tm_7_4_3 140 initConfig = some { st := some 3, left := [], cur := 1, right := [2, 2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_4_3 35 { st := some 3, left := [], cur := 1, right := [2, 2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 1, left := [2, 1, 1, 1], cur := 1, right := [2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h4 : steps tm_7_4_3 175 initConfig = some { st := some 1, left := [2, 1, 1, 1], cur := 1, right := [2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_4_3 35 { st := some 1, left := [2, 1, 1, 1], cur := 1, right := [2, 1, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 0, left := [2, 2, 1, 1], cur := 1, right := [1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h5 : steps tm_7_4_3 210 initConfig = some { st := some 0, left := [2, 2, 1, 1], cur := 1, right := [1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_4_3 35 { st := some 0, left := [2, 2, 1, 1], cur := 1, right := [1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 4, left := [1], cur := 2, right := [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h6 : steps tm_7_4_3 245 initConfig = some { st := some 4, left := [1], cur := 2, right := [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_4_3 35 { st := some 4, left := [1], cur := 2, right := [1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h7 : steps tm_7_4_3 280 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_4_3 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h8 : steps tm_7_4_3 315 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_7_4_3 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 2, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h9 : steps tm_7_4_3 350 initConfig = some { st := some 2, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_7_4_3 35 { st := some 2, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 3, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h10 : steps tm_7_4_3 385 initConfig = some { st := some 3, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_7_4_3 35 { st := some 3, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 5, left := [2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h11 : steps tm_7_4_3 420 initConfig = some { st := some 5, left := [2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_7_4_3 35 { st := some 5, left := [2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h12 : steps tm_7_4_3 455 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_7_4_3 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } := rfl
  have h13 : steps tm_7_4_3 490 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } := steps_add tm_7_4_3 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_7_4_3 19 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 1, 0, 0, 2, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 2] } := rfl
  have h14 : steps tm_7_4_3 509 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 2] } := steps_add tm_7_4_3 490 19 initConfig _ _ h13 hstep14
  exact h14

/-! ### 8x4 — fw2_3 @ step 5657 -/
def tm_8_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 7⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 1⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨3, Dir.L, some 7⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 7⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 0⟩
  | 3, 3 => some ⟨0, Dir.R, some 0⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.R, some 3⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨3, Dir.R, some 2⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨3, Dir.R, some 1⟩
  | 7, 0 => some ⟨1, Dir.R, some 0⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.R, some 6⟩
  | 7, 3 => some ⟨0, Dir.R, some 4⟩
  | _, _ => none

theorem valid_8_4 : ValidTM 8 4 tm_8_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 8 => rfl

def landmark_8_4 : Config := { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] }
set_option maxHeartbeats 800000 in
theorem reaches_landmark_8_4 : steps tm_8_4 5657 initConfig = some landmark_8_4 := by
  have h0 : steps tm_8_4 35 initConfig = some { st := some 7, left := [1], cur := 2, right := [3, 3, 1] } := rfl
  have hstep1 : steps tm_8_4 35 { st := some 7, left := [1], cur := 2, right := [3, 3, 1] } = some { st := some 0, left := [2, 1], cur := 2, right := [2, 2, 0, 1] } := rfl
  have h1 : steps tm_8_4 70 initConfig = some { st := some 0, left := [2, 1], cur := 2, right := [2, 2, 0, 1] } := steps_add tm_8_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_4 35 { st := some 0, left := [2, 1], cur := 2, right := [2, 2, 0, 1] } = some { st := some 3, left := [1, 2, 2, 2, 1], cur := 2, right := [1] } := rfl
  have h2 : steps tm_8_4 105 initConfig = some { st := some 3, left := [1, 2, 2, 2, 1], cur := 2, right := [1] } := steps_add tm_8_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_8_4 35 { st := some 3, left := [1, 2, 2, 2, 1], cur := 2, right := [1] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2, 1, 2, 1, 1, 3, 1] } := rfl
  have h3 : steps tm_8_4 140 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2, 1, 2, 1, 1, 3, 1] } := steps_add tm_8_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_8_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2, 1, 2, 1, 1, 3, 1] } = some { st := some 0, left := [2, 2, 1, 1, 1], cur := 1, right := [1, 2, 1, 3, 1] } := rfl
  have h4 : steps tm_8_4 175 initConfig = some { st := some 0, left := [2, 2, 1, 1, 1], cur := 1, right := [1, 2, 1, 3, 1] } := steps_add tm_8_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_8_4 35 { st := some 0, left := [2, 2, 1, 1, 1], cur := 1, right := [1, 2, 1, 3, 1] } = some { st := some 6, left := [1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 2, 1, 3, 1] } := rfl
  have h5 : steps tm_8_4 210 initConfig = some { st := some 6, left := [1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 2, 1, 3, 1] } := steps_add tm_8_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_8_4 35 { st := some 6, left := [1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 2, 1, 3, 1] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1] } := rfl
  have h6 : steps tm_8_4 245 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1] } := steps_add tm_8_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_8_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1] } = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1] } := rfl
  have h7 : steps tm_8_4 280 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1] } := steps_add tm_8_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_8_4 35 { st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1] } := rfl
  have h8 : steps tm_8_4 315 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1] } := steps_add tm_8_4 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_8_4 35 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 2, 1, 3, 1] } := rfl
  have h9 : steps tm_8_4 350 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 2, 1, 3, 1] } := steps_add tm_8_4 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 2, 1, 3, 1] } = some { st := some 4, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 3, 1] } := rfl
  have h10 : steps tm_8_4 385 initConfig = some { st := some 4, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 3, 1] } := steps_add tm_8_4 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_8_4 35 { st := some 4, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 3, 1] } = some { st := some 4, left := [2, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h11 : steps tm_8_4 420 initConfig = some { st := some 4, left := [2, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_8_4 35 { st := some 4, left := [2, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h12 : steps tm_8_4 455 initConfig = some { st := some 2, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_8_4 35 { st := some 2, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h13 : steps tm_8_4 490 initConfig = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h14 : steps tm_8_4 525 initConfig = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h15 : steps tm_8_4 560 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h16 : steps tm_8_4 595 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h17 : steps tm_8_4 630 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_8_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h18 : steps tm_8_4 665 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h19 : steps tm_8_4 700 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h20 : steps tm_8_4 735 initConfig = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h21 : steps tm_8_4 770 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h22 : steps tm_8_4 805 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h23 : steps tm_8_4 840 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h24 : steps tm_8_4 875 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } := rfl
  have h25 : steps tm_8_4 910 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } := rfl
  have h26 : steps tm_8_4 945 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } := rfl
  have h27 : steps tm_8_4 980 initConfig = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 2, 3, 1] } := rfl
  have h28 : steps tm_8_4 1015 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 2, 3, 1] } := steps_add tm_8_4 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } := rfl
  have h29 : steps tm_8_4 1050 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } := steps_add tm_8_4 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } := rfl
  have h30 : steps tm_8_4 1085 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } := steps_add tm_8_4 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_8_4 35 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 2, 3, 1] } := rfl
  have h31 : steps tm_8_4 1120 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 2, 3, 1] } := steps_add tm_8_4 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 2, 1, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } := rfl
  have h32 : steps tm_8_4 1155 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } := steps_add tm_8_4 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } := rfl
  have h33 : steps tm_8_4 1190 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } := steps_add tm_8_4 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_8_4 35 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 3, 1] } := rfl
  have h34 : steps tm_8_4 1225 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 3, 1] } := steps_add tm_8_4 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 2, 3, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := rfl
  have h35 : steps tm_8_4 1260 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := steps_add tm_8_4 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := rfl
  have h36 : steps tm_8_4 1295 initConfig = some { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := steps_add tm_8_4 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := rfl
  have h37 : steps tm_8_4 1330 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } := steps_add tm_8_4 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 2, 3, 1] } = some { st := some 3, left := [3, 0, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1] } := rfl
  have h38 : steps tm_8_4 1365 initConfig = some { st := some 3, left := [3, 0, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1] } := steps_add tm_8_4 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_8_4 35 { st := some 3, left := [3, 0, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h39 : steps tm_8_4 1400 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h40 : steps tm_8_4 1435 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h41 : steps tm_8_4 1470 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h42 : steps tm_8_4 1505 initConfig = some { st := some 6, left := [1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_8_4 35 { st := some 6, left := [1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h43 : steps tm_8_4 1540 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_8_4 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h44 : steps tm_8_4 1575 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h45 : steps tm_8_4 1610 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h46 : steps tm_8_4 1645 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h47 : steps tm_8_4 1680 initConfig = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_8_4 35 { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h48 : steps tm_8_4 1715 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h49 : steps tm_8_4 1750 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_8_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h50 : steps tm_8_4 1785 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h51 : steps tm_8_4 1820 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h52 : steps tm_8_4 1855 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h53 : steps tm_8_4 1890 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h54 : steps tm_8_4 1925 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h55 : steps tm_8_4 1960 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_8_4 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h56 : steps tm_8_4 1995 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h57 : steps tm_8_4 2030 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h58 : steps tm_8_4 2065 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h59 : steps tm_8_4 2100 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h60 : steps tm_8_4 2135 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h61 : steps tm_8_4 2170 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h62 : steps tm_8_4 2205 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h63 : steps tm_8_4 2240 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h64 : steps tm_8_4 2275 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h65 : steps tm_8_4 2310 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h66 : steps tm_8_4 2345 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h67 : steps tm_8_4 2380 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h68 : steps tm_8_4 2415 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h69 : steps tm_8_4 2450 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h70 : steps tm_8_4 2485 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_8_4 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h71 : steps tm_8_4 2520 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h72 : steps tm_8_4 2555 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2520 35 initConfig _ _ h71 hstep72
  have hstep73 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h73 : steps tm_8_4 2590 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2555 35 initConfig _ _ h72 hstep73
  have hstep74 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h74 : steps tm_8_4 2625 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2590 35 initConfig _ _ h73 hstep74
  have hstep75 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h75 : steps tm_8_4 2660 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2625 35 initConfig _ _ h74 hstep75
  have hstep76 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h76 : steps tm_8_4 2695 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2660 35 initConfig _ _ h75 hstep76
  have hstep77 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h77 : steps tm_8_4 2730 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2695 35 initConfig _ _ h76 hstep77
  have hstep78 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h78 : steps tm_8_4 2765 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2730 35 initConfig _ _ h77 hstep78
  have hstep79 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h79 : steps tm_8_4 2800 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2765 35 initConfig _ _ h78 hstep79
  have hstep80 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h80 : steps tm_8_4 2835 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2800 35 initConfig _ _ h79 hstep80
  have hstep81 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h81 : steps tm_8_4 2870 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2835 35 initConfig _ _ h80 hstep81
  have hstep82 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h82 : steps tm_8_4 2905 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2870 35 initConfig _ _ h81 hstep82
  have hstep83 : steps tm_8_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h83 : steps tm_8_4 2940 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2905 35 initConfig _ _ h82 hstep83
  have hstep84 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h84 : steps tm_8_4 2975 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2940 35 initConfig _ _ h83 hstep84
  have hstep85 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h85 : steps tm_8_4 3010 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 2975 35 initConfig _ _ h84 hstep85
  have hstep86 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h86 : steps tm_8_4 3045 initConfig = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3010 35 initConfig _ _ h85 hstep86
  have hstep87 : steps tm_8_4 35 { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h87 : steps tm_8_4 3080 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3045 35 initConfig _ _ h86 hstep87
  have hstep88 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h88 : steps tm_8_4 3115 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3080 35 initConfig _ _ h87 hstep88
  have hstep89 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h89 : steps tm_8_4 3150 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3115 35 initConfig _ _ h88 hstep89
  have hstep90 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h90 : steps tm_8_4 3185 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3150 35 initConfig _ _ h89 hstep90
  have hstep91 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h91 : steps tm_8_4 3220 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3185 35 initConfig _ _ h90 hstep91
  have hstep92 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h92 : steps tm_8_4 3255 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3220 35 initConfig _ _ h91 hstep92
  have hstep93 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h93 : steps tm_8_4 3290 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3255 35 initConfig _ _ h92 hstep93
  have hstep94 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h94 : steps tm_8_4 3325 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3290 35 initConfig _ _ h93 hstep94
  have hstep95 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h95 : steps tm_8_4 3360 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3325 35 initConfig _ _ h94 hstep95
  have hstep96 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h96 : steps tm_8_4 3395 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3360 35 initConfig _ _ h95 hstep96
  have hstep97 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h97 : steps tm_8_4 3430 initConfig = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3395 35 initConfig _ _ h96 hstep97
  have hstep98 : steps tm_8_4 35 { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h98 : steps tm_8_4 3465 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3430 35 initConfig _ _ h97 hstep98
  have hstep99 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h99 : steps tm_8_4 3500 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3465 35 initConfig _ _ h98 hstep99
  have hstep100 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h100 : steps tm_8_4 3535 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3500 35 initConfig _ _ h99 hstep100
  have hstep101 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h101 : steps tm_8_4 3570 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3535 35 initConfig _ _ h100 hstep101
  have hstep102 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h102 : steps tm_8_4 3605 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3570 35 initConfig _ _ h101 hstep102
  have hstep103 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h103 : steps tm_8_4 3640 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3605 35 initConfig _ _ h102 hstep103
  have hstep104 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h104 : steps tm_8_4 3675 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3640 35 initConfig _ _ h103 hstep104
  have hstep105 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h105 : steps tm_8_4 3710 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3675 35 initConfig _ _ h104 hstep105
  have hstep106 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h106 : steps tm_8_4 3745 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3710 35 initConfig _ _ h105 hstep106
  have hstep107 : steps tm_8_4 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h107 : steps tm_8_4 3780 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3745 35 initConfig _ _ h106 hstep107
  have hstep108 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h108 : steps tm_8_4 3815 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3780 35 initConfig _ _ h107 hstep108
  have hstep109 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h109 : steps tm_8_4 3850 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3815 35 initConfig _ _ h108 hstep109
  have hstep110 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h110 : steps tm_8_4 3885 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3850 35 initConfig _ _ h109 hstep110
  have hstep111 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h111 : steps tm_8_4 3920 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3885 35 initConfig _ _ h110 hstep111
  have hstep112 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h112 : steps tm_8_4 3955 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3920 35 initConfig _ _ h111 hstep112
  have hstep113 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h113 : steps tm_8_4 3990 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3955 35 initConfig _ _ h112 hstep113
  have hstep114 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h114 : steps tm_8_4 4025 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 3990 35 initConfig _ _ h113 hstep114
  have hstep115 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h115 : steps tm_8_4 4060 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4025 35 initConfig _ _ h114 hstep115
  have hstep116 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h116 : steps tm_8_4 4095 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4060 35 initConfig _ _ h115 hstep116
  have hstep117 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h117 : steps tm_8_4 4130 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4095 35 initConfig _ _ h116 hstep117
  have hstep118 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h118 : steps tm_8_4 4165 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4130 35 initConfig _ _ h117 hstep118
  have hstep119 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h119 : steps tm_8_4 4200 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4165 35 initConfig _ _ h118 hstep119
  have hstep120 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h120 : steps tm_8_4 4235 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4200 35 initConfig _ _ h119 hstep120
  have hstep121 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h121 : steps tm_8_4 4270 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4235 35 initConfig _ _ h120 hstep121
  have hstep122 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h122 : steps tm_8_4 4305 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4270 35 initConfig _ _ h121 hstep122
  have hstep123 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h123 : steps tm_8_4 4340 initConfig = some { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4305 35 initConfig _ _ h122 hstep123
  have hstep124 : steps tm_8_4 35 { st := some 6, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h124 : steps tm_8_4 4375 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4340 35 initConfig _ _ h123 hstep124
  have hstep125 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h125 : steps tm_8_4 4410 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4375 35 initConfig _ _ h124 hstep125
  have hstep126 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h126 : steps tm_8_4 4445 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4410 35 initConfig _ _ h125 hstep126
  have hstep127 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h127 : steps tm_8_4 4480 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4445 35 initConfig _ _ h126 hstep127
  have hstep128 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h128 : steps tm_8_4 4515 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4480 35 initConfig _ _ h127 hstep128
  have hstep129 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h129 : steps tm_8_4 4550 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4515 35 initConfig _ _ h128 hstep129
  have hstep130 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h130 : steps tm_8_4 4585 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4550 35 initConfig _ _ h129 hstep130
  have hstep131 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h131 : steps tm_8_4 4620 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4585 35 initConfig _ _ h130 hstep131
  have hstep132 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h132 : steps tm_8_4 4655 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4620 35 initConfig _ _ h131 hstep132
  have hstep133 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h133 : steps tm_8_4 4690 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4655 35 initConfig _ _ h132 hstep133
  have hstep134 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h134 : steps tm_8_4 4725 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4690 35 initConfig _ _ h133 hstep134
  have hstep135 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h135 : steps tm_8_4 4760 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4725 35 initConfig _ _ h134 hstep135
  have hstep136 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h136 : steps tm_8_4 4795 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4760 35 initConfig _ _ h135 hstep136
  have hstep137 : steps tm_8_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h137 : steps tm_8_4 4830 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4795 35 initConfig _ _ h136 hstep137
  have hstep138 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h138 : steps tm_8_4 4865 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4830 35 initConfig _ _ h137 hstep138
  have hstep139 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h139 : steps tm_8_4 4900 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4865 35 initConfig _ _ h138 hstep139
  have hstep140 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h140 : steps tm_8_4 4935 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4900 35 initConfig _ _ h139 hstep140
  have hstep141 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h141 : steps tm_8_4 4970 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4935 35 initConfig _ _ h140 hstep141
  have hstep142 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h142 : steps tm_8_4 5005 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 4970 35 initConfig _ _ h141 hstep142
  have hstep143 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h143 : steps tm_8_4 5040 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5005 35 initConfig _ _ h142 hstep143
  have hstep144 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := rfl
  have h144 : steps tm_8_4 5075 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5040 35 initConfig _ _ h143 hstep144
  have hstep145 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h145 : steps tm_8_4 5110 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5075 35 initConfig _ _ h144 hstep145
  have hstep146 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h146 : steps tm_8_4 5145 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5110 35 initConfig _ _ h145 hstep146
  have hstep147 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h147 : steps tm_8_4 5180 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5145 35 initConfig _ _ h146 hstep147
  have hstep148 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h148 : steps tm_8_4 5215 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5180 35 initConfig _ _ h147 hstep148
  have hstep149 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h149 : steps tm_8_4 5250 initConfig = some { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5215 35 initConfig _ _ h148 hstep149
  have hstep150 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h150 : steps tm_8_4 5285 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5250 35 initConfig _ _ h149 hstep150
  have hstep151 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := rfl
  have h151 : steps tm_8_4 5320 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5285 35 initConfig _ _ h150 hstep151
  have hstep152 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h152 : steps tm_8_4 5355 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5320 35 initConfig _ _ h151 hstep152
  have hstep153 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h153 : steps tm_8_4 5390 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5355 35 initConfig _ _ h152 hstep153
  have hstep154 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h154 : steps tm_8_4 5425 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5390 35 initConfig _ _ h153 hstep154
  have hstep155 : steps tm_8_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h155 : steps tm_8_4 5460 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5425 35 initConfig _ _ h154 hstep155
  have hstep156 : steps tm_8_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h156 : steps tm_8_4 5495 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5460 35 initConfig _ _ h155 hstep156
  have hstep157 : steps tm_8_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h157 : steps tm_8_4 5530 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5495 35 initConfig _ _ h156 hstep157
  have hstep158 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := rfl
  have h158 : steps tm_8_4 5565 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } := steps_add tm_8_4 5530 35 initConfig _ _ h157 hstep158
  have hstep159 : steps tm_8_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2, 1] } = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h159 : steps tm_8_4 5600 initConfig = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_8_4 5565 35 initConfig _ _ h158 hstep159
  have hstep160 : steps tm_8_4 35 { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h160 : steps tm_8_4 5635 initConfig = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_8_4 5600 35 initConfig _ _ h159 hstep160
  have hstep161 : steps tm_8_4 22 { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := rfl
  have h161 : steps tm_8_4 5657 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2] } := steps_add tm_8_4 5635 22 initConfig _ _ h160 hstep161
  exact h161

/-! ### 8x4 — fwm2_3 @ step 90 -/
def tm_8_4_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨0, Dir.R, some 5⟩
  | 1, 0 => some ⟨2, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨0, Dir.L, some 4⟩
  | 2, 0 => some ⟨2, Dir.L, some 0⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 2⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨0, Dir.L, some 6⟩
  | 3, 3 => some ⟨3, Dir.R, some 1⟩
  | 4, 0 => some ⟨0, Dir.L, some 5⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 0 => some ⟨1, Dir.R, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, none⟩
  | 5, 2 => some ⟨3, Dir.L, some 0⟩
  | 5, 3 => some ⟨3, Dir.R, some 3⟩
  | 6, 0 => some ⟨0, Dir.R, some 2⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 3⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨2, Dir.L, some 1⟩
  | _, _ => none

theorem valid_8_4_1 : ValidTM 8 4 tm_8_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 8 => rfl

def landmark_8_4_1 : Config := { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] }
theorem reaches_landmark_8_4_1 : steps tm_8_4_1 90 initConfig = some landmark_8_4_1 := by
  have h0 : steps tm_8_4_1 35 initConfig = some { st := some 4, left := [2, 2], cur := 0, right := [1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_8_4_1 35 { st := some 4, left := [2, 2], cur := 0, right := [1, 1, 1, 2] } = some { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } := rfl
  have h1 : steps tm_8_4_1 70 initConfig = some { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } := steps_add tm_8_4_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_4_1 20 { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } = some { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] } := rfl
  have h2 : steps tm_8_4_1 90 initConfig = some { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] } := steps_add tm_8_4_1 70 20 initConfig _ _ h1 hstep2
  exact h2

/-! ### 9x4 — fw2_3 @ step 2510 -/
def tm_9_4 : TM
  | 0, 0 => some ⟨0, Dir.L, some 7⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 7⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨3, Dir.L, some 0⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.R, some 0⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 1⟩
  | 3, 3 => some ⟨3, Dir.R, some 8⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.R, some 6⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 5, 3 => some ⟨2, Dir.R, some 6⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 4⟩
  | 7, 0 => some ⟨1, Dir.R, some 0⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 7, 3 => some ⟨0, Dir.R, some 8⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨2, Dir.L, some 7⟩
  | 8, 2 => some ⟨0, Dir.R, some 3⟩
  | 8, 3 => some ⟨0, Dir.L, some 6⟩
  | _, _ => none

theorem valid_9_4 : ValidTM 9 4 tm_9_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 9 => rfl

def landmark_9_4 : Config := { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] }
theorem reaches_landmark_9_4 : steps tm_9_4 2510 initConfig = some landmark_9_4 := by
  have h0 : steps tm_9_4 35 initConfig = some { st := some 2, left := [1, 1, 1], cur := 0, right := [3] } := rfl
  have hstep1 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1], cur := 0, right := [3] } = some { st := some 4, left := [], cur := 2, right := [1, 2, 1, 0, 3, 3, 1] } := rfl
  have h1 : steps tm_9_4 70 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 2, 1, 0, 3, 3, 1] } := steps_add tm_9_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_9_4 35 { st := some 4, left := [], cur := 2, right := [1, 2, 1, 0, 3, 3, 1] } = some { st := some 0, left := [2, 1, 1], cur := 1, right := [1, 1, 0, 3, 3, 1] } := rfl
  have h2 : steps tm_9_4 105 initConfig = some { st := some 0, left := [2, 1, 1], cur := 1, right := [1, 1, 0, 3, 3, 1] } := steps_add tm_9_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1], cur := 1, right := [1, 1, 0, 3, 3, 1] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 3, 1] } := rfl
  have h3 : steps tm_9_4 140 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 3, 1] } := steps_add tm_9_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 3, 1] } = some { st := some 7, left := [1, 1, 1, 1, 1], cur := 1, right := [2, 0, 2, 2, 0, 2] } := rfl
  have h4 : steps tm_9_4 175 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1], cur := 1, right := [2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_9_4 35 { st := some 7, left := [1, 1, 1, 1, 1], cur := 1, right := [2, 0, 2, 2, 0, 2] } = some { st := some 3, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := rfl
  have h5 : steps tm_9_4 210 initConfig = some { st := some 3, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_9_4 35 { st := some 3, left := [1, 1, 1, 1], cur := 2, right := [1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } = some { st := some 2, left := [], cur := 1, right := [1, 1, 2, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := rfl
  have h6 : steps tm_9_4 245 initConfig = some { st := some 2, left := [], cur := 1, right := [1, 1, 2, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_9_4 35 { st := some 2, left := [], cur := 1, right := [1, 1, 2, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := rfl
  have h7 : steps tm_9_4 280 initConfig = some { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_9_4 35 { st := some 0, left := [2, 1], cur := 1, right := [1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } = some { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := rfl
  have h8 : steps tm_9_4 315 initConfig = some { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_9_4 35 { st := some 4, left := [1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2] } = some { st := some 3, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 2, 0, 2, 0, 2, 2, 0, 2] } := rfl
  have h9 : steps tm_9_4 350 initConfig = some { st := some 3, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 2, 0, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_9_4 35 { st := some 3, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [0, 2, 0, 2, 0, 2, 2, 0, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } := rfl
  have h10 : steps tm_9_4 385 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } := rfl
  have h11 : steps tm_9_4 420 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2, 0, 2, 2, 0, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 2, 0, 2] } := rfl
  have h12 : steps tm_9_4 455 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 0, 2, 2, 0, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 3, 1, 2, 0, 2, 2, 0, 2] } := rfl
  have h13 : steps tm_9_4 490 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 3, 1, 2, 0, 2, 2, 0, 2] } := steps_add tm_9_4 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 3, 1, 2, 0, 2, 2, 0, 2] } = some { st := some 7, left := [2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 2] } := rfl
  have h14 : steps tm_9_4 525 initConfig = some { st := some 7, left := [2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 2] } := steps_add tm_9_4 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_9_4 35 { st := some 7, left := [2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 0, 3, 3, 1, 2] } := rfl
  have h15 : steps tm_9_4 560 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h16 : steps tm_9_4 595 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h17 : steps tm_9_4 630 initConfig = some { st := some 6, left := [1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_9_4 35 { st := some 6, left := [1, 1], cur := 1, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h18 : steps tm_9_4 665 initConfig = some { st := some 6, left := [1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_9_4 35 { st := some 6, left := [1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h19 : steps tm_9_4 700 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_9_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h20 : steps tm_9_4 735 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h21 : steps tm_9_4 770 initConfig = some { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_9_4 35 { st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h22 : steps tm_9_4 805 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h23 : steps tm_9_4 840 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h24 : steps tm_9_4 875 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_9_4 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h25 : steps tm_9_4 910 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h26 : steps tm_9_4 945 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_9_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h27 : steps tm_9_4 980 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h28 : steps tm_9_4 1015 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_9_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h29 : steps tm_9_4 1050 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h30 : steps tm_9_4 1085 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h31 : steps tm_9_4 1120 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h32 : steps tm_9_4 1155 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h33 : steps tm_9_4 1190 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h34 : steps tm_9_4 1225 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h35 : steps tm_9_4 1260 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h36 : steps tm_9_4 1295 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h37 : steps tm_9_4 1330 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h38 : steps tm_9_4 1365 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h39 : steps tm_9_4 1400 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h40 : steps tm_9_4 1435 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h41 : steps tm_9_4 1470 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h42 : steps tm_9_4 1505 initConfig = some { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h43 : steps tm_9_4 1540 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h44 : steps tm_9_4 1575 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h45 : steps tm_9_4 1610 initConfig = some { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h46 : steps tm_9_4 1645 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h47 : steps tm_9_4 1680 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h48 : steps tm_9_4 1715 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h49 : steps tm_9_4 1750 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_9_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 0, 3, 3, 1, 2] } := rfl
  have h50 : steps tm_9_4 1785 initConfig = some { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_9_4 35 { st := some 1, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := rfl
  have h51 : steps tm_9_4 1820 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := rfl
  have h52 : steps tm_9_4 1855 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := rfl
  have h53 : steps tm_9_4 1890 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_9_4 35 { st := some 2, left := [1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 0, 3, 3, 1, 2] } := rfl
  have h54 : steps tm_9_4 1925 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [2, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := rfl
  have h55 : steps tm_9_4 1960 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := rfl
  have h56 : steps tm_9_4 1995 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := rfl
  have h57 : steps tm_9_4 2030 initConfig = some { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := steps_add tm_9_4 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_9_4 35 { st := some 4, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := rfl
  have h58 : steps tm_9_4 2065 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } := steps_add tm_9_4 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 2, 0, 3, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h59 : steps tm_9_4 2100 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h60 : steps tm_9_4 2135 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h61 : steps tm_9_4 2170 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := rfl
  have h62 : steps tm_9_4 2205 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } := steps_add tm_9_4 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 3, 1, 2] } := rfl
  have h63 : steps tm_9_4 2240 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 3, 1, 2] } := steps_add tm_9_4 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_9_4 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 3, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := rfl
  have h64 : steps tm_9_4 2275 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := steps_add tm_9_4 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_9_4 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := rfl
  have h65 : steps tm_9_4 2310 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := steps_add tm_9_4 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_9_4 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } = some { st := some 4, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := rfl
  have h66 : steps tm_9_4 2345 initConfig = some { st := some 4, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := steps_add tm_9_4 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_9_4 35 { st := some 4, left := [1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := rfl
  have h67 : steps tm_9_4 2380 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } := steps_add tm_9_4 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_9_4 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2] } = some { st := some 7, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [2] } := rfl
  have h68 : steps tm_9_4 2415 initConfig = some { st := some 7, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [2] } := steps_add tm_9_4 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_9_4 35 { st := some 7, left := [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 3, right := [2] } = some { st := some 2, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2] } := rfl
  have h69 : steps tm_9_4 2450 initConfig = some { st := some 2, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2] } := steps_add tm_9_4 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_9_4 35 { st := some 2, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 2] } = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] } := rfl
  have h70 : steps tm_9_4 2485 initConfig = some { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] } := steps_add tm_9_4 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_9_4 25 { st := some 3, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] } = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] } := rfl
  have h71 : steps tm_9_4 2510 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2] } := steps_add tm_9_4 2485 25 initConfig _ _ h70 hstep71
  exact h71

/-! ### 9x4 — fw3_3 @ step 309 -/
def tm_9_4_1 : TM
  | 0, 0 => some ⟨2, Dir.L, some 8⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 5⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨1, Dir.L, some 5⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨0, Dir.L, some 6⟩
  | 3, 3 => some ⟨0, Dir.L, some 7⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨0, Dir.L, some 1⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, some 7⟩
  | 5, 3 => some ⟨0, Dir.L, some 6⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 2⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 7, 3 => some ⟨3, Dir.R, some 0⟩
  | 8, 0 => some ⟨1, Dir.R, some 3⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 1⟩
  | 8, 3 => some ⟨0, Dir.R, some 0⟩
  | _, _ => none

theorem valid_9_4_1 : ValidTM 9 4 tm_9_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 9 => rfl

def landmark_9_4_1 : Config := { st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] }
theorem reaches_landmark_9_4_1 : steps tm_9_4_1 309 initConfig = some landmark_9_4_1 := by
  have h0 : steps tm_9_4_1 35 initConfig = some { st := some 6, left := [3, 1, 1], cur := 1, right := [3, 2] } := rfl
  have hstep1 : steps tm_9_4_1 35 { st := some 6, left := [3, 1, 1], cur := 1, right := [3, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [0, 3, 2, 1, 3, 2] } := rfl
  have h1 : steps tm_9_4_1 70 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [0, 3, 2, 1, 3, 2] } := steps_add tm_9_4_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_9_4_1 35 { st := some 2, left := [1, 1], cur := 1, right := [0, 3, 2, 1, 3, 2] } = some { st := some 0, left := [2, 2], cur := 0, right := [0, 1, 3, 1, 1, 3, 2] } := rfl
  have h2 : steps tm_9_4_1 105 initConfig = some { st := some 0, left := [2, 2], cur := 0, right := [0, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_9_4_1 35 { st := some 0, left := [2, 2], cur := 0, right := [0, 1, 3, 1, 1, 3, 2] } = some { st := some 2, left := [1], cur := 2, right := [2, 3, 2, 2, 1, 3, 1, 1, 3, 2] } := rfl
  have h3 : steps tm_9_4_1 140 initConfig = some { st := some 2, left := [1], cur := 2, right := [2, 3, 2, 2, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_9_4_1 35 { st := some 2, left := [1], cur := 2, right := [2, 3, 2, 2, 1, 3, 1, 1, 3, 2] } = some { st := some 5, left := [1], cur := 2, right := [1, 2, 2, 0, 1, 3, 1, 1, 3, 1, 1, 3, 2] } := rfl
  have h4 : steps tm_9_4_1 175 initConfig = some { st := some 5, left := [1], cur := 2, right := [1, 2, 2, 0, 1, 3, 1, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_9_4_1 35 { st := some 5, left := [1], cur := 2, right := [1, 2, 2, 0, 1, 3, 1, 1, 3, 1, 1, 3, 2] } = some { st := some 5, left := [1, 1, 1, 3, 1, 1], cur := 2, right := [3, 1, 1, 3, 1, 1, 3, 2] } := rfl
  have h5 : steps tm_9_4_1 210 initConfig = some { st := some 5, left := [1, 1, 1, 3, 1, 1], cur := 2, right := [3, 1, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_9_4_1 35 { st := some 5, left := [1, 1, 1, 3, 1, 1], cur := 2, right := [3, 1, 1, 3, 1, 1, 3, 2] } = some { st := some 2, left := [1, 1], cur := 1, right := [2, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := rfl
  have h6 : steps tm_9_4_1 245 initConfig = some { st := some 2, left := [1, 1], cur := 1, right := [2, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_9_4_1 35 { st := some 2, left := [1, 1], cur := 1, right := [2, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := rfl
  have h7 : steps tm_9_4_1 280 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_9_4_1 29 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } = some { st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := rfl
  have h8 : steps tm_9_4_1 309 initConfig = some { st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 3, 1, 1, 3, 2] } := steps_add tm_9_4_1 280 29 initConfig _ _ h7 hstep8
  exact h8

/-! ### 9x4 — fw3_4 @ step 77 -/
def tm_9_4_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 7⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 0, 3 => some ⟨1, Dir.L, some 5⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 6⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨0, Dir.L, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 8⟩
  | 3, 3 => some ⟨3, Dir.R, some 1⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 4, 3 => some ⟨3, Dir.R, some 3⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 0⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 7, 3 => some ⟨3, Dir.L, some 0⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨2, Dir.L, some 7⟩
  | 8, 2 => some ⟨0, Dir.R, some 3⟩
  | 8, 3 => some ⟨2, Dir.R, some 3⟩
  | _, _ => none

theorem valid_9_4_2 : ValidTM 9 4 tm_9_4_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, trivial⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 9 => rfl

def landmark_9_4_2 : Config := { st := some 5, left := [1], cur := 0, right := [0, 1, 2, 2, 3, 1, 2] }
theorem reaches_landmark_9_4_2 : steps tm_9_4_2 77 initConfig = some landmark_9_4_2 := by
  have h0 : steps tm_9_4_2 35 initConfig = some { st := some 2, left := [1], cur := 1, right := [1, 2, 3] } := rfl
  have hstep1 : steps tm_9_4_2 35 { st := some 2, left := [1], cur := 1, right := [1, 2, 3] } = some { st := some 6, left := [0, 1, 1, 1], cur := 2, right := [2, 3, 1, 2] } := rfl
  have h1 : steps tm_9_4_2 70 initConfig = some { st := some 6, left := [0, 1, 1, 1], cur := 2, right := [2, 3, 1, 2] } := steps_add tm_9_4_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_9_4_2 7 { st := some 6, left := [0, 1, 1, 1], cur := 2, right := [2, 3, 1, 2] } = some { st := some 5, left := [1], cur := 0, right := [0, 1, 2, 2, 3, 1, 2] } := rfl
  have h2 : steps tm_9_4_2 77 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 1, 2, 2, 3, 1, 2] } := steps_add tm_9_4_2 70 7 initConfig _ _ h1 hstep2
  exact h2

/-! ### 9x4 — fwp2_4 @ step 23 -/
def tm_9_4_3 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 8⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, none⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨0, Dir.L, some 4⟩
  | 8, 2 => some ⟨0, Dir.L, some 8⟩
  | 8, 3 => some ⟨3, Dir.L, some 2⟩
  | _, _ => none

theorem valid_9_4_3 : ValidTM 9 4 tm_9_4_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 9 => rfl

def landmark_9_4_3 : Config := { st := some 6, left := [], cur := 3, right := [3, 3, 3] }
theorem reaches_landmark_9_4_3 : steps tm_9_4_3 23 initConfig = some landmark_9_4_3 := by
  have h0 : steps tm_9_4_3 23 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 3, 3] } := rfl
  exact h0

/-! ### 10x4 — fwp21_4 @ step 31 -/
def tm_10_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 8⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨1, Dir.R, none⟩
  | 8, 2 => some ⟨0, Dir.R, some 4⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | _, _ => none

theorem valid_10_4 : ValidTM 10 4 tm_10_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 10 => rfl

def landmark_10_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 3, 3, 0, 0, 0, 1] }
theorem reaches_landmark_10_4 : steps tm_10_4 31 initConfig = some landmark_10_4 := by
  have h0 : steps tm_10_4 31 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 3, 3, 0, 0, 0, 1] } := rfl
  exact h0

/-! ### 11x4 — fwp21_4 @ step 61 -/
def tm_11_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 8⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨1, Dir.R, none⟩
  | 8, 2 => some ⟨0, Dir.L, some 10⟩
  | 8, 3 => some ⟨0, Dir.L, some 10⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨1, Dir.L, some 0⟩
  | 10, 1 => some ⟨0, Dir.L, some 4⟩
  | 10, 2 => some ⟨0, Dir.L, some 4⟩
  | 10, 3 => some ⟨1, Dir.L, some 2⟩
  | _, _ => none

theorem valid_11_4 : ValidTM 11 4 tm_11_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 11 => rfl

def landmark_11_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 3, 0, 0, 1] }
theorem reaches_landmark_11_4 : steps tm_11_4 61 initConfig = some landmark_11_4 := by
  have h0 : steps tm_11_4 35 initConfig = some { st := some 4, left := [], cur := 0, right := [1, 2] } := rfl
  have hstep1 : steps tm_11_4 26 { st := some 4, left := [], cur := 0, right := [1, 2] } = some { st := some 6, left := [], cur := 3, right := [3, 3, 0, 0, 1] } := rfl
  have h1 : steps tm_11_4 61 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 3, 0, 0, 1] } := steps_add tm_11_4 35 26 initConfig _ _ h0 hstep1
  exact h1

/-! ### 11x4 — fwp22_4 @ step 13 -/
def tm_11_4_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨2, Dir.L, some 8⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.R, none⟩
  | 8, 3 => some ⟨1, Dir.L, some 8⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | _, _ => none

theorem valid_11_4_1 : ValidTM 11 4 tm_11_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 11 => rfl

def landmark_11_4_1 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 2] }
theorem reaches_landmark_11_4_1 : steps tm_11_4_1 13 initConfig = some landmark_11_4_1 := by
  have h0 : steps tm_11_4_1 13 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 2] } := rfl
  exact h0

/-! ### 11x4 — fwp2_4 @ step 57 -/
def tm_11_4_2 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 8⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, none⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 4⟩
  | 8, 1 => some ⟨0, Dir.L, some 1⟩
  | 8, 2 => some ⟨0, Dir.L, some 8⟩
  | 8, 3 => some ⟨0, Dir.L, some 9⟩
  | 9, 0 => some ⟨1, Dir.R, some 4⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨3, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 5⟩
  | 10, 0 => some ⟨1, Dir.R, some 9⟩
  | 10, 1 => some ⟨2, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 9⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | _, _ => none

theorem valid_11_4_2 : ValidTM 11 4 tm_11_4_2 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 11 => rfl

def landmark_11_4_2 : Config := { st := some 2, left := [], cur := 3, right := [3, 3] }
theorem reaches_landmark_11_4_2 : steps tm_11_4_2 57 initConfig = some landmark_11_4_2 := by
  have h0 : steps tm_11_4_2 35 initConfig = some { st := some 9, left := [3, 1], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_11_4_2 22 { st := some 9, left := [3, 1], cur := 0, right := [] } = some { st := some 2, left := [], cur := 3, right := [3, 3] } := rfl
  have h1 : steps tm_11_4_2 57 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 3] } := steps_add tm_11_4_2 35 22 initConfig _ _ h0 hstep1
  exact h1

/-! ### 14x4 — fwp24_4 @ step 38 -/
def tm_14_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨3, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 6⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨3, Dir.R, some 1⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | _, _ => none

theorem valid_14_4 : ValidTM 14 4 tm_14_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 14 => rfl

def landmark_14_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 3, 3, 3] }
theorem reaches_landmark_14_4 : steps tm_14_4 38 initConfig = some landmark_14_4 := by
  have h0 : steps tm_14_4 35 initConfig = some { st := some 9, left := [], cur := 1, right := [0, 0, 0, 2, 2, 3, 3, 3] } := rfl
  have hstep1 : steps tm_14_4 3 { st := some 9, left := [], cur := 1, right := [0, 0, 0, 2, 2, 3, 3, 3] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 3, 3, 3] } := rfl
  have h1 : steps tm_14_4 38 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 3, 3, 3] } := steps_add tm_14_4 35 3 initConfig _ _ h0 hstep1
  exact h1

/-! ### 15x4 — fwp25_4 @ step 21 -/
def tm_15_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨2, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 1⟩
  | 12, 2 => some ⟨3, Dir.L, some 14⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.L, some 13⟩
  | 14, 1 => some ⟨3, Dir.L, some 14⟩
  | 14, 2 => some ⟨3, Dir.L, some 14⟩
  | 14, 3 => some ⟨3, Dir.L, some 14⟩
  | _, _ => none

theorem valid_15_4 : ValidTM 15 4 tm_15_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 15 => rfl

def landmark_15_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 3, 2, 2] }
theorem reaches_landmark_15_4 : steps tm_15_4 21 initConfig = some landmark_15_4 := by
  have h0 : steps tm_15_4 21 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 3, 2, 2] } := rfl
  exact h0

/-! ### 16x4 — fwp24_4 @ step 65 -/
def tm_16_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 14⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨1, Dir.L, some 4⟩
  | 14, 1 => some ⟨2, Dir.L, some 15⟩
  | 14, 2 => some ⟨3, Dir.L, some 15⟩
  | 14, 3 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨1, Dir.L, some 6⟩
  | 15, 1 => some ⟨1, Dir.L, some 14⟩
  | 15, 2 => some ⟨3, Dir.L, some 13⟩
  | 15, 3 => some ⟨2, Dir.R, some 14⟩
  | _, _ => none

theorem valid_16_4 : ValidTM 16 4 tm_16_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 16 => rfl

def landmark_16_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3] }
theorem reaches_landmark_16_4 : steps tm_16_4 65 initConfig = some landmark_16_4 := by
  have h0 : steps tm_16_4 35 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_16_4 30 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3] } := rfl
  have h1 : steps tm_16_4 65 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3] } := steps_add tm_16_4 35 30 initConfig _ _ h0 hstep1
  exact h1

/-! ### 16x4 — fwp25_4 @ step 29 -/
def tm_16_4_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 15⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 1⟩
  | 12, 2 => some ⟨3, Dir.L, some 14⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.L, some 13⟩
  | 14, 1 => some ⟨3, Dir.L, some 14⟩
  | 14, 2 => some ⟨3, Dir.L, some 14⟩
  | 14, 3 => some ⟨3, Dir.L, some 14⟩
  | 15, 0 => some ⟨1, Dir.R, some 1⟩
  | 15, 1 => some ⟨1, Dir.R, some 4⟩
  | 15, 2 => some ⟨0, Dir.L, some 12⟩
  | 15, 3 => some ⟨2, Dir.L, some 14⟩
  | _, _ => none

theorem valid_16_4_1 : ValidTM 16 4 tm_16_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 16 => rfl

def landmark_16_4_1 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2] }
theorem reaches_landmark_16_4_1 : steps tm_16_4_1 29 initConfig = some landmark_16_4_1 := by
  have h0 : steps tm_16_4_1 29 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2] } := rfl
  exact h0

/-! ### 19x4 — fwp24_4 @ step 164 -/
def tm_19_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 14⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨1, Dir.L, some 4⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨0, Dir.R, some 17⟩
  | 14, 3 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨1, Dir.L, some 6⟩
  | 15, 1 => some ⟨0, Dir.L, some 16⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨1, Dir.R, some 18⟩
  | 16, 0 => some ⟨1, Dir.L, some 15⟩
  | 16, 1 => some ⟨0, Dir.L, some 17⟩
  | 16, 2 => some ⟨2, Dir.R, some 18⟩
  | 16, 3 => some ⟨2, Dir.R, some 16⟩
  | 17, 0 => some ⟨0, Dir.L, some 18⟩
  | 17, 1 => some ⟨0, Dir.L, some 17⟩
  | 17, 2 => some ⟨0, Dir.R, some 14⟩
  | 17, 3 => some ⟨3, Dir.R, some 18⟩
  | 18, 0 => some ⟨1, Dir.R, some 17⟩
  | 18, 1 => some ⟨2, Dir.L, some 18⟩
  | 18, 2 => some ⟨3, Dir.L, some 18⟩
  | 18, 3 => some ⟨3, Dir.L, some 13⟩
  | _, _ => none

theorem valid_19_4 : ValidTM 19 4 tm_19_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 19 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 19 => rfl

def landmark_19_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 3, 3] }
theorem reaches_landmark_19_4 : steps tm_19_4 164 initConfig = some landmark_19_4 := by
  have h0 : steps tm_19_4 35 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_19_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } = some { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } := rfl
  have h1 : steps tm_19_4 70 initConfig = some { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } := steps_add tm_19_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_19_4 35 { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } = some { st := some 2, left := [1, 1, 3], cur := 2, right := [] } := rfl
  have h2 : steps tm_19_4 105 initConfig = some { st := some 2, left := [1, 1, 3], cur := 2, right := [] } := steps_add tm_19_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_19_4 35 { st := some 2, left := [1, 1, 3], cur := 2, right := [] } = some { st := some 14, left := [1, 3], cur := 1, right := [] } := rfl
  have h3 : steps tm_19_4 140 initConfig = some { st := some 14, left := [1, 3], cur := 1, right := [] } := steps_add tm_19_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_19_4 24 { st := some 14, left := [1, 3], cur := 1, right := [] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 3, 3] } := rfl
  have h4 : steps tm_19_4 164 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 3, 3] } := steps_add tm_19_4 140 24 initConfig _ _ h3 hstep4
  exact h4

/-! ### 19x4 — fwp26_4 @ step 72 -/
def tm_19_4_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 16⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨2, Dir.L, some 15⟩
  | 12, 2 => some ⟨3, Dir.L, some 14⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.L, some 13⟩
  | 14, 1 => some ⟨3, Dir.L, some 14⟩
  | 14, 2 => some ⟨3, Dir.L, some 14⟩
  | 14, 3 => some ⟨3, Dir.L, some 14⟩
  | 15, 0 => some ⟨3, Dir.L, some 14⟩
  | 15, 1 => some ⟨2, Dir.L, some 15⟩
  | 15, 2 => some ⟨2, Dir.L, some 15⟩
  | 15, 3 => some ⟨2, Dir.L, some 15⟩
  | 16, 0 => some ⟨0, Dir.L, some 4⟩
  | 16, 1 => some ⟨0, Dir.L, some 1⟩
  | 16, 2 => some ⟨0, Dir.L, some 16⟩
  | 16, 3 => some ⟨0, Dir.L, some 17⟩
  | 17, 0 => some ⟨1, Dir.R, some 4⟩
  | 17, 1 => some ⟨0, Dir.L, some 18⟩
  | 17, 2 => some ⟨1, Dir.R, some 18⟩
  | 17, 3 => some ⟨2, Dir.R, some 18⟩
  | 18, 0 => some ⟨1, Dir.R, some 17⟩
  | 18, 1 => some ⟨2, Dir.L, some 18⟩
  | 18, 2 => some ⟨3, Dir.L, some 17⟩
  | 18, 3 => some ⟨1, Dir.L, some 12⟩
  | _, _ => none

theorem valid_19_4_1 : ValidTM 19 4 tm_19_4_1 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 19 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 19 => rfl

def landmark_19_4_1 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] }
theorem reaches_landmark_19_4_1 : steps tm_19_4_1 72 initConfig = some landmark_19_4_1 := by
  have h0 : steps tm_19_4_1 35 initConfig = some { st := some 18, left := [1, 1], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_19_4_1 35 { st := some 18, left := [1, 1], cur := 0, right := [] } = some { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := rfl
  have h1 : steps tm_19_4_1 70 initConfig = some { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := steps_add tm_19_4_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_19_4_1 2 { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := rfl
  have h2 : steps tm_19_4_1 72 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := steps_add tm_19_4_1 70 2 initConfig _ _ h1 hstep2
  exact h2

/-! ### 20x4 — fwp25_4 @ step 141 -/
def tm_20_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 15⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 1⟩
  | 12, 2 => some ⟨3, Dir.L, some 14⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.L, some 13⟩
  | 14, 1 => some ⟨3, Dir.L, some 14⟩
  | 14, 2 => some ⟨3, Dir.L, some 14⟩
  | 14, 3 => some ⟨3, Dir.L, some 14⟩
  | 15, 0 => some ⟨0, Dir.L, some 4⟩
  | 15, 1 => some ⟨0, Dir.L, some 17⟩
  | 15, 2 => some ⟨0, Dir.L, some 12⟩
  | 15, 3 => some ⟨0, Dir.L, some 16⟩
  | 16, 0 => some ⟨1, Dir.R, some 1⟩
  | 16, 1 => some ⟨0, Dir.L, some 18⟩
  | 16, 2 => some ⟨0, Dir.R, some 18⟩
  | 16, 3 => some ⟨3, Dir.L, some 19⟩
  | 17, 0 => some ⟨1, Dir.R, some 4⟩
  | 17, 1 => some ⟨0, Dir.L, some 19⟩
  | 17, 2 => some ⟨2, Dir.R, some 18⟩
  | 17, 3 => some ⟨2, Dir.L, some 14⟩
  | 18, 0 => some ⟨1, Dir.R, some 16⟩
  | 18, 1 => some ⟨1, Dir.R, some 18⟩
  | 18, 2 => some ⟨2, Dir.R, some 16⟩
  | 18, 3 => some ⟨1, Dir.R, some 19⟩
  | 19, 0 => some ⟨1, Dir.L, some 18⟩
  | 19, 1 => some ⟨2, Dir.L, some 18⟩
  | 19, 2 => some ⟨3, Dir.L, some 15⟩
  | 19, 3 => some ⟨1, Dir.R, some 17⟩
  | _, _ => none

theorem valid_20_4 : ValidTM 20 4 tm_20_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 19 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 20 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 19 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 20 => rfl

def landmark_20_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 3, 2] }
theorem reaches_landmark_20_4 : steps tm_20_4 141 initConfig = some landmark_20_4 := by
  have h0 : steps tm_20_4 35 initConfig = some { st := some 18, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_20_4 35 { st := some 18, left := [], cur := 1, right := [] } = some { st := some 15, left := [], cur := 1, right := [3] } := rfl
  have h1 : steps tm_20_4 70 initConfig = some { st := some 15, left := [], cur := 1, right := [3] } := steps_add tm_20_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_20_4 35 { st := some 15, left := [], cur := 1, right := [3] } = some { st := some 17, left := [1], cur := 0, right := [0, 3] } := rfl
  have h2 : steps tm_20_4 105 initConfig = some { st := some 17, left := [1], cur := 0, right := [0, 3] } := steps_add tm_20_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_20_4 35 { st := some 17, left := [1], cur := 0, right := [0, 3] } = some { st := some 2, left := [3], cur := 3, right := [0, 0, 0, 0, 3, 3, 2] } := rfl
  have h3 : steps tm_20_4 140 initConfig = some { st := some 2, left := [3], cur := 3, right := [0, 0, 0, 0, 3, 3, 2] } := steps_add tm_20_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_20_4 1 { st := some 2, left := [3], cur := 3, right := [0, 0, 0, 0, 3, 3, 2] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 3, 2] } := rfl
  have h4 : steps tm_20_4 141 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 3, 2] } := steps_add tm_20_4 140 1 initConfig _ _ h3 hstep4
  exact h4

/-! ### 21x4 — fwp24_4 @ step 254 -/
def tm_21_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨0, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨0, Dir.L, some 1⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 3 => some ⟨3, Dir.L, some 6⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 2⟩
  | 3, 2 => some ⟨1, Dir.L, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 8⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 10⟩
  | 8, 2 => some ⟨1, Dir.L, some 11⟩
  | 8, 3 => some ⟨3, Dir.R, some 12⟩
  | 9, 0 => some ⟨3, Dir.R, some 2⟩
  | 9, 1 => some ⟨3, Dir.L, some 9⟩
  | 9, 2 => some ⟨3, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 10, 0 => some ⟨0, Dir.L, some 5⟩
  | 10, 1 => some ⟨0, Dir.L, some 10⟩
  | 10, 2 => some ⟨0, Dir.L, some 10⟩
  | 10, 3 => some ⟨0, Dir.L, some 10⟩
  | 11, 0 => some ⟨0, Dir.L, some 10⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.L, some 14⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | 12, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 0 => some ⟨0, Dir.L, some 11⟩
  | 13, 1 => some ⟨2, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨2, Dir.L, some 13⟩
  | 14, 0 => some ⟨1, Dir.L, some 4⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨2, Dir.R, some 16⟩
  | 14, 3 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨1, Dir.L, some 6⟩
  | 15, 1 => some ⟨0, Dir.L, some 16⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨1, Dir.R, some 20⟩
  | 16, 0 => some ⟨1, Dir.L, some 15⟩
  | 16, 1 => some ⟨0, Dir.L, some 17⟩
  | 16, 2 => some ⟨2, Dir.R, some 19⟩
  | 16, 3 => some ⟨2, Dir.L, some 19⟩
  | 17, 0 => some ⟨0, Dir.L, some 18⟩
  | 17, 1 => some ⟨0, Dir.L, some 17⟩
  | 17, 2 => some ⟨0, Dir.R, some 14⟩
  | 17, 3 => some ⟨2, Dir.L, some 20⟩
  | 18, 0 => some ⟨1, Dir.R, some 17⟩
  | 18, 1 => some ⟨0, Dir.L, some 19⟩
  | 18, 2 => some ⟨1, Dir.R, some 20⟩
  | 18, 3 => some ⟨3, Dir.L, some 18⟩
  | 19, 0 => some ⟨1, Dir.R, some 18⟩
  | 19, 1 => some ⟨0, Dir.L, some 20⟩
  | 19, 2 => some ⟨2, Dir.L, some 20⟩
  | 19, 3 => some ⟨3, Dir.R, some 20⟩
  | 20, 0 => some ⟨1, Dir.R, some 19⟩
  | 20, 1 => some ⟨2, Dir.L, some 18⟩
  | 20, 2 => some ⟨3, Dir.L, some 20⟩
  | 20, 3 => some ⟨3, Dir.L, some 12⟩
  | _, _ => none

theorem valid_21_4 : ValidTM 21 4 tm_21_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 19 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | 20 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | _ + 4 => omega
    | _ + 21 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 19 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | 20 =>
      match sym with
      | 0 | 1 | 2 | 3 => omega
      | _ + 4 => rfl
    | _ + 21 => rfl

def landmark_21_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 2, 2, 3, 3] }
theorem reaches_landmark_21_4 : steps tm_21_4 254 initConfig = some landmark_21_4 := by
  have h0 : steps tm_21_4 35 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_21_4 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 2] } = some { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } := rfl
  have h1 : steps tm_21_4 70 initConfig = some { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } := steps_add tm_21_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_21_4 35 { st := some 7, left := [1], cur := 2, right := [1, 1, 2] } = some { st := some 18, left := [], cur := 0, right := [2] } := rfl
  have h2 : steps tm_21_4 105 initConfig = some { st := some 18, left := [], cur := 0, right := [2] } := steps_add tm_21_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_21_4 35 { st := some 18, left := [], cur := 0, right := [2] } = some { st := some 4, left := [1], cur := 1, right := [1, 2] } := rfl
  have h3 : steps tm_21_4 140 initConfig = some { st := some 4, left := [1], cur := 1, right := [1, 2] } := steps_add tm_21_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_21_4 35 { st := some 4, left := [1], cur := 1, right := [1, 2] } = some { st := some 4, left := [1], cur := 1, right := [1, 1, 2] } := rfl
  have h4 : steps tm_21_4 175 initConfig = some { st := some 4, left := [1], cur := 1, right := [1, 1, 2] } := steps_add tm_21_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_21_4 35 { st := some 4, left := [1], cur := 1, right := [1, 1, 2] } = some { st := some 18, left := [1, 1, 3, 1, 1], cur := 0, right := [] } := rfl
  have h5 : steps tm_21_4 210 initConfig = some { st := some 18, left := [1, 1, 3, 1, 1], cur := 0, right := [] } := steps_add tm_21_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_21_4 35 { st := some 18, left := [1, 1, 3, 1, 1], cur := 0, right := [] } = some { st := some 13, left := [], cur := 1, right := [2, 2, 2, 3, 3] } := rfl
  have h6 : steps tm_21_4 245 initConfig = some { st := some 13, left := [], cur := 1, right := [2, 2, 2, 3, 3] } := steps_add tm_21_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_21_4 9 { st := some 13, left := [], cur := 1, right := [2, 2, 2, 3, 3] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 2, 2, 3, 3] } := rfl
  have h7 : steps tm_21_4 254 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 2, 2, 2, 2, 3, 3] } := steps_add tm_21_4 245 9 initConfig _ _ h6 hstep7
  exact h7

end BB.Landmarks2026_11_23.S4
