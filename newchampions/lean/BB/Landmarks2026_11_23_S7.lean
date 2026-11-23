/-
  BB/Landmarks2026_11_23_S7.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs
  for 15 7-symbol landmark machines (2026-11-23 sweep).
-/
import BB.TM

namespace BB.Landmarks2026_11_23.S7
open BB

/-! ### 3x7 — fw1_6 @ step 312 -/
def tm_3_7 : TM
  | 0, 0 => some ⟨6, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨5, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.L, some 2⟩
  | 0, 6 => some ⟨0, Dir.L, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 1⟩
  | 1, 5 => some ⟨4, Dir.L, some 2⟩
  | 1, 6 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨4, Dir.R, some 0⟩
  | 2, 6 => some ⟨0, Dir.R, some 0⟩
  | _, _ => none

theorem valid_3_7 : ValidTM 3 7 tm_3_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 3 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 3 => rfl

def landmark_3_7 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_3_7 : steps tm_3_7 312 initConfig = some landmark_3_7 := by
  have h0 : steps tm_3_7 35 initConfig = some { st := some 2, left := [], cur := 0, right := [3, 1, 1, 4, 6] } := rfl
  have hstep1 : steps tm_3_7 35 { st := some 2, left := [], cur := 0, right := [3, 1, 1, 4, 6] } = some { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 4, 6] } := rfl
  have h1 : steps tm_3_7 70 initConfig = some { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 4, 6] } := steps_add tm_3_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_3_7 35 { st := some 1, left := [3, 3, 3], cur := 2, right := [1, 1, 4, 6] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 6] } := rfl
  have h2 : steps tm_3_7 105 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 6] } := steps_add tm_3_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_3_7 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 6] } = some { st := some 2, left := [2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 6] } := rfl
  have h3 : steps tm_3_7 140 initConfig = some { st := some 2, left := [2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 6] } := steps_add tm_3_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_3_7 35 { st := some 2, left := [2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 6] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 0, right := [] } := rfl
  have h4 : steps tm_3_7 175 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 0, right := [] } := steps_add tm_3_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_3_7 35 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 6] } := rfl
  have h5 : steps tm_3_7 210 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 6] } := steps_add tm_3_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_3_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 6] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 6] } := rfl
  have h6 : steps tm_3_7 245 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 6] } := steps_add tm_3_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_3_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 6] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 2, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h7 : steps tm_3_7 280 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 2, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_3_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_3_7 32 { st := some 0, left := [2, 2, 2, 2, 3], cur := 2, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h8 : steps tm_3_7 312 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_3_7 280 32 initConfig _ _ h7 hstep8
  exact h8

/-! ### 4x7 — fw3_7 @ step 108 -/
def tm_4_7 : TM
  | 0, 0 => some ⟨5, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨0, Dir.R, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨0, Dir.L, some 0⟩
  | 0, 6 => some ⟨1, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 3⟩
  | 1, 5 => some ⟨0, Dir.L, some 0⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨6, Dir.L, some 3⟩
  | 2, 6 => some ⟨5, Dir.L, some 3⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨6, Dir.L, some 0⟩
  | 3, 2 => some ⟨6, Dir.L, some 2⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 5 => some ⟨4, Dir.L, some 3⟩
  | 3, 6 => some ⟨6, Dir.L, some 2⟩
  | _, _ => none

theorem valid_4_7 : ValidTM 4 7 tm_4_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 4 => rfl

def landmark_4_7 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6] }
theorem reaches_landmark_4_7 : steps tm_4_7 108 initConfig = some landmark_4_7 := by
  have h0 : steps tm_4_7 35 initConfig = some { st := some 1, left := [3], cur := 6, right := [6, 6, 6] } := rfl
  have hstep1 : steps tm_4_7 35 { st := some 1, left := [3], cur := 6, right := [6, 6, 6] } = some { st := some 0, left := [2, 3], cur := 4, right := [5, 5, 5, 5, 6, 6] } := rfl
  have h1 : steps tm_4_7 70 initConfig = some { st := some 0, left := [2, 3], cur := 4, right := [5, 5, 5, 5, 6, 6] } := steps_add tm_4_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_7 35 { st := some 0, left := [2, 3], cur := 4, right := [5, 5, 5, 5, 6, 6] } = some { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4, 4, 4, 5, 5, 5, 6, 6] } := rfl
  have h2 : steps tm_4_7 105 initConfig = some { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4, 4, 4, 5, 5, 5, 6, 6] } := steps_add tm_4_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_7 3 { st := some 2, left := [], cur := 2, right := [1, 1, 4, 4, 4, 4, 5, 5, 5, 6, 6] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6] } := rfl
  have h3 : steps tm_4_7 108 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6] } := steps_add tm_4_7 105 3 initConfig _ _ h2 hstep3
  exact h3

/-! ### 4x7 — tfw_6 @ step 276 -/
def tm_4_7_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.L, some 1⟩
  | 0, 6 => some ⟨6, Dir.R, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨5, Dir.L, some 2⟩
  | 1, 5 => some ⟨1, Dir.R, none⟩
  | 1, 6 => some ⟨0, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨5, Dir.L, some 2⟩
  | 2, 6 => some ⟨2, Dir.R, some 3⟩
  | 3, 0 => some ⟨0, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 1⟩
  | 3, 2 => some ⟨4, Dir.R, some 1⟩
  | 3, 3 => some ⟨1, Dir.R, some 1⟩
  | 3, 4 => some ⟨5, Dir.R, some 1⟩
  | 3, 5 => some ⟨6, Dir.L, some 2⟩
  | 3, 6 => some ⟨2, Dir.L, some 1⟩
  | _, _ => none

theorem valid_4_7_1 : ValidTM 4 7 tm_4_7_1 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, trivial⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 4 => rfl

def landmark_4_7_1 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] }
theorem reaches_landmark_4_7_1 : steps tm_4_7_1 276 initConfig = some landmark_4_7_1 := by
  have h0 : steps tm_4_7_1 35 initConfig = some { st := some 2, left := [], cur := 2, right := [3] } := rfl
  have hstep1 : steps tm_4_7_1 35 { st := some 2, left := [], cur := 2, right := [3] } = some { st := some 1, left := [3], cur := 1, right := [1, 1, 1, 3] } := rfl
  have h1 : steps tm_4_7_1 70 initConfig = some { st := some 1, left := [3], cur := 1, right := [1, 1, 1, 3] } := steps_add tm_4_7_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_7_1 35 { st := some 1, left := [3], cur := 1, right := [1, 1, 1, 3] } = some { st := some 1, left := [4, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := rfl
  have h2 : steps tm_4_7_1 105 initConfig = some { st := some 1, left := [4, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } := steps_add tm_4_7_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_7_1 35 { st := some 1, left := [4, 3, 3, 3, 3, 3, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [3, 3, 3] } := rfl
  have h3 : steps tm_4_7_1 140 initConfig = some { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [3, 3, 3] } := steps_add tm_4_7_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_7_1 35 { st := some 2, left := [2, 3, 3, 3], cur := 2, right := [3, 3, 3] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3] } := rfl
  have h4 : steps tm_4_7_1 175 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3] } := steps_add tm_4_7_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_7_1 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3] } = some { st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 6] } := rfl
  have h5 : steps tm_4_7_1 210 initConfig = some { st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 6] } := steps_add tm_4_7_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_7_1 35 { st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 6] } = some { st := some 2, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 2] } := rfl
  have h6 : steps tm_4_7_1 245 initConfig = some { st := some 2, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 2] } := steps_add tm_4_7_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_7_1 31 { st := some 2, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := rfl
  have h7 : steps tm_4_7_1 276 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := steps_add tm_4_7_1 245 31 initConfig _ _ h6 hstep7
  exact h7

/-! ### 5x7 — fw1_6 @ step 3000 -/
def tm_5_7 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨0, Dir.L, some 4⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.L, some 2⟩
  | 0, 6 => some ⟨6, Dir.L, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 1⟩
  | 1, 5 => some ⟨4, Dir.L, some 2⟩
  | 1, 6 => some ⟨6, Dir.R, some 4⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨5, Dir.R, some 0⟩
  | 2, 6 => some ⟨4, Dir.L, some 2⟩
  | 3, 0 => some ⟨1, Dir.R, some 0⟩
  | 3, 1 => some ⟨0, Dir.L, some 4⟩
  | 3, 2 => some ⟨0, Dir.L, some 3⟩
  | 3, 3 => some ⟨1, Dir.L, some 4⟩
  | 3, 4 => some ⟨5, Dir.L, some 3⟩
  | 3, 5 => some ⟨5, Dir.R, some 3⟩
  | 3, 6 => some ⟨5, Dir.L, some 4⟩
  | 4, 0 => some ⟨1, Dir.L, some 3⟩
  | 4, 1 => some ⟨2, Dir.L, some 3⟩
  | 4, 2 => some ⟨4, Dir.L, some 4⟩
  | 4, 3 => some ⟨0, Dir.R, some 4⟩
  | 4, 4 => some ⟨4, Dir.R, some 0⟩
  | 4, 5 => some ⟨6, Dir.L, some 0⟩
  | 4, 6 => some ⟨6, Dir.R, some 0⟩
  | _, _ => none

theorem valid_5_7 : ValidTM 5 7 tm_5_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 5 => rfl

def landmark_5_7 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5] }
theorem reaches_landmark_5_7 : steps tm_5_7 3000 initConfig = some landmark_5_7 := by
  have h0 : steps tm_5_7 35 initConfig = some { st := some 4, left := [], cur := 0, right := [1, 2] } := rfl
  have hstep1 : steps tm_5_7 35 { st := some 4, left := [], cur := 0, right := [1, 2] } = some { st := some 2, left := [3, 3], cur := 3, right := [3, 5] } := rfl
  have h1 : steps tm_5_7 70 initConfig = some { st := some 2, left := [3, 3], cur := 3, right := [3, 5] } := steps_add tm_5_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_7 35 { st := some 2, left := [3, 3], cur := 3, right := [3, 5] } = some { st := some 4, left := [6, 3, 5, 2, 2, 3], cur := 0, right := [] } := rfl
  have h2 : steps tm_5_7 105 initConfig = some { st := some 4, left := [6, 3, 5, 2, 2, 3], cur := 0, right := [] } := steps_add tm_5_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_7 35 { st := some 4, left := [6, 3, 5, 2, 2, 3], cur := 0, right := [] } = some { st := some 1, left := [3, 5, 2, 2, 3], cur := 6, right := [5] } := rfl
  have h3 : steps tm_5_7 140 initConfig = some { st := some 1, left := [3, 5, 2, 2, 3], cur := 6, right := [5] } := steps_add tm_5_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_7 35 { st := some 1, left := [3, 5, 2, 2, 3], cur := 6, right := [5] } = some { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 3, 6, 6] } := rfl
  have h4 : steps tm_5_7 175 initConfig = some { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_7 35 { st := some 0, left := [2, 3], cur := 3, right := [1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 3, 6, 6] } := rfl
  have h5 : steps tm_5_7 210 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 3, 6, 6] } := steps_add tm_5_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [3, 3, 1, 4, 3, 6, 6] } = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h6 : steps tm_5_7 245 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_7 35 { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h7 : steps tm_5_7 280 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_5_7 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h8 : steps tm_5_7 315 initConfig = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_5_7 35 { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6, 6] } := rfl
  have h9 : steps tm_5_7 350 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_5_7 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6, 6] } := rfl
  have h10 : steps tm_5_7 385 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6, 6] } := steps_add tm_5_7 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 3, 6, 6] } := rfl
  have h11 : steps tm_5_7 420 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 3, 6, 6] } := steps_add tm_5_7 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h12 : steps tm_5_7 455 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h13 : steps tm_5_7 490 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_5_7 35 { st := some 2, left := [], cur := 3, right := [1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h14 : steps tm_5_7 525 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_5_7 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h15 : steps tm_5_7 560 initConfig = some { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_5_7 35 { st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h16 : steps tm_5_7 595 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_5_7 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h17 : steps tm_5_7 630 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h18 : steps tm_5_7 665 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h19 : steps tm_5_7 700 initConfig = some { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_5_7 35 { st := some 2, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h20 : steps tm_5_7 735 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h21 : steps tm_5_7 770 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h22 : steps tm_5_7 805 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h23 : steps tm_5_7 840 initConfig = some { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h24 : steps tm_5_7 875 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h25 : steps tm_5_7 910 initConfig = some { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_5_7 35 { st := some 2, left := [3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h26 : steps tm_5_7 945 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h27 : steps tm_5_7 980 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h28 : steps tm_5_7 1015 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } := rfl
  have h29 : steps tm_5_7 1050 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } := rfl
  have h30 : steps tm_5_7 1085 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 3, 6, 6] } := rfl
  have h31 : steps tm_5_7 1120 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } := rfl
  have h32 : steps tm_5_7 1155 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } := rfl
  have h33 : steps tm_5_7 1190 initConfig = some { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 3, 6, 6] } := rfl
  have h34 : steps tm_5_7 1225 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 3, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h35 : steps tm_5_7 1260 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h36 : steps tm_5_7 1295 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := rfl
  have h37 : steps tm_5_7 1330 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } := steps_add tm_5_7 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h38 : steps tm_5_7 1365 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h39 : steps tm_5_7 1400 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := rfl
  have h40 : steps tm_5_7 1435 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } := steps_add tm_5_7 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 6] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 6, 6] } := rfl
  have h41 : steps tm_5_7 1470 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 6, 6] } := steps_add tm_5_7 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_5_7 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := rfl
  have h42 : steps tm_5_7 1505 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := steps_add tm_5_7 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := rfl
  have h43 : steps tm_5_7 1540 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := steps_add tm_5_7 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := rfl
  have h44 : steps tm_5_7 1575 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } := steps_add tm_5_7 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_5_7 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 5] } := rfl
  have h45 : steps tm_5_7 1610 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 5] } := steps_add tm_5_7 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := rfl
  have h46 : steps tm_5_7 1645 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := steps_add tm_5_7 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := rfl
  have h47 : steps tm_5_7 1680 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_5_7 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } := rfl
  have h48 : steps tm_5_7 1715 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } := steps_add tm_5_7 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h49 : steps tm_5_7 1750 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := rfl
  have h50 : steps tm_5_7 1785 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := steps_add tm_5_7 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h51 : steps tm_5_7 1820 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h52 : steps tm_5_7 1855 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_5_7 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h53 : steps tm_5_7 1890 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h54 : steps tm_5_7 1925 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h55 : steps tm_5_7 1960 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_5_7 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h56 : steps tm_5_7 1995 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h57 : steps tm_5_7 2030 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := rfl
  have h58 : steps tm_5_7 2065 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := steps_add tm_5_7 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h59 : steps tm_5_7 2100 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h60 : steps tm_5_7 2135 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h61 : steps tm_5_7 2170 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } := rfl
  have h62 : steps tm_5_7 2205 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } := steps_add tm_5_7 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h63 : steps tm_5_7 2240 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h64 : steps tm_5_7 2275 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_5_7 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := rfl
  have h65 : steps tm_5_7 2310 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h66 : steps tm_5_7 2345 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h67 : steps tm_5_7 2380 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := rfl
  have h68 : steps tm_5_7 2415 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } := steps_add tm_5_7 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h69 : steps tm_5_7 2450 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h70 : steps tm_5_7 2485 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h71 : steps tm_5_7 2520 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h72 : steps tm_5_7 2555 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2520 35 initConfig _ _ h71 hstep72
  have hstep73 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5] } := rfl
  have h73 : steps tm_5_7 2590 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5] } := steps_add tm_5_7 2555 35 initConfig _ _ h72 hstep73
  have hstep74 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5] } = some { st := some 2, left := [3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h74 : steps tm_5_7 2625 initConfig = some { st := some 2, left := [3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2590 35 initConfig _ _ h73 hstep74
  have hstep75 : steps tm_5_7 35 { st := some 2, left := [3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4, 5] } := rfl
  have h75 : steps tm_5_7 2660 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4, 5] } := steps_add tm_5_7 2625 35 initConfig _ _ h74 hstep75
  have hstep76 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 2, right := [3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h76 : steps tm_5_7 2695 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2660 35 initConfig _ _ h75 hstep76
  have hstep77 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := rfl
  have h77 : steps tm_5_7 2730 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2695 35 initConfig _ _ h76 hstep77
  have hstep78 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h78 : steps tm_5_7 2765 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2730 35 initConfig _ _ h77 hstep78
  have hstep79 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h79 : steps tm_5_7 2800 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2765 35 initConfig _ _ h78 hstep79
  have hstep80 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := rfl
  have h80 : steps tm_5_7 2835 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } := steps_add tm_5_7 2800 35 initConfig _ _ h79 hstep80
  have hstep81 : steps tm_5_7 35 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 1, 4, 5] } := rfl
  have h81 : steps tm_5_7 2870 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 1, 4, 5] } := steps_add tm_5_7 2835 35 initConfig _ _ h80 hstep81
  have hstep82 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 1, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5] } := rfl
  have h82 : steps tm_5_7 2905 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5] } := steps_add tm_5_7 2870 35 initConfig _ _ h81 hstep82
  have hstep83 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } := rfl
  have h83 : steps tm_5_7 2940 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } := steps_add tm_5_7 2905 35 initConfig _ _ h82 hstep83
  have hstep84 : steps tm_5_7 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } := rfl
  have h84 : steps tm_5_7 2975 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } := steps_add tm_5_7 2940 35 initConfig _ _ h83 hstep84
  have hstep85 : steps tm_5_7 25 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 4, 5] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5] } := rfl
  have h85 : steps tm_5_7 3000 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5] } := steps_add tm_5_7 2975 25 initConfig _ _ h84 hstep85
  exact h85

/-! ### 5x7 — fw3_6 @ step 94 -/
def tm_5_7_1 : TM
  | 0, 0 => some ⟨1, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨5, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨3, Dir.R, some 0⟩
  | 0, 6 => some ⟨6, Dir.L, some 4⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 3⟩
  | 1, 5 => some ⟨2, Dir.L, some 0⟩
  | 1, 6 => some ⟨6, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 0⟩
  | 2, 6 => some ⟨6, Dir.R, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨0, Dir.L, some 0⟩
  | 3, 2 => some ⟨5, Dir.L, some 4⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 5 => some ⟨4, Dir.L, some 3⟩
  | 3, 6 => some ⟨2, Dir.L, some 4⟩
  | 4, 0 => some ⟨4, Dir.L, some 2⟩
  | 4, 1 => some ⟨4, Dir.R, some 0⟩
  | 4, 2 => some ⟨0, Dir.R, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨2, Dir.R, some 3⟩
  | 4, 5 => some ⟨6, Dir.L, some 2⟩
  | 4, 6 => some ⟨6, Dir.R, some 4⟩
  | _, _ => none

theorem valid_5_7_1 : ValidTM 5 7 tm_5_7_1 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 5 => rfl

def landmark_5_7_1 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 5, 5, 5, 2, 2] }
theorem reaches_landmark_5_7_1 : steps tm_5_7_1 94 initConfig = some landmark_5_7_1 := by
  have h0 : steps tm_5_7_1 35 initConfig = some { st := some 4, left := [0, 3], cur := 6, right := [1] } := rfl
  have hstep1 : steps tm_5_7_1 35 { st := some 4, left := [0, 3], cur := 6, right := [1] } = some { st := some 3, left := [], cur := 0, right := [4, 4, 4, 5, 5, 5, 2, 2] } := rfl
  have h1 : steps tm_5_7_1 70 initConfig = some { st := some 3, left := [], cur := 0, right := [4, 4, 4, 5, 5, 5, 2, 2] } := steps_add tm_5_7_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_7_1 24 { st := some 3, left := [], cur := 0, right := [4, 4, 4, 5, 5, 5, 2, 2] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 5, 5, 5, 2, 2] } := rfl
  have h2 : steps tm_5_7_1 94 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 5, 5, 5, 2, 2] } := steps_add tm_5_7_1 70 24 initConfig _ _ h1 hstep2
  exact h2

/-! ### 5x7 — fw3_7 @ step 116 -/
def tm_5_7_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨0, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.L, some 3⟩
  | 0, 6 => some ⟨6, Dir.R, some 4⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 3⟩
  | 1, 5 => some ⟨1, Dir.L, some 3⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨4, Dir.R, some 0⟩
  | 2, 6 => some ⟨5, Dir.L, some 3⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨4, Dir.R, some 0⟩
  | 3, 2 => some ⟨6, Dir.L, some 2⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 5 => some ⟨4, Dir.L, some 3⟩
  | 3, 6 => some ⟨6, Dir.L, some 2⟩
  | 4, 0 => some ⟨1, Dir.R, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 4⟩
  | 4, 3 => some ⟨2, Dir.L, some 4⟩
  | 4, 4 => some ⟨5, Dir.L, some 2⟩
  | 4, 5 => some ⟨6, Dir.R, some 4⟩
  | 4, 6 => some ⟨6, Dir.L, some 3⟩
  | _, _ => none

theorem valid_5_7_2 : ValidTM 5 7 tm_5_7_2 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 5 => rfl

def landmark_5_7_2 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 6, 6] }
theorem reaches_landmark_5_7_2 : steps tm_5_7_2 116 initConfig = some landmark_5_7_2 := by
  have h0 : steps tm_5_7_2 35 initConfig = some { st := some 2, left := [], cur := 2, right := [3, 5] } := rfl
  have hstep1 : steps tm_5_7_2 35 { st := some 2, left := [], cur := 2, right := [3, 5] } = some { st := some 3, left := [], cur := 2, right := [5, 5, 6, 6] } := rfl
  have h1 : steps tm_5_7_2 70 initConfig = some { st := some 3, left := [], cur := 2, right := [5, 5, 6, 6] } := steps_add tm_5_7_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_7_2 35 { st := some 3, left := [], cur := 2, right := [5, 5, 6, 6] } = some { st := some 0, left := [2, 3], cur := 3, right := [4, 4, 4, 4, 5, 6, 6] } := rfl
  have h2 : steps tm_5_7_2 105 initConfig = some { st := some 0, left := [2, 3], cur := 3, right := [4, 4, 4, 4, 5, 6, 6] } := steps_add tm_5_7_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_7_2 11 { st := some 0, left := [2, 3], cur := 3, right := [4, 4, 4, 4, 5, 6, 6] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 6, 6] } := rfl
  have h3 : steps tm_5_7_2 116 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 6, 6] } := steps_add tm_5_7_2 105 11 initConfig _ _ h2 hstep3
  exact h3

/-! ### 5x7 — fwm21_7 @ step 56 -/
def tm_5_7_3 : TM
  | 0, 0 => some ⟨4, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.L, some 0⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 0, 6 => some ⟨0, Dir.L, some 4⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 4⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.L, some 0⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 0⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨5, Dir.L, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | _, _ => none

theorem valid_5_7_3 : ValidTM 5 7 tm_5_7_3 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 5 => rfl

def landmark_5_7_3 : Config := { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] }
theorem reaches_landmark_5_7_3 : steps tm_5_7_3 56 initConfig = some landmark_5_7_3 := by
  have h0 : steps tm_5_7_3 35 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 0, right := [2] } := rfl
  have hstep1 : steps tm_5_7_3 21 { st := some 0, left := [2, 2, 2, 2, 3], cur := 0, right := [2] } = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] } := rfl
  have h1 : steps tm_5_7_3 56 initConfig = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] } := steps_add tm_5_7_3 35 21 initConfig _ _ h0 hstep1
  exact h1

/-! ### 6x7 — fwm21_7 @ step 139 -/
def tm_6_7 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.L, some 0⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 0, 6 => some ⟨2, Dir.L, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 4⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨6, Dir.L, some 5⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 0⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨5, Dir.L, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 5, 0 => some ⟨0, Dir.L, some 2⟩
  | 5, 1 => some ⟨4, Dir.L, some 3⟩
  | 5, 2 => some ⟨0, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 3⟩
  | 5, 4 => some ⟨2, Dir.R, some 3⟩
  | 5, 5 => some ⟨1, Dir.R, some 0⟩
  | 5, 6 => some ⟨4, Dir.R, some 5⟩
  | _, _ => none

theorem valid_6_7 : ValidTM 6 7 tm_6_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 6 => rfl

def landmark_6_7 : Config := { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 2] }
theorem reaches_landmark_6_7 : steps tm_6_7 139 initConfig = some landmark_6_7 := by
  have h0 : steps tm_6_7 35 initConfig = some { st := some 0, left := [3], cur := 0, right := [6] } := rfl
  have hstep1 : steps tm_6_7 35 { st := some 0, left := [3], cur := 0, right := [6] } = some { st := some 3, left := [6, 6, 6, 6, 6], cur := 6, right := [1] } := rfl
  have h1 : steps tm_6_7 70 initConfig = some { st := some 3, left := [6, 6, 6, 6, 6], cur := 6, right := [1] } := steps_add tm_6_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_7 35 { st := some 3, left := [6, 6, 6, 6, 6], cur := 6, right := [1] } = some { st := some 1, left := [2, 3, 3, 3, 3], cur := 4, right := [] } := rfl
  have h2 : steps tm_6_7 105 initConfig = some { st := some 1, left := [2, 3, 3, 3, 3], cur := 4, right := [] } := steps_add tm_6_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_7 34 { st := some 1, left := [2, 3, 3, 3, 3], cur := 4, right := [] } = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := rfl
  have h3 : steps tm_6_7 139 initConfig = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 2] } := steps_add tm_6_7 105 34 initConfig _ _ h2 hstep3
  exact h3

/-! ### 6x7 — fwm21tfw1_7 @ step 53 -/
def tm_6_7_1 : TM
  | 0, 0 => some ⟨5, Dir.L, some 5⟩
  | 0, 1 => some ⟨6, Dir.L, some 0⟩
  | 0, 2 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.R, some 5⟩
  | 0, 4 => some ⟨6, Dir.R, some 0⟩
  | 0, 5 => some ⟨4, Dir.L, some 3⟩
  | 0, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 4⟩
  | 1, 2 => some ⟨6, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 0⟩
  | 1, 5 => some ⟨1, Dir.L, some 4⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 0 => some ⟨6, Dir.R, some 0⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨4, Dir.L, some 2⟩
  | 2, 3 => some ⟨4, Dir.L, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 0⟩
  | 2, 5 => some ⟨6, Dir.L, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.L, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 3⟩
  | 3, 3 => some ⟨2, Dir.R, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 0⟩
  | 3, 5 => some ⟨6, Dir.L, some 2⟩
  | 3, 6 => some ⟨5, Dir.R, some 2⟩
  | 4, 0 => some ⟨6, Dir.R, some 0⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 4, 3 => some ⟨2, Dir.R, some 1⟩
  | 4, 4 => some ⟨2, Dir.R, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 4⟩
  | 4, 6 => some ⟨2, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 5⟩
  | 5, 1 => some ⟨2, Dir.L, some 5⟩
  | 5, 2 => some ⟨1, Dir.L, some 1⟩
  | 5, 3 => some ⟨4, Dir.R, some 5⟩
  | 5, 4 => some ⟨3, Dir.L, some 0⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.R, some 4⟩
  | _, _ => none

theorem valid_6_7_1 : ValidTM 6 7 tm_6_7_1 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 6 => rfl

def landmark_6_7_1 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 3, 5] }
theorem reaches_landmark_6_7_1 : steps tm_6_7_1 53 initConfig = some landmark_6_7_1 := by
  have h0 : steps tm_6_7_1 35 initConfig = some { st := some 1, left := [5, 6], cur := 4, right := [4, 3, 5] } := rfl
  have hstep1 : steps tm_6_7_1 18 { st := some 1, left := [5, 6], cur := 4, right := [4, 3, 5] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 3, 5] } := rfl
  have h1 : steps tm_6_7_1 53 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 3, 5] } := steps_add tm_6_7_1 35 18 initConfig _ _ h0 hstep1
  exact h1

/-! ### 6x7 — fwm2_7 @ step 160 -/
def tm_6_7_2 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.R, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 5⟩
  | 1, 6 => some ⟨2, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.L, some 1⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 5, 0 => some ⟨1, Dir.R, some 1⟩
  | 5, 1 => some ⟨2, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.R, some 3⟩
  | 5, 3 => some ⟨4, Dir.L, some 2⟩
  | 5, 4 => some ⟨0, Dir.L, some 0⟩
  | 5, 5 => some ⟨4, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 3⟩
  | _, _ => none

theorem valid_6_7_2 : ValidTM 6 7 tm_6_7_2 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 6 => rfl

def landmark_6_7_2 : Config := { st := some 0, left := [2, 2, 3], cur := 1, right := [2] }
theorem reaches_landmark_6_7_2 : steps tm_6_7_2 160 initConfig = some landmark_6_7_2 := by
  have h0 : steps tm_6_7_2 35 initConfig = some { st := some 3, left := [0, 3], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_6_7_2 35 { st := some 3, left := [0, 3], cur := 1, right := [] } = some { st := some 3, left := [], cur := 0, right := [4, 4] } := rfl
  have h1 : steps tm_6_7_2 70 initConfig = some { st := some 3, left := [], cur := 0, right := [4, 4] } := steps_add tm_6_7_2 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_7_2 35 { st := some 3, left := [], cur := 0, right := [4, 4] } = some { st := some 3, left := [], cur := 6, right := [6, 6] } := rfl
  have h2 : steps tm_6_7_2 105 initConfig = some { st := some 3, left := [], cur := 6, right := [6, 6] } := steps_add tm_6_7_2 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_7_2 35 { st := some 3, left := [], cur := 6, right := [6, 6] } = some { st := some 3, left := [2, 3, 2, 2], cur := 0, right := [] } := rfl
  have h3 : steps tm_6_7_2 140 initConfig = some { st := some 3, left := [2, 3, 2, 2], cur := 0, right := [] } := steps_add tm_6_7_2 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_7_2 20 { st := some 3, left := [2, 3, 2, 2], cur := 0, right := [] } = some { st := some 0, left := [2, 2, 3], cur := 1, right := [2] } := rfl
  have h4 : steps tm_6_7_2 160 initConfig = some { st := some 0, left := [2, 2, 3], cur := 1, right := [2] } := steps_add tm_6_7_2 140 20 initConfig _ _ h3 hstep4
  exact h4

/-! ### 7x7 — fwm21tfw1_7 @ step 100 -/
def tm_7_7 : TM
  | 0, 0 => some ⟨5, Dir.L, some 5⟩
  | 0, 1 => some ⟨6, Dir.L, some 0⟩
  | 0, 2 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 5⟩
  | 0, 4 => some ⟨6, Dir.R, some 0⟩
  | 0, 5 => some ⟨4, Dir.L, some 3⟩
  | 0, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 4⟩
  | 1, 2 => some ⟨6, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 0⟩
  | 1, 5 => some ⟨1, Dir.L, some 4⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 0 => some ⟨6, Dir.R, some 0⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨4, Dir.L, some 2⟩
  | 2, 3 => some ⟨4, Dir.L, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 0⟩
  | 2, 5 => some ⟨6, Dir.L, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 3, 0 => some ⟨3, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.L, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 3⟩
  | 3, 3 => some ⟨2, Dir.R, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 0⟩
  | 3, 5 => some ⟨6, Dir.L, some 2⟩
  | 3, 6 => some ⟨5, Dir.R, some 2⟩
  | 4, 0 => some ⟨6, Dir.R, some 0⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 4, 3 => some ⟨2, Dir.R, some 1⟩
  | 4, 4 => some ⟨2, Dir.R, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 4⟩
  | 4, 6 => some ⟨2, Dir.L, some 4⟩
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨2, Dir.L, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 0⟩
  | 5, 3 => some ⟨3, Dir.R, some 6⟩
  | 5, 4 => some ⟨6, Dir.R, some 6⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.R, some 4⟩
  | 6, 0 => some ⟨0, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.R, some 5⟩
  | 6, 3 => some ⟨4, Dir.L, some 6⟩
  | 6, 4 => some ⟨1, Dir.L, some 6⟩
  | 6, 5 => some ⟨1, Dir.L, some 5⟩
  | 6, 6 => some ⟨3, Dir.L, some 1⟩
  | _, _ => none

theorem valid_7_7 : ValidTM 7 7 tm_7_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 7 => rfl

def landmark_7_7 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] }
theorem reaches_landmark_7_7 : steps tm_7_7 100 initConfig = some landmark_7_7 := by
  have h0 : steps tm_7_7 35 initConfig = some { st := some 6, left := [3, 2], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_7_7 35 { st := some 6, left := [3, 2], cur := 1, right := [] } = some { st := some 1, left := [2, 5, 6], cur := 1, right := [3, 5] } := rfl
  have h1 : steps tm_7_7 70 initConfig = some { st := some 1, left := [2, 5, 6], cur := 1, right := [3, 5] } := steps_add tm_7_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_7 30 { st := some 1, left := [2, 5, 6], cur := 1, right := [3, 5] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] } := rfl
  have h2 : steps tm_7_7 100 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] } := steps_add tm_7_7 70 30 initConfig _ _ h1 hstep2
  exact h2

/-! ### 7x7 — fwm2_6 @ step 334 -/
def tm_7_7_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.R, some 0⟩
  | 0, 6 => some ⟨0, Dir.L, some 5⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 6⟩
  | 1, 6 => some ⟨4, Dir.R, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  | 2, 6 => some ⟨6, Dir.R, some 1⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨0, Dir.R, some 5⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 2⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  | 3, 6 => some ⟨6, Dir.R, some 5⟩
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨4, Dir.L, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨0, Dir.R, some 5⟩
  | 4, 5 => some ⟨0, Dir.L, some 6⟩
  | 4, 6 => some ⟨2, Dir.L, some 1⟩
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨2, Dir.L, some 6⟩
  | 5, 2 => some ⟨5, Dir.L, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨2, Dir.L, some 6⟩
  | 5, 5 => some ⟨0, Dir.L, some 2⟩
  | 5, 6 => some ⟨6, Dir.R, some 3⟩
  | 6, 0 => some ⟨0, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.R, some 1⟩
  | 6, 3 => some ⟨0, Dir.L, some 5⟩
  | 6, 4 => some ⟨5, Dir.L, some 5⟩
  | 6, 5 => some ⟨6, Dir.L, some 1⟩
  | 6, 6 => some ⟨4, Dir.R, some 5⟩
  | _, _ => none

theorem valid_7_7_1 : ValidTM 7 7 tm_7_7_1 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 7 => rfl

def landmark_7_7_1 : Config := { st := some 0, left := [2, 3, 5], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 4] }
theorem reaches_landmark_7_7_1 : steps tm_7_7_1 334 initConfig = some landmark_7_7_1 := by
  have h0 : steps tm_7_7_1 35 initConfig = some { st := some 5, left := [], cur := 0, right := [1, 1, 0, 0, 1, 3] } := rfl
  have hstep1 : steps tm_7_7_1 35 { st := some 5, left := [], cur := 0, right := [1, 1, 0, 0, 1, 3] } = some { st := some 1, left := [2, 0, 0, 0, 0, 3, 3, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_7_7_1 70 initConfig = some { st := some 1, left := [2, 0, 0, 0, 0, 3, 3, 3], cur := 0, right := [] } := steps_add tm_7_7_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_7_1 35 { st := some 1, left := [2, 0, 0, 0, 0, 3, 3, 3], cur := 0, right := [] } = some { st := some 4, left := [0, 3, 3, 3, 3, 3, 3], cur := 2, right := [] } := rfl
  have h2 : steps tm_7_7_1 105 initConfig = some { st := some 4, left := [0, 3, 3, 3, 3, 3, 3], cur := 2, right := [] } := steps_add tm_7_7_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_7_1 35 { st := some 4, left := [0, 3, 3, 3, 3, 3, 3], cur := 2, right := [] } = some { st := some 2, left := [2, 2, 3, 3], cur := 6, right := [3, 4] } := rfl
  have h3 : steps tm_7_7_1 140 initConfig = some { st := some 2, left := [2, 2, 3, 3], cur := 6, right := [3, 4] } := steps_add tm_7_7_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_7_1 35 { st := some 2, left := [2, 2, 3, 3], cur := 6, right := [3, 4] } = some { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 4, 5, 4] } := rfl
  have h4 : steps tm_7_7_1 175 initConfig = some { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 4, 5, 4] } := steps_add tm_7_7_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_7_1 35 { st := some 2, left := [2, 3, 3], cur := 1, right := [3, 1, 4, 5, 4] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 5, 4] } := rfl
  have h5 : steps tm_7_7_1 210 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 5, 4] } := steps_add tm_7_7_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_7_1 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 4, 5, 4] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 5, 4] } := rfl
  have h6 : steps tm_7_7_1 245 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 5, 4] } := steps_add tm_7_7_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_7_1 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [4, 5, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 5], cur := 6, right := [1, 4] } := rfl
  have h7 : steps tm_7_7_1 280 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 5], cur := 6, right := [1, 4] } := steps_add tm_7_7_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_7_1 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 5], cur := 6, right := [1, 4] } = some { st := some 2, left := [3, 3, 5], cur := 3, right := [3, 1, 1, 1, 1, 1, 2, 0, 4] } := rfl
  have h8 : steps tm_7_7_1 315 initConfig = some { st := some 2, left := [3, 3, 5], cur := 3, right := [3, 1, 1, 1, 1, 1, 2, 0, 4] } := steps_add tm_7_7_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_7_7_1 19 { st := some 2, left := [3, 3, 5], cur := 3, right := [3, 1, 1, 1, 1, 1, 2, 0, 4] } = some { st := some 0, left := [2, 3, 5], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 4] } := rfl
  have h9 : steps tm_7_7_1 334 initConfig = some { st := some 0, left := [2, 3, 5], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 0, 4] } := steps_add tm_7_7_1 315 19 initConfig _ _ h8 hstep9
  exact h9

/-! ### 10x7 — fwp2_6 @ step 327 -/
def tm_10_7 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.R, some 8⟩
  | 0, 6 => some ⟨0, Dir.L, some 9⟩
  | 1, 0 => some ⟨0, Dir.L, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨0, Dir.L, some 9⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨0, Dir.L, some 6⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 9⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨4, Dir.L, some 0⟩
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 6⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨6, Dir.R, some 4⟩
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨0, Dir.R, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨1, Dir.R, some 8⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨1, Dir.R, some 4⟩
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨2, Dir.R, some 1⟩
  | 6, 2 => some ⟨4, Dir.R, some 1⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨6, Dir.L, some 2⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨1, Dir.L, some 6⟩
  | 7, 0 => some ⟨0, Dir.L, some 2⟩
  | 7, 1 => some ⟨1, Dir.R, some 4⟩
  | 7, 2 => some ⟨2, Dir.R, some 4⟩
  | 7, 3 => some ⟨0, Dir.L, some 4⟩
  | 7, 4 => some ⟨4, Dir.R, some 4⟩
  | 7, 5 => some ⟨0, Dir.L, some 8⟩
  | 7, 6 => some ⟨6, Dir.L, some 9⟩
  | 8, 0 => some ⟨0, Dir.L, some 6⟩
  | 8, 1 => some ⟨1, Dir.R, some 8⟩
  | 8, 2 => some ⟨2, Dir.R, some 6⟩
  | 8, 3 => some ⟨0, Dir.L, some 2⟩
  | 8, 4 => some ⟨4, Dir.R, some 6⟩
  | 8, 5 => some ⟨0, Dir.L, some 9⟩
  | 8, 6 => some ⟨6, Dir.R, some 6⟩
  | 9, 0 => some ⟨1, Dir.L, some 2⟩
  | 9, 1 => some ⟨4, Dir.R, some 8⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨6, Dir.R, some 1⟩
  | 9, 4 => some ⟨2, Dir.R, some 6⟩
  | 9, 5 => some ⟨1, Dir.R, some 1⟩
  | 9, 6 => some ⟨6, Dir.R, some 2⟩
  | _, _ => none

theorem valid_10_7 : ValidTM 10 7 tm_10_7 := by
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
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 10 => rfl

def landmark_10_7 : Config := { st := some 0, left := [2, 3, 3, 3, 5, 5, 5], cur := 1, right := [2] }
theorem reaches_landmark_10_7 : steps tm_10_7 327 initConfig = some landmark_10_7 := by
  have h0 : steps tm_10_7 35 initConfig = some { st := some 4, left := [3, 3], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_10_7 35 { st := some 4, left := [3, 3], cur := 1, right := [] } = some { st := some 7, left := [], cur := 2, right := [] } := rfl
  have h1 : steps tm_10_7 70 initConfig = some { st := some 7, left := [], cur := 2, right := [] } := steps_add tm_10_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_10_7 35 { st := some 7, left := [], cur := 2, right := [] } = some { st := some 1, left := [6], cur := 6, right := [] } := rfl
  have h2 : steps tm_10_7 105 initConfig = some { st := some 1, left := [6], cur := 6, right := [] } := steps_add tm_10_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_10_7 35 { st := some 1, left := [6], cur := 6, right := [] } = some { st := some 8, left := [4, 2, 3, 5], cur := 0, right := [] } := rfl
  have h3 : steps tm_10_7 140 initConfig = some { st := some 8, left := [4, 2, 3, 5], cur := 0, right := [] } := steps_add tm_10_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_10_7 35 { st := some 8, left := [4, 2, 3, 5], cur := 0, right := [] } = some { st := some 1, left := [5, 2, 4, 2], cur := 0, right := [] } := rfl
  have h4 : steps tm_10_7 175 initConfig = some { st := some 1, left := [5, 2, 4, 2], cur := 0, right := [] } := steps_add tm_10_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_10_7 35 { st := some 1, left := [5, 2, 4, 2], cur := 0, right := [] } = some { st := some 1, left := [4], cur := 2, right := [] } := rfl
  have h5 : steps tm_10_7 210 initConfig = some { st := some 1, left := [4], cur := 2, right := [] } := steps_add tm_10_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_10_7 35 { st := some 1, left := [4], cur := 2, right := [] } = some { st := some 1, left := [4, 2, 3, 5], cur := 0, right := [1] } := rfl
  have h6 : steps tm_10_7 245 initConfig = some { st := some 1, left := [4, 2, 3, 5], cur := 0, right := [1] } := steps_add tm_10_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_10_7 35 { st := some 1, left := [4, 2, 3, 5], cur := 0, right := [1] } = some { st := some 1, left := [3, 5], cur := 2, right := [4, 3, 6] } := rfl
  have h7 : steps tm_10_7 280 initConfig = some { st := some 1, left := [3, 5], cur := 2, right := [4, 3, 6] } := steps_add tm_10_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_10_7 35 { st := some 1, left := [3, 5], cur := 2, right := [4, 3, 6] } = some { st := some 6, left := [3, 3, 5], cur := 3, right := [3, 1, 2] } := rfl
  have h8 : steps tm_10_7 315 initConfig = some { st := some 6, left := [3, 3, 5], cur := 3, right := [3, 1, 2] } := steps_add tm_10_7 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_10_7 12 { st := some 6, left := [3, 3, 5], cur := 3, right := [3, 1, 2] } = some { st := some 0, left := [2, 3, 3, 3, 5, 5, 5], cur := 1, right := [2] } := rfl
  have h9 : steps tm_10_7 327 initConfig = some { st := some 0, left := [2, 3, 3, 3, 5, 5, 5], cur := 1, right := [2] } := steps_add tm_10_7 315 12 initConfig _ _ h8 hstep9
  exact h9

/-! ### 20x7 — fe1_7 @ step 452 -/
def tm_20_7 : TM
  | 0, 0 => some ⟨6, Dir.L, some 5⟩
  | 0, 1 => none
  | 0, 2 => some ⟨0, Dir.R, some 5⟩
  | 0, 3 => some ⟨0, Dir.R, some 3⟩
  | 0, 4 => some ⟨1, Dir.L, some 13⟩
  | 0, 5 => some ⟨6, Dir.R, some 5⟩
  | 0, 6 => none
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 1⟩
  | 1, 2 => some ⟨2, Dir.L, some 2⟩
  | 1, 3 => some ⟨4, Dir.R, some 5⟩
  | 1, 4 => some ⟨1, Dir.R, some 1⟩
  | 1, 5 => some ⟨5, Dir.L, some 2⟩
  | 1, 6 => some ⟨3, Dir.L, some 15⟩
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 2⟩
  | 2, 3 => some ⟨3, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 2⟩
  | 2, 5 => some ⟨5, Dir.R, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 3, 0 => some ⟨1, Dir.L, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => none
  | 3, 5 => some ⟨5, Dir.R, some 3⟩
  | 3, 6 => none
  | 4, 0 => some ⟨3, Dir.L, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨4, Dir.L, some 5⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => none
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨6, Dir.L, some 9⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 7⟩
  | 6, 0 => some ⟨0, Dir.R, some 8⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨5, Dir.L, some 13⟩
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 6, 4 => none
  | 6, 5 => none
  | 6, 6 => some ⟨6, Dir.R, some 8⟩
  | 7, 0 => some ⟨2, Dir.L, some 0⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.L, some 7⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨6, Dir.L, some 12⟩
  | 7, 5 => some ⟨5, Dir.L, some 7⟩
  | 7, 6 => some ⟨5, Dir.L, some 0⟩
  | 8, 0 => some ⟨3, Dir.R, some 15⟩
  | 8, 1 => none
  | 8, 2 => some ⟨0, Dir.L, some 0⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 8, 4 => none
  | 8, 5 => some ⟨2, Dir.L, some 18⟩
  | 8, 6 => none
  | 9, 0 => some ⟨2, Dir.R, some 14⟩
  | 9, 1 => some ⟨5, Dir.R, some 14⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => some ⟨2, Dir.R, some 7⟩
  | 9, 5 => some ⟨5, Dir.L, some 9⟩
  | 9, 6 => some ⟨1, Dir.R, some 5⟩
  | 10, 0 => some ⟨2, Dir.L, some 11⟩
  | 10, 1 => none
  | 10, 2 => some ⟨2, Dir.R, some 10⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 10⟩
  | 10, 5 => some ⟨5, Dir.R, some 10⟩
  | 10, 6 => some ⟨6, Dir.R, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 14⟩
  | 11, 1 => some ⟨2, Dir.R, some 14⟩
  | 11, 2 => some ⟨2, Dir.L, some 11⟩
  | 11, 3 => some ⟨3, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 11⟩
  | 11, 5 => some ⟨5, Dir.L, some 11⟩
  | 11, 6 => some ⟨6, Dir.L, some 11⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 1 => some ⟨6, Dir.L, some 14⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.R, some 12⟩
  | 12, 5 => some ⟨5, Dir.R, some 12⟩
  | 12, 6 => some ⟨6, Dir.R, some 12⟩
  | 13, 0 => some ⟨1, Dir.R, some 1⟩
  | 13, 1 => some ⟨1, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 4 => some ⟨1, Dir.L, some 14⟩
  | 13, 5 => some ⟨5, Dir.L, some 13⟩
  | 13, 6 => some ⟨5, Dir.R, some 4⟩
  | 14, 0 => some ⟨1, Dir.R, some 1⟩
  | 14, 1 => some ⟨4, Dir.R, some 15⟩
  | 14, 2 => some ⟨1, Dir.R, some 10⟩
  | 14, 3 => some ⟨0, Dir.R, some 12⟩
  | 14, 4 => some ⟨4, Dir.L, some 13⟩
  | 14, 5 => some ⟨0, Dir.R, some 16⟩
  | 14, 6 => some ⟨6, Dir.L, some 13⟩
  | 15, 0 => some ⟨4, Dir.L, some 9⟩
  | 15, 1 => some ⟨1, Dir.R, some 15⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨3, Dir.R, some 15⟩
  | 15, 4 => some ⟨0, Dir.R, some 15⟩
  | 15, 5 => some ⟨5, Dir.R, some 15⟩
  | 15, 6 => some ⟨6, Dir.R, some 15⟩
  | 16, 0 => some ⟨5, Dir.L, some 17⟩
  | 16, 1 => none
  | 16, 2 => some ⟨2, Dir.R, some 16⟩
  | 16, 3 => some ⟨3, Dir.R, some 16⟩
  | 16, 4 => some ⟨4, Dir.R, some 16⟩
  | 16, 5 => some ⟨5, Dir.R, some 16⟩
  | 16, 6 => some ⟨6, Dir.R, some 16⟩
  | 17, 0 => some ⟨5, Dir.R, some 14⟩
  | 17, 1 => none
  | 17, 2 => some ⟨2, Dir.L, some 17⟩
  | 17, 3 => some ⟨3, Dir.L, some 17⟩
  | 17, 4 => some ⟨4, Dir.L, some 17⟩
  | 17, 5 => some ⟨5, Dir.L, some 17⟩
  | 17, 6 => some ⟨6, Dir.L, some 17⟩
  | 18, 0 => some ⟨1, Dir.R, some 1⟩
  | 18, 1 => some ⟨4, Dir.R, some 19⟩
  | 18, 2 => some ⟨2, Dir.L, some 18⟩
  | 18, 3 => some ⟨3, Dir.L, some 18⟩
  | 18, 4 => some ⟨4, Dir.L, some 18⟩
  | 18, 5 => some ⟨5, Dir.L, some 18⟩
  | 18, 6 => none
  | 19, 0 => some ⟨2, Dir.L, some 18⟩
  | 19, 1 => none
  | 19, 2 => some ⟨2, Dir.R, some 19⟩
  | 19, 3 => some ⟨3, Dir.R, some 19⟩
  | 19, 4 => some ⟨4, Dir.R, some 19⟩
  | 19, 5 => some ⟨5, Dir.R, some 19⟩
  | 19, 6 => none
  | _, _ => none

theorem valid_20_7 : ValidTM 20 7 tm_20_7 := by
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
      | 1 | 6 => trivial
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 4 | 6 => trivial
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => trivial
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 4 | 5 => trivial
      | _ + 7 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 4 | 6 => trivial
      | _ + 7 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => trivial
      | _ + 7 => omega
    | 19 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 6 => trivial
      | _ + 7 => omega
    | _ + 20 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 19 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 20 => rfl

def landmark_20_7 : Config := { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_20_7 : steps tm_20_7 452 initConfig = some landmark_20_7 := by
  have h0 : steps tm_20_7 35 initConfig = some { st := some 9, left := [3, 1], cur := 1, right := [5, 5, 6] } := rfl
  have hstep1 : steps tm_20_7 35 { st := some 9, left := [3, 1], cur := 1, right := [5, 5, 6] } = some { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } := rfl
  have h1 : steps tm_20_7 70 initConfig = some { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } := steps_add tm_20_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_20_7 35 { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } = some { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } := rfl
  have h2 : steps tm_20_7 105 initConfig = some { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } := steps_add tm_20_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_20_7 35 { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } = some { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } := rfl
  have h3 : steps tm_20_7 140 initConfig = some { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } := steps_add tm_20_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_20_7 35 { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } = some { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } := rfl
  have h4 : steps tm_20_7 175 initConfig = some { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } := steps_add tm_20_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_20_7 35 { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } = some { st := some 15, left := [5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6, 5, 5, 5, 5, 5, 5] } := rfl
  have h5 : steps tm_20_7 210 initConfig = some { st := some 15, left := [5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6, 5, 5, 5, 5, 5, 5] } := steps_add tm_20_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_20_7 35 { st := some 15, left := [5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6, 5, 5, 5, 5, 5, 5] } = some { st := some 16, left := [5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6] } := rfl
  have h6 : steps tm_20_7 245 initConfig = some { st := some 16, left := [5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6] } := steps_add tm_20_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_20_7 35 { st := some 16, left := [5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5, 5, 6] } = some { st := some 17, left := [5, 6, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } := rfl
  have h7 : steps tm_20_7 280 initConfig = some { st := some 17, left := [5, 6, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } := steps_add tm_20_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_20_7 35 { st := some 17, left := [5, 6, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [5] } = some { st := some 17, left := [0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [6, 5, 5, 5, 5, 5] } := rfl
  have h8 : steps tm_20_7 315 initConfig = some { st := some 17, left := [0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [6, 5, 5, 5, 5, 5] } := steps_add tm_20_7 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_20_7 35 { st := some 17, left := [0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 3], cur := 5, right := [6, 5, 5, 5, 5, 5] } = some { st := some 2, left := [3], cur := 1, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := rfl
  have h9 : steps tm_20_7 350 initConfig = some { st := some 2, left := [3], cur := 1, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := steps_add tm_20_7 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_20_7 35 { st := some 2, left := [3], cur := 1, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } = some { st := some 18, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 2] } := rfl
  have h10 : steps tm_20_7 385 initConfig = some { st := some 18, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 2] } := steps_add tm_20_7 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_20_7 35 { st := some 18, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 2] } = some { st := some 5, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1], cur := 5, right := [5, 5, 5, 5, 5, 2] } := rfl
  have h11 : steps tm_20_7 420 initConfig = some { st := some 5, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1], cur := 5, right := [5, 5, 5, 5, 5, 2] } := steps_add tm_20_7 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_20_7 32 { st := some 5, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 1], cur := 5, right := [5, 5, 5, 5, 5, 2] } = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h12 : steps tm_20_7 452 initConfig = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_20_7 420 32 initConfig _ _ h11 hstep12
  exact h12

/-! ### 21x7 — fe1_7 @ step 395 -/
def tm_21_7 : TM
  | 0, 0 => some ⟨6, Dir.L, some 5⟩
  | 0, 1 => none
  | 0, 2 => some ⟨0, Dir.R, some 5⟩
  | 0, 3 => some ⟨0, Dir.R, some 3⟩
  | 0, 4 => some ⟨1, Dir.L, some 13⟩
  | 0, 5 => some ⟨6, Dir.R, some 5⟩
  | 0, 6 => none
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 1⟩
  | 1, 2 => some ⟨2, Dir.L, some 2⟩
  | 1, 3 => some ⟨4, Dir.R, some 5⟩
  | 1, 4 => some ⟨1, Dir.R, some 1⟩
  | 1, 5 => some ⟨5, Dir.L, some 2⟩
  | 1, 6 => some ⟨3, Dir.L, some 15⟩
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 2⟩
  | 2, 3 => some ⟨3, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 2⟩
  | 2, 5 => some ⟨5, Dir.R, some 2⟩
  | 2, 6 => some ⟨5, Dir.R, some 2⟩
  | 3, 0 => some ⟨1, Dir.L, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => none
  | 3, 5 => some ⟨5, Dir.R, some 3⟩
  | 3, 6 => none
  | 4, 0 => some ⟨3, Dir.L, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨5, Dir.L, some 20⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => none
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨6, Dir.L, some 9⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => some ⟨5, Dir.L, some 7⟩
  | 6, 0 => some ⟨0, Dir.R, some 8⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => none
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 6, 4 => none
  | 6, 5 => none
  | 6, 6 => some ⟨6, Dir.R, some 8⟩
  | 7, 0 => some ⟨2, Dir.L, some 0⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.L, some 7⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨6, Dir.L, some 12⟩
  | 7, 5 => some ⟨5, Dir.L, some 7⟩
  | 7, 6 => some ⟨5, Dir.L, some 0⟩
  | 8, 0 => some ⟨3, Dir.R, some 15⟩
  | 8, 1 => none
  | 8, 2 => some ⟨0, Dir.L, some 0⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 8, 4 => none
  | 8, 5 => some ⟨2, Dir.L, some 18⟩
  | 8, 6 => none
  | 9, 0 => some ⟨2, Dir.R, some 14⟩
  | 9, 1 => some ⟨5, Dir.R, some 14⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => none
  | 9, 5 => some ⟨5, Dir.L, some 9⟩
  | 9, 6 => some ⟨1, Dir.R, some 5⟩
  | 10, 0 => some ⟨2, Dir.L, some 11⟩
  | 10, 1 => none
  | 10, 2 => some ⟨2, Dir.R, some 10⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 10⟩
  | 10, 5 => some ⟨5, Dir.R, some 10⟩
  | 10, 6 => some ⟨6, Dir.R, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 14⟩
  | 11, 1 => some ⟨2, Dir.R, some 14⟩
  | 11, 2 => some ⟨2, Dir.L, some 11⟩
  | 11, 3 => some ⟨3, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 11⟩
  | 11, 5 => some ⟨5, Dir.L, some 11⟩
  | 11, 6 => some ⟨6, Dir.L, some 11⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 1 => some ⟨6, Dir.L, some 14⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.R, some 12⟩
  | 12, 5 => some ⟨5, Dir.R, some 12⟩
  | 12, 6 => some ⟨6, Dir.R, some 12⟩
  | 13, 0 => some ⟨1, Dir.R, some 1⟩
  | 13, 1 => some ⟨1, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 4 => some ⟨1, Dir.L, some 14⟩
  | 13, 5 => some ⟨5, Dir.L, some 13⟩
  | 13, 6 => some ⟨4, Dir.R, some 4⟩
  | 14, 0 => some ⟨1, Dir.R, some 1⟩
  | 14, 1 => some ⟨4, Dir.R, some 15⟩
  | 14, 2 => some ⟨1, Dir.R, some 10⟩
  | 14, 3 => some ⟨0, Dir.R, some 12⟩
  | 14, 4 => some ⟨4, Dir.L, some 13⟩
  | 14, 5 => some ⟨0, Dir.R, some 16⟩
  | 14, 6 => some ⟨6, Dir.L, some 13⟩
  | 15, 0 => some ⟨4, Dir.L, some 9⟩
  | 15, 1 => some ⟨1, Dir.R, some 15⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨3, Dir.R, some 15⟩
  | 15, 4 => some ⟨0, Dir.R, some 15⟩
  | 15, 5 => some ⟨5, Dir.R, some 15⟩
  | 15, 6 => some ⟨6, Dir.R, some 15⟩
  | 16, 0 => some ⟨5, Dir.L, some 17⟩
  | 16, 1 => none
  | 16, 2 => some ⟨2, Dir.R, some 16⟩
  | 16, 3 => some ⟨3, Dir.R, some 16⟩
  | 16, 4 => some ⟨4, Dir.R, some 16⟩
  | 16, 5 => some ⟨5, Dir.R, some 16⟩
  | 16, 6 => some ⟨6, Dir.R, some 16⟩
  | 17, 0 => some ⟨5, Dir.R, some 14⟩
  | 17, 1 => none
  | 17, 2 => some ⟨2, Dir.L, some 17⟩
  | 17, 3 => some ⟨3, Dir.L, some 17⟩
  | 17, 4 => some ⟨4, Dir.L, some 17⟩
  | 17, 5 => some ⟨5, Dir.L, some 17⟩
  | 17, 6 => some ⟨6, Dir.L, some 17⟩
  | 18, 0 => some ⟨1, Dir.R, some 1⟩
  | 18, 1 => some ⟨4, Dir.R, some 19⟩
  | 18, 2 => some ⟨2, Dir.L, some 18⟩
  | 18, 3 => some ⟨3, Dir.L, some 18⟩
  | 18, 4 => some ⟨4, Dir.L, some 18⟩
  | 18, 5 => some ⟨5, Dir.L, some 18⟩
  | 18, 6 => none
  | 19, 0 => some ⟨2, Dir.L, some 18⟩
  | 19, 1 => none
  | 19, 2 => some ⟨2, Dir.R, some 19⟩
  | 19, 3 => some ⟨3, Dir.R, some 19⟩
  | 19, 4 => some ⟨4, Dir.R, some 19⟩
  | 19, 5 => some ⟨5, Dir.R, some 19⟩
  | 19, 6 => none
  | 20, 0 => none
  | 20, 1 => none
  | 20, 2 => none
  | 20, 3 => some ⟨4, Dir.R, some 0⟩
  | 20, 4 => some ⟨6, Dir.R, some 7⟩
  | 20, 5 => none
  | 20, 6 => none
  | _, _ => none

theorem valid_21_7 : ValidTM 21 7 tm_21_7 := by
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
      | 1 | 6 => trivial
      | _ + 7 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 4 | 6 => trivial
      | _ + 7 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => trivial
      | _ + 7 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 2 | 4 | 5 => trivial
      | _ + 7 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 4 | 6 => trivial
      | _ + 7 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 4 => trivial
      | _ + 7 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | _ + 7 => omega
    | 16 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 17 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 1 => trivial
      | _ + 7 => omega
    | 18 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => trivial
      | _ + 7 => omega
    | 19 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 1 | 6 => trivial
      | _ + 7 => omega
    | 20 =>
      match sym with
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 0 | 1 | 2 | 5 | 6 => trivial
      | _ + 7 => omega
    | _ + 21 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 16 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 17 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 18 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 19 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | 20 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    | _ + 21 => rfl

def landmark_21_7 : Config := { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_21_7 : steps tm_21_7 395 initConfig = some landmark_21_7 := by
  have h0 : steps tm_21_7 35 initConfig = some { st := some 9, left := [3, 1], cur := 1, right := [5, 5, 6] } := rfl
  have hstep1 : steps tm_21_7 35 { st := some 9, left := [3, 1], cur := 1, right := [5, 5, 6] } = some { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } := rfl
  have h1 : steps tm_21_7 70 initConfig = some { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } := steps_add tm_21_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_21_7 35 { st := some 15, left := [6, 4], cur := 6, right := [5, 5, 5, 5, 5, 5] } = some { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } := rfl
  have h2 : steps tm_21_7 105 initConfig = some { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } := steps_add tm_21_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_21_7 35 { st := some 16, left := [5, 5, 5, 5, 5, 0, 5, 6, 4], cur := 6, right := [] } = some { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } := rfl
  have h3 : steps tm_21_7 140 initConfig = some { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } := steps_add tm_21_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_21_7 35 { st := some 17, left := [5, 5, 0, 5, 5, 5, 6, 4], cur := 5, right := [6, 5, 5, 5] } = some { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } := rfl
  have h4 : steps tm_21_7 175 initConfig = some { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } := steps_add tm_21_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_21_7 35 { st := some 16, left := [0, 5, 5, 5, 5, 5, 5, 6, 4], cur := 6, right := [5, 5, 5, 5, 5] } = some { st := some 15, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := rfl
  have h5 : steps tm_21_7 210 initConfig = some { st := some 15, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := steps_add tm_21_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_21_7 35 { st := some 15, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } = some { st := some 9, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 1, right := [5, 5, 5, 5, 5, 5, 6] } := rfl
  have h6 : steps tm_21_7 245 initConfig = some { st := some 9, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 1, right := [5, 5, 5, 5, 5, 5, 6] } := steps_add tm_21_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_21_7 35 { st := some 9, left := [5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 1, right := [5, 5, 5, 5, 5, 5, 6] } = some { st := some 16, left := [5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 6, right := [5, 5] } := rfl
  have h7 : steps tm_21_7 280 initConfig = some { st := some 16, left := [5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 6, right := [5, 5] } := steps_add tm_21_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_21_7 35 { st := some 16, left := [5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 6, right := [5, 5] } = some { st := some 17, left := [5, 5, 6, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 5, right := [5, 5] } := rfl
  have h8 : steps tm_21_7 315 initConfig = some { st := some 17, left := [5, 5, 6, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 5, right := [5, 5] } := steps_add tm_21_7 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_21_7 35 { st := some 17, left := [5, 5, 6, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 3], cur := 5, right := [5, 5] } = some { st := some 13, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := rfl
  have h9 : steps tm_21_7 350 initConfig = some { st := some 13, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } := steps_add tm_21_7 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_21_7 35 { st := some 13, left := [5, 5, 6, 3], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5] } = some { st := some 7, left := [5, 5, 5, 5, 5, 6, 4], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h10 : steps tm_21_7 385 initConfig = some { st := some 7, left := [5, 5, 5, 5, 5, 6, 4], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_21_7 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_21_7 10 { st := some 7, left := [5, 5, 5, 5, 5, 6, 4], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := rfl
  have h11 : steps tm_21_7 395 initConfig = some { st := some 1, left := [1, 1], cur := 5, right := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] } := steps_add tm_21_7 385 10 initConfig _ _ h10 hstep11
  exact h11

end BB.Landmarks2026_11_23.S7
