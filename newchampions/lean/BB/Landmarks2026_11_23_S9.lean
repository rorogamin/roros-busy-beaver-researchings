/-
  BB/Landmarks2026_11_23_S9.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs
  for 8 9-symbol landmark machines (2026-11-23 sweep).
-/
import BB.TM

namespace BB.Landmarks2026_11_23.S9
open BB

/-! ### 4x9 — fw2_7 @ step 561 -/
def tm_4_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨5, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨4, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.L, some 0⟩
  | 0, 7 => some ⟨5, Dir.L, some 2⟩
  | 0, 8 => some ⟨7, Dir.R, some 3⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 1⟩
  | 1, 5 => some ⟨4, Dir.L, some 2⟩
  | 1, 6 => some ⟨6, Dir.L, some 2⟩
  | 1, 7 => some ⟨0, Dir.R, some 3⟩
  | 1, 8 => some ⟨1, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨7, Dir.R, some 0⟩
  | 2, 6 => some ⟨6, Dir.L, some 2⟩
  | 2, 7 => some ⟨0, Dir.R, some 3⟩
  | 2, 8 => some ⟨8, Dir.R, some 0⟩
  | 3, 0 => some ⟨1, Dir.R, some 0⟩
  | 3, 1 => some ⟨1, Dir.L, some 3⟩
  | 3, 2 => some ⟨0, Dir.L, some 3⟩
  | 3, 3 => some ⟨4, Dir.R, some 0⟩
  | 3, 4 => some ⟨5, Dir.R, some 0⟩
  | 3, 5 => some ⟨6, Dir.R, some 0⟩
  | 3, 6 => some ⟨7, Dir.L, some 2⟩
  | 3, 7 => some ⟨8, Dir.L, some 2⟩
  | 3, 8 => some ⟨6, Dir.L, some 0⟩
  | _, _ => none

theorem valid_4_9 : ValidTM 4 9 tm_4_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 4 => rfl

def landmark_4_9 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 5, 6] }
theorem reaches_landmark_4_9 : steps tm_4_9 561 initConfig = some landmark_4_9 := by
  have h0 : steps tm_4_9 35 initConfig = some { st := some 2, left := [], cur := 3, right := [7] } := rfl
  have hstep1 : steps tm_4_9 35 { st := some 2, left := [], cur := 3, right := [7] } = some { st := some 0, left := [1, 7, 2, 2, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_4_9 70 initConfig = some { st := some 0, left := [1, 7, 2, 2, 3], cur := 0, right := [] } := steps_add tm_4_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_9 35 { st := some 0, left := [1, 7, 2, 2, 3], cur := 0, right := [] } = some { st := some 0, left := [2, 3], cur := 1, right := [1, 3, 1, 7] } := rfl
  have h2 : steps tm_4_9 105 initConfig = some { st := some 0, left := [2, 3], cur := 1, right := [1, 3, 1, 7] } := steps_add tm_4_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_9 35 { st := some 0, left := [2, 3], cur := 1, right := [1, 3, 1, 7] } = some { st := some 2, left := [3, 3, 3], cur := 3, right := [3, 1, 1, 3, 7] } := rfl
  have h3 : steps tm_4_9 140 initConfig = some { st := some 2, left := [3, 3, 3], cur := 3, right := [3, 1, 1, 3, 7] } := steps_add tm_4_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_9 35 { st := some 2, left := [3, 3, 3], cur := 3, right := [3, 1, 1, 3, 7] } = some { st := some 1, left := [3, 3], cur := 2, right := [1, 3, 1, 1, 1, 1, 3, 7] } := rfl
  have h4 : steps tm_4_9 175 initConfig = some { st := some 1, left := [3, 3], cur := 2, right := [1, 3, 1, 1, 1, 1, 3, 7] } := steps_add tm_4_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_9 35 { st := some 1, left := [3, 3], cur := 2, right := [1, 3, 1, 1, 1, 1, 3, 7] } = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 3, 1, 1, 1, 3, 7] } := rfl
  have h5 : steps tm_4_9 210 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 3, 1, 1, 1, 3, 7] } := steps_add tm_4_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_9 35 { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 3, 1, 1, 1, 3, 7] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 7] } := rfl
  have h6 : steps tm_4_9 245 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 7] } := steps_add tm_4_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 3, 7] } = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 3, 7] } := rfl
  have h7 : steps tm_4_9 280 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 3, 7] } := steps_add tm_4_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_4_9 35 { st := some 1, left := [3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 3, 7] } = some { st := some 1, left := [3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7] } := rfl
  have h8 : steps tm_4_9 315 initConfig = some { st := some 1, left := [3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7] } := steps_add tm_4_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_4_9 35 { st := some 1, left := [3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 8] } := rfl
  have h9 : steps tm_4_9 350 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 8] } := steps_add tm_4_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_4_9 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 8] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5, 5, 5, 6] } := rfl
  have h10 : steps tm_4_9 385 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5, 5, 5, 6] } := steps_add tm_4_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_4_9 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 4, 5, 5, 5, 6] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 4, 5, 5, 5, 6] } := rfl
  have h11 : steps tm_4_9 420 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 4, 5, 5, 5, 6] } := steps_add tm_4_9 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_4_9 35 { st := some 2, left := [2, 2, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 4, 5, 5, 5, 6] } = some { st := some 2, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5, 5, 5, 6] } := rfl
  have h12 : steps tm_4_9 455 initConfig = some { st := some 2, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5, 5, 5, 6] } := steps_add tm_4_9 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_4_9 35 { st := some 2, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 4, 5, 5, 5, 6] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [4, 5, 5, 5, 6] } := rfl
  have h13 : steps tm_4_9 490 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [4, 5, 5, 5, 6] } := steps_add tm_4_9 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_4_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [4, 5, 5, 5, 6] } = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5, 5, 5, 6] } := rfl
  have h14 : steps tm_4_9 525 initConfig = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5, 5, 5, 6] } := steps_add tm_4_9 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_4_9 35 { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 1, 4, 5, 5, 5, 6] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [1, 1, 4, 5, 5, 5, 6] } := rfl
  have h15 : steps tm_4_9 560 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [1, 1, 4, 5, 5, 5, 6] } := steps_add tm_4_9 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_4_9 1 { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [1, 1, 4, 5, 5, 5, 6] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 5, 6] } := rfl
  have h16 : steps tm_4_9 561 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 4, 5, 5, 5, 6] } := steps_add tm_4_9 560 1 initConfig _ _ h15 hstep16
  exact h16

/-! ### 5x9 — fwm21_8_fix @ step 838 -/
def tm_5_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 1⟩
  | 0, 8 => some ⟨8, Dir.R, some 3⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨0, Dir.R, some 3⟩
  | 1, 5 => some ⟨1, Dir.R, some 1⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 1, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 8 => some ⟨6, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.R, some 1⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 2, 8 => some ⟨6, Dir.L, some 4⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.L, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨8, Dir.L, some 1⟩
  | 3, 8 => some ⟨7, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | 4, 8 => some ⟨7, Dir.L, some 3⟩
  | _, _ => none

theorem valid_5_9 : ValidTM 5 9 tm_5_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 5 => rfl

def landmark_5_9 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 1, 7, 2] }
theorem reaches_landmark_5_9 : steps tm_5_9 838 initConfig = some landmark_5_9 := by
  have h0 : steps tm_5_9 35 initConfig = some { st := some 3, left := [5, 5], cur := 7, right := [] } := rfl
  have hstep1 : steps tm_5_9 35 { st := some 3, left := [5, 5], cur := 7, right := [] } = some { st := some 2, left := [2], cur := 4, right := [0, 3, 7, 2] } := rfl
  have h1 : steps tm_5_9 70 initConfig = some { st := some 2, left := [2], cur := 4, right := [0, 3, 7, 2] } := steps_add tm_5_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_9 35 { st := some 2, left := [2], cur := 4, right := [0, 3, 7, 2] } = some { st := some 1, left := [3, 6], cur := 0, right := [6, 1, 3, 7, 2] } := rfl
  have h2 : steps tm_5_9 105 initConfig = some { st := some 1, left := [3, 6], cur := 0, right := [6, 1, 3, 7, 2] } := steps_add tm_5_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_9 35 { st := some 1, left := [3, 6], cur := 0, right := [6, 1, 3, 7, 2] } = some { st := some 3, left := [6], cur := 5, right := [6, 4, 5, 8, 1, 1, 7, 2] } := rfl
  have h3 : steps tm_5_9 140 initConfig = some { st := some 3, left := [6], cur := 5, right := [6, 4, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_9 35 { st := some 3, left := [6], cur := 5, right := [6, 4, 5, 8, 1, 1, 7, 2] } = some { st := some 3, left := [6], cur := 6, right := [4, 4, 6, 6, 4, 5, 8, 1, 1, 7, 2] } := rfl
  have h4 : steps tm_5_9 175 initConfig = some { st := some 3, left := [6], cur := 6, right := [4, 4, 6, 6, 4, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_9 35 { st := some 3, left := [6], cur := 6, right := [4, 4, 6, 6, 4, 5, 8, 1, 1, 7, 2] } = some { st := some 3, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h5 : steps tm_5_9 210 initConfig = some { st := some 3, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_9 35 { st := some 3, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [6, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h6 : steps tm_5_9 245 initConfig = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [6, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_9 35 { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [6, 4, 4, 4, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 6, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h7 : steps tm_5_9 280 initConfig = some { st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 6, 4, 4, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_5_9 35 { st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 6, 4, 4, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h8 : steps tm_5_9 315 initConfig = some { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_5_9 35 { st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h9 : steps tm_5_9 350 initConfig = some { st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_5_9 35 { st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 4, left := [6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } := rfl
  have h10 : steps tm_5_9 385 initConfig = some { st := some 4, left := [6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } := steps_add tm_5_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_5_9 35 { st := some 4, left := [6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 6, 5, 8, 1, 1, 7, 2] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 8, 1, 1, 7, 2] } := rfl
  have h11 : steps tm_5_9 420 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 8, 1, 1, 7, 2] } := steps_add tm_5_9 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_5_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 8, 1, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } := rfl
  have h12 : steps tm_5_9 455 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } := steps_add tm_5_9 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := rfl
  have h13 : steps tm_5_9 490 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_5_9 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := rfl
  have h14 : steps tm_5_9 525 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_5_9 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } := rfl
  have h15 : steps tm_5_9 560 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := rfl
  have h16 : steps tm_5_9 595 initConfig = some { st := some 2, left := [3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_5_9 35 { st := some 2, left := [3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := rfl
  have h17 : steps tm_5_9 630 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } := rfl
  have h18 : steps tm_5_9 665 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } := steps_add tm_5_9 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], cur := 3, right := [7, 2, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } := rfl
  have h19 : steps tm_5_9 700 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 7, 2, 1, 7, 2] } = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 7, 2, 1, 7, 2] } := rfl
  have h20 : steps tm_5_9 735 initConfig = some { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 7, 2, 1, 7, 2] } := steps_add tm_5_9 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_5_9 35 { st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 7, 2, 1, 7, 2] } = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [1, 7, 2, 1, 7, 2] } := rfl
  have h21 : steps tm_5_9 770 initConfig = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [1, 7, 2, 1, 7, 2] } := steps_add tm_5_9 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_5_9 35 { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [1, 7, 2, 1, 7, 2] } = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 7, 2, 1, 7, 2] } := rfl
  have h22 : steps tm_5_9 805 initConfig = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 7, 2, 1, 7, 2] } := steps_add tm_5_9 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_5_9 33 { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 7, 2, 1, 7, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 1, 7, 2] } := rfl
  have h23 : steps tm_5_9 838 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2, 1, 7, 2] } := steps_add tm_5_9 805 33 initConfig _ _ h22 hstep23
  exact h23

/-! ### 6x9 — fwm21_8_blank @ step 182 -/
def tm_6_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨0, Dir.L, some 5⟩
  | 0, 5 => some ⟨0, Dir.L, some 3⟩
  | 0, 6 => some ⟨0, Dir.L, some 5⟩
  | 0, 7 => some ⟨3, Dir.L, some 2⟩
  | 0, 8 => some ⟨7, Dir.R, some 5⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨2, Dir.R, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 0⟩
  | 1, 8 => some ⟨8, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 3⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 2, 8 => some ⟨8, Dir.R, some 5⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨7, Dir.R, some 3⟩
  | 3, 8 => some ⟨8, Dir.L, some 2⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 5⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | 4, 8 => some ⟨8, Dir.L, some 1⟩
  | 5, 0 => some ⟨1, Dir.L, some 3⟩
  | 5, 1 => some ⟨2, Dir.L, some 3⟩
  | 5, 2 => some ⟨3, Dir.R, some 3⟩
  | 5, 3 => some ⟨4, Dir.L, some 2⟩
  | 5, 4 => some ⟨7, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.R, some 0⟩
  | 5, 6 => some ⟨1, Dir.L, some 5⟩
  | 5, 7 => some ⟨8, Dir.L, some 0⟩
  | 5, 8 => some ⟨7, Dir.L, some 2⟩
  | _, _ => none

theorem valid_6_9 : ValidTM 6 9 tm_6_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 6 => rfl

def landmark_6_9 : Config := { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 7] }
theorem reaches_landmark_6_9 : steps tm_6_9 182 initConfig = some landmark_6_9 := by
  have h0 : steps tm_6_9 35 initConfig = some { st := some 5, left := [5], cur := 5, right := [] } := rfl
  have hstep1 : steps tm_6_9 35 { st := some 5, left := [5], cur := 5, right := [] } = some { st := some 4, left := [6, 7, 2, 3], cur := 0, right := [] } := rfl
  have h1 : steps tm_6_9 70 initConfig = some { st := some 4, left := [6, 7, 2, 3], cur := 0, right := [] } := steps_add tm_6_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_9 35 { st := some 4, left := [6, 7, 2, 3], cur := 0, right := [] } = some { st := some 2, left := [2, 2, 3], cur := 2, right := [8, 2] } := rfl
  have h2 : steps tm_6_9 105 initConfig = some { st := some 2, left := [2, 2, 3], cur := 2, right := [8, 2] } := steps_add tm_6_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_9 35 { st := some 2, left := [2, 2, 3], cur := 2, right := [8, 2] } = some { st := some 2, left := [2], cur := 3, right := [3, 3, 3, 8, 7] } := rfl
  have h3 : steps tm_6_9 140 initConfig = some { st := some 2, left := [2], cur := 3, right := [3, 3, 3, 8, 7] } := steps_add tm_6_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_6_9 35 { st := some 2, left := [2], cur := 3, right := [3, 3, 3, 8, 7] } = some { st := some 2, left := [2], cur := 2, right := [3, 3, 1, 1, 7, 7] } := rfl
  have h4 : steps tm_6_9 175 initConfig = some { st := some 2, left := [2], cur := 2, right := [3, 3, 1, 1, 7, 7] } := steps_add tm_6_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_6_9 7 { st := some 2, left := [2], cur := 2, right := [3, 3, 1, 1, 7, 7] } = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 7] } := rfl
  have h5 : steps tm_6_9 182 initConfig = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 7, 7] } := steps_add tm_6_9 175 7 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x9 — fwm21_8 @ step 198 -/
def tm_7_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 1⟩
  | 0, 8 => some ⟨8, Dir.L, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨1, Dir.L, some 0⟩
  | 1, 5 => some ⟨0, Dir.L, some 5⟩
  | 1, 6 => some ⟨2, Dir.R, some 3⟩
  | 1, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 8 => some ⟨3, Dir.R, some 4⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 1⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 2, 8 => some ⟨8, Dir.L, some 5⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 6⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨7, Dir.L, some 5⟩
  | 3, 8 => some ⟨8, Dir.R, some 5⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨2, Dir.L, some 6⟩
  | 4, 8 => some ⟨8, Dir.L, some 0⟩
  | 5, 0 => some ⟨1, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨2, Dir.R, some 6⟩
  | 5, 4 => some ⟨4, Dir.R, some 5⟩
  | 5, 5 => some ⟨0, Dir.L, some 6⟩
  | 5, 6 => some ⟨0, Dir.L, some 3⟩
  | 5, 7 => some ⟨7, Dir.L, some 6⟩
  | 5, 8 => some ⟨8, Dir.L, some 6⟩
  | 6, 0 => some ⟨1, Dir.R, some 3⟩
  | 6, 1 => some ⟨2, Dir.L, some 3⟩
  | 6, 2 => some ⟨3, Dir.R, some 3⟩
  | 6, 3 => some ⟨4, Dir.L, some 2⟩
  | 6, 4 => some ⟨6, Dir.L, some 2⟩
  | 6, 5 => some ⟨4, Dir.R, some 3⟩
  | 6, 6 => some ⟨1, Dir.L, some 3⟩
  | 6, 7 => some ⟨8, Dir.L, some 1⟩
  | 6, 8 => some ⟨8, Dir.R, some 2⟩
  | _, _ => none

theorem valid_7_9 : ValidTM 7 9 tm_7_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 7 => rfl

def landmark_7_9 : Config := { st := some 0, left := [2, 2, 3], cur := 1, right := [7, 2] }
theorem reaches_landmark_7_9 : steps tm_7_9 198 initConfig = some landmark_7_9 := by
  have h0 : steps tm_7_9 35 initConfig = some { st := some 0, left := [3], cur := 6, right := [] } := rfl
  have hstep1 : steps tm_7_9 35 { st := some 0, left := [3], cur := 6, right := [] } = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := rfl
  have h1 : steps tm_7_9 70 initConfig = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := steps_add tm_7_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_9 35 { st := some 4, left := [6], cur := 5, right := [4, 4] } = some { st := some 2, left := [], cur := 0, right := [6] } := rfl
  have h2 : steps tm_7_9 105 initConfig = some { st := some 2, left := [], cur := 0, right := [6] } := steps_add tm_7_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_9 35 { st := some 2, left := [], cur := 0, right := [6] } = some { st := some 3, left := [4, 6], cur := 2, right := [] } := rfl
  have h3 : steps tm_7_9 140 initConfig = some { st := some 3, left := [4, 6], cur := 2, right := [] } := steps_add tm_7_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_9 35 { st := some 3, left := [4, 6], cur := 2, right := [] } = some { st := some 5, left := [2, 8, 3, 2, 3], cur := 1, right := [] } := rfl
  have h4 : steps tm_7_9 175 initConfig = some { st := some 5, left := [2, 8, 3, 2, 3], cur := 1, right := [] } := steps_add tm_7_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_9 23 { st := some 5, left := [2, 8, 3, 2, 3], cur := 1, right := [] } = some { st := some 0, left := [2, 2, 3], cur := 1, right := [7, 2] } := rfl
  have h5 : steps tm_7_9 198 initConfig = some { st := some 0, left := [2, 2, 3], cur := 1, right := [7, 2] } := steps_add tm_7_9 175 23 initConfig _ _ h4 hstep5
  exact h5

/-! ### 7x9 — fwm21_8_fix @ step 377 -/
def tm_7_9_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 1⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨6, Dir.L, some 4⟩
  | 0, 5 => some ⟨3, Dir.L, some 2⟩
  | 0, 6 => some ⟨5, Dir.R, some 0⟩
  | 0, 7 => some ⟨7, Dir.L, some 1⟩
  | 0, 8 => some ⟨8, Dir.L, some 2⟩
  | 1, 0 => some ⟨0, Dir.L, some 3⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨1, Dir.L, some 0⟩
  | 1, 5 => some ⟨0, Dir.L, some 5⟩
  | 1, 6 => some ⟨2, Dir.R, some 3⟩
  | 1, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 8 => some ⟨2, Dir.L, some 2⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨7, Dir.L, some 5⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 2, 8 => some ⟨8, Dir.L, some 5⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 6⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨7, Dir.L, some 5⟩
  | 3, 8 => some ⟨8, Dir.R, some 3⟩
  | 4, 0 => some ⟨0, Dir.L, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 1⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 0⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | 4, 8 => some ⟨8, Dir.L, some 0⟩
  | 5, 0 => some ⟨1, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨2, Dir.R, some 6⟩
  | 5, 4 => some ⟨4, Dir.R, some 5⟩
  | 5, 5 => some ⟨0, Dir.L, some 6⟩
  | 5, 6 => some ⟨0, Dir.L, some 3⟩
  | 5, 7 => some ⟨7, Dir.L, some 6⟩
  | 5, 8 => some ⟨8, Dir.L, some 6⟩
  | 6, 0 => some ⟨1, Dir.R, some 3⟩
  | 6, 1 => some ⟨2, Dir.L, some 3⟩
  | 6, 2 => some ⟨3, Dir.R, some 3⟩
  | 6, 3 => some ⟨4, Dir.L, some 2⟩
  | 6, 4 => some ⟨6, Dir.L, some 2⟩
  | 6, 5 => some ⟨4, Dir.R, some 3⟩
  | 6, 6 => some ⟨1, Dir.L, some 3⟩
  | 6, 7 => some ⟨8, Dir.L, some 1⟩
  | 6, 8 => some ⟨7, Dir.R, some 1⟩
  | _, _ => none

theorem valid_7_9_1 : ValidTM 7 9 tm_7_9_1 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 7 => rfl

def landmark_7_9_1 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2] }
theorem reaches_landmark_7_9_1 : steps tm_7_9_1 377 initConfig = some landmark_7_9_1 := by
  have h0 : steps tm_7_9_1 35 initConfig = some { st := some 0, left := [3], cur := 6, right := [] } := rfl
  have hstep1 : steps tm_7_9_1 35 { st := some 0, left := [3], cur := 6, right := [] } = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := rfl
  have h1 : steps tm_7_9_1 70 initConfig = some { st := some 4, left := [6], cur := 5, right := [4, 4] } := steps_add tm_7_9_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_9_1 35 { st := some 4, left := [6], cur := 5, right := [4, 4] } = some { st := some 2, left := [], cur := 0, right := [6] } := rfl
  have h2 : steps tm_7_9_1 105 initConfig = some { st := some 2, left := [], cur := 0, right := [6] } := steps_add tm_7_9_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_9_1 35 { st := some 2, left := [], cur := 0, right := [6] } = some { st := some 6, left := [2], cur := 7, right := [] } := rfl
  have h3 : steps tm_7_9_1 140 initConfig = some { st := some 6, left := [2], cur := 7, right := [] } := steps_add tm_7_9_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_9_1 35 { st := some 6, left := [2], cur := 7, right := [] } = some { st := some 6, left := [2, 2], cur := 7, right := [8] } := rfl
  have h4 : steps tm_7_9_1 175 initConfig = some { st := some 6, left := [2, 2], cur := 7, right := [8] } := steps_add tm_7_9_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_9_1 35 { st := some 6, left := [2, 2], cur := 7, right := [8] } = some { st := some 3, left := [5, 6, 6], cur := 4, right := [6, 5, 8, 8] } := rfl
  have h5 : steps tm_7_9_1 210 initConfig = some { st := some 3, left := [5, 6, 6], cur := 4, right := [6, 5, 8, 8] } := steps_add tm_7_9_1 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_9_1 35 { st := some 3, left := [5, 6, 6], cur := 4, right := [6, 5, 8, 8] } = some { st := some 5, left := [2, 2, 3, 3, 3, 3, 3, 3], cur := 8, right := [8] } := rfl
  have h6 : steps tm_7_9_1 245 initConfig = some { st := some 5, left := [2, 2, 3, 3, 3, 3, 3, 3], cur := 8, right := [8] } := steps_add tm_7_9_1 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_9_1 35 { st := some 5, left := [2, 2, 3, 3, 3, 3, 3, 3], cur := 8, right := [8] } = some { st := some 2, left := [2, 2, 3, 3, 3], cur := 3, right := [3, 3, 7, 2] } := rfl
  have h7 : steps tm_7_9_1 280 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3], cur := 3, right := [3, 3, 7, 2] } := steps_add tm_7_9_1 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_9_1 35 { st := some 2, left := [2, 2, 3, 3, 3], cur := 3, right := [3, 3, 7, 2] } = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 7, 2] } := rfl
  have h8 : steps tm_7_9_1 315 initConfig = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 7, 2] } := steps_add tm_7_9_1 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_7_9_1 35 { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 7, 2] } = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 1, 7, 2] } := rfl
  have h9 : steps tm_7_9_1 350 initConfig = some { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 1, 7, 2] } := steps_add tm_7_9_1 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_7_9_1 27 { st := some 2, left := [2, 3], cur := 2, right := [3, 3, 3, 3, 3, 1, 7, 2] } = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2] } := rfl
  have h10 : steps tm_7_9_1 377 initConfig = some { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1, 7, 2] } := steps_add tm_7_9_1 350 27 initConfig _ _ h9 hstep10
  exact h10

/-! ### 9x9 — fwpw_8_blank @ step 1529 -/
def tm_9_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨0, Dir.L, some 0⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨1, Dir.L, some 3⟩
  | 0, 6 => some ⟨0, Dir.L, some 4⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨8, Dir.L, some 4⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => some ⟨4, Dir.R, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 2, 8 => some ⟨0, Dir.L, some 8⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨0, Dir.L, some 5⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 3, 8 => some ⟨6, Dir.R, some 7⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨0, Dir.L, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨4, Dir.R, some 0⟩
  | 4, 5 => some ⟨0, Dir.L, some 4⟩
  | 4, 6 => some ⟨2, Dir.R, some 5⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 4, 8 => some ⟨8, Dir.L, some 2⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 5, 8 => some ⟨8, Dir.L, some 8⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨8, Dir.L, some 0⟩
  | 6, 5 => some ⟨0, Dir.L, some 7⟩
  | 6, 6 => some ⟨0, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 0⟩
  | 6, 8 => some ⟨8, Dir.R, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨0, Dir.L, some 8⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨0, Dir.L, some 8⟩
  | 7, 6 => some ⟨2, Dir.L, some 5⟩
  | 7, 7 => some ⟨0, Dir.L, some 8⟩
  | 7, 8 => some ⟨4, Dir.L, some 1⟩
  | 8, 0 => some ⟨1, Dir.L, some 0⟩
  | 8, 1 => some ⟨8, Dir.L, some 5⟩
  | 8, 2 => some ⟨1, Dir.R, some 2⟩
  | 8, 3 => some ⟨1, Dir.L, some 2⟩
  | 8, 4 => some ⟨1, Dir.R, some 6⟩
  | 8, 5 => some ⟨0, Dir.L, some 4⟩
  | 8, 6 => some ⟨4, Dir.L, some 4⟩
  | 8, 7 => some ⟨2, Dir.L, some 5⟩
  | 8, 8 => some ⟨7, Dir.L, some 8⟩
  | _, _ => none

theorem valid_9_9 : ValidTM 9 9 tm_9_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 9 => rfl

def landmark_9_9 : Config := { st := some 7, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] }
theorem reaches_landmark_9_9 : steps tm_9_9 1529 initConfig = some landmark_9_9 := by
  have h0 : steps tm_9_9 35 initConfig = some { st := some 4, left := [7], cur := 2, right := [1] } := rfl
  have hstep1 : steps tm_9_9 35 { st := some 4, left := [7], cur := 2, right := [1] } = some { st := some 1, left := [], cur := 0, right := [1, 2] } := rfl
  have h1 : steps tm_9_9 70 initConfig = some { st := some 1, left := [], cur := 0, right := [1, 2] } := steps_add tm_9_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_9_9 35 { st := some 1, left := [], cur := 0, right := [1, 2] } = some { st := some 5, left := [2], cur := 3, right := [] } := rfl
  have h2 : steps tm_9_9 105 initConfig = some { st := some 5, left := [2], cur := 3, right := [] } := steps_add tm_9_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_9_9 35 { st := some 5, left := [2], cur := 3, right := [] } = some { st := some 3, left := [], cur := 7, right := [1, 1, 1, 1] } := rfl
  have h3 : steps tm_9_9 140 initConfig = some { st := some 3, left := [], cur := 7, right := [1, 1, 1, 1] } := steps_add tm_9_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_9_9 35 { st := some 3, left := [], cur := 7, right := [1, 1, 1, 1] } = some { st := some 0, left := [5, 7], cur := 8, right := [] } := rfl
  have h4 : steps tm_9_9 175 initConfig = some { st := some 0, left := [5, 7], cur := 8, right := [] } := steps_add tm_9_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_9_9 35 { st := some 0, left := [5, 7], cur := 8, right := [] } = some { st := some 1, left := [], cur := 0, right := [7, 7, 1, 8] } := rfl
  have h5 : steps tm_9_9 210 initConfig = some { st := some 1, left := [], cur := 0, right := [7, 7, 1, 8] } := steps_add tm_9_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_9_9 35 { st := some 1, left := [], cur := 0, right := [7, 7, 1, 8] } = some { st := some 4, left := [7], cur := 3, right := [8, 8] } := rfl
  have h6 : steps tm_9_9 245 initConfig = some { st := some 4, left := [7], cur := 3, right := [8, 8] } := steps_add tm_9_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_9_9 35 { st := some 4, left := [7], cur := 3, right := [8, 8] } = some { st := some 4, left := [7, 7], cur := 3, right := [4, 1, 8] } := rfl
  have h7 : steps tm_9_9 280 initConfig = some { st := some 4, left := [7, 7], cur := 3, right := [4, 1, 8] } := steps_add tm_9_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_9_9 35 { st := some 4, left := [7, 7], cur := 3, right := [4, 1, 8] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 8] } := rfl
  have h8 : steps tm_9_9 315 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 8] } := steps_add tm_9_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_9_9 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 8] } = some { st := some 4, left := [7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 3, 8] } := rfl
  have h9 : steps tm_9_9 350 initConfig = some { st := some 4, left := [7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 3, 8] } := steps_add tm_9_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_9_9 35 { st := some 4, left := [7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 3, 8] } = some { st := some 8, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [7, 8] } := rfl
  have h10 : steps tm_9_9 385 initConfig = some { st := some 8, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [7, 8] } := steps_add tm_9_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_9_9 35 { st := some 8, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [7, 8] } = some { st := some 0, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [8, 0, 8] } := rfl
  have h11 : steps tm_9_9 420 initConfig = some { st := some 0, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [8, 0, 8] } := steps_add tm_9_9 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_9_9 35 { st := some 0, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 3, right := [8, 0, 8] } = some { st := some 1, left := [7, 7, 7, 7, 7], cur := 4, right := [4, 1, 2, 3, 3, 8] } := rfl
  have h12 : steps tm_9_9 455 initConfig = some { st := some 1, left := [7, 7, 7, 7, 7], cur := 4, right := [4, 1, 2, 3, 3, 8] } := steps_add tm_9_9 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_9_9 35 { st := some 1, left := [7, 7, 7, 7, 7], cur := 4, right := [4, 1, 2, 3, 3, 8] } = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 1, 2, 3, 3, 8] } := rfl
  have h13 : steps tm_9_9 490 initConfig = some { st := some 6, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 1, 2, 3, 3, 8] } := steps_add tm_9_9 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_9_9 35 { st := some 6, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 1, 2, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 3, 8] } := rfl
  have h14 : steps tm_9_9 525 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 3, 8] } := steps_add tm_9_9 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 1, 2, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8] } := rfl
  have h15 : steps tm_9_9 560 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8] } := steps_add tm_9_9 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8] } = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } := rfl
  have h16 : steps tm_9_9 595 initConfig = some { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } := steps_add tm_9_9 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_9_9 35 { st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } := rfl
  have h17 : steps tm_9_9 630 initConfig = some { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } := steps_add tm_9_9 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_9_9 35 { st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8] } = some { st := some 5, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h18 : steps tm_9_9 665 initConfig = some { st := some 5, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_9_9 35 { st := some 5, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 5, left := [7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h19 : steps tm_9_9 700 initConfig = some { st := some 5, left := [7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_9_9 35 { st := some 5, left := [7, 7], cur := 7, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h20 : steps tm_9_9 735 initConfig = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_9_9 35 { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h21 : steps tm_9_9 770 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h22 : steps tm_9_9 805 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h23 : steps tm_9_9 840 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h24 : steps tm_9_9 875 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h25 : steps tm_9_9 910 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h26 : steps tm_9_9 945 initConfig = some { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h27 : steps tm_9_9 980 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h28 : steps tm_9_9 1015 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } := rfl
  have h29 : steps tm_9_9 1050 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3, 3, 8] } := rfl
  have h30 : steps tm_9_9 1085 initConfig = some { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3, 3, 8] } := steps_add tm_9_9 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_9_9 35 { st := some 6, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 3, 3, 8] } := rfl
  have h31 : steps tm_9_9 1120 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 3, 3, 8] } := steps_add tm_9_9 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 8] } := rfl
  have h32 : steps tm_9_9 1155 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 8] } := steps_add tm_9_9 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 8] } = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } := rfl
  have h33 : steps tm_9_9 1190 initConfig = some { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } := steps_add tm_9_9 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_9_9 35 { st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } := rfl
  have h34 : steps tm_9_9 1225 initConfig = some { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } := steps_add tm_9_9 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_9_9 35 { st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 8] } = some { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 4] } := rfl
  have h35 : steps tm_9_9 1260 initConfig = some { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 4] } := steps_add tm_9_9 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_9_9 35 { st := some 1, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 4] } = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 4] } := rfl
  have h36 : steps tm_9_9 1295 initConfig = some { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_9_9 35 { st := some 2, left := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h37 : steps tm_9_9 1330 initConfig = some { st := some 2, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_9_9 35 { st := some 2, left := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h38 : steps tm_9_9 1365 initConfig = some { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_9_9 35 { st := some 2, left := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h39 : steps tm_9_9 1400 initConfig = some { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_9_9 35 { st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h40 : steps tm_9_9 1435 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_9_9 35 { st := some 2, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h41 : steps tm_9_9 1470 initConfig = some { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_9_9 35 { st := some 2, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h42 : steps tm_9_9 1505 initConfig = some { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_9_9 24 { st := some 2, left := [2, 3, 3], cur := 2, right := [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } = some { st := some 7, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := rfl
  have h43 : steps tm_9_9 1529 initConfig = some { st := some 7, left := [2, 2, 2, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4] } := steps_add tm_9_9 1505 24 initConfig _ _ h42 hstep43
  exact h43

/-! ### 16x9 — fwpw6_9 @ step 406 -/
def tm_16_9 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨0, Dir.L, some 4⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨1, Dir.R, some 1⟩
  | 0, 6 => some ⟨6, Dir.R, some 15⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨6, Dir.L, some 2⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => some ⟨0, Dir.L, some 9⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 2, 8 => some ⟨5, Dir.L, some 11⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.L, some 12⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 3, 8 => some ⟨0, Dir.R, some 13⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 4⟩
  | 4, 5 => some ⟨0, Dir.L, some 14⟩
  | 4, 6 => some ⟨4, Dir.L, some 10⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 4, 8 => some ⟨4, Dir.R, some 14⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 5, 8 => some ⟨0, Dir.L, some 9⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨6, Dir.L, some 0⟩
  | 6, 5 => some ⟨0, Dir.L, some 8⟩
  | 6, 6 => some ⟨0, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 0⟩
  | 6, 8 => some ⟨8, Dir.R, some 3⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨6, Dir.L, some 11⟩
  | 7, 8 => some ⟨2, Dir.R, some 13⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨2, Dir.L, some 0⟩
  | 8, 5 => some ⟨0, Dir.L, some 9⟩
  | 8, 6 => some ⟨1, Dir.L, some 12⟩
  | 8, 7 => some ⟨0, Dir.L, some 15⟩
  | 8, 8 => some ⟨8, Dir.R, some 3⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨6, Dir.L, some 3⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨8, Dir.R, some 0⟩
  | 9, 5 => some ⟨0, Dir.L, some 10⟩
  | 9, 6 => some ⟨1, Dir.L, some 14⟩
  | 9, 7 => some ⟨1, Dir.L, some 10⟩
  | 9, 8 => some ⟨8, Dir.L, some 12⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨0, Dir.L, some 13⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨2, Dir.L, some 13⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨0, Dir.L, some 11⟩
  | 10, 7 => some ⟨2, Dir.L, some 0⟩
  | 10, 8 => some ⟨8, Dir.R, some 11⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨1, Dir.L, some 0⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨3, Dir.L, some 13⟩
  | 11, 5 => some ⟨7, Dir.L, some 9⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨2, Dir.L, some 5⟩
  | 11, 8 => some ⟨1, Dir.R, some 15⟩
  | 12, 0 => some ⟨3, Dir.R, some 12⟩
  | 12, 1 => some ⟨1, Dir.L, some 13⟩
  | 12, 2 => some ⟨7, Dir.L, some 12⟩
  | 12, 3 => some ⟨7, Dir.L, some 12⟩
  | 12, 4 => some ⟨1, Dir.R, some 5⟩
  | 12, 5 => some ⟨0, Dir.R, some 3⟩
  | 12, 6 => some ⟨0, Dir.L, some 0⟩
  | 12, 7 => some ⟨2, Dir.R, some 7⟩
  | 12, 8 => some ⟨5, Dir.R, some 10⟩
  | 13, 0 => some ⟨1, Dir.R, none⟩
  | 13, 1 => some ⟨8, Dir.R, some 2⟩
  | 13, 2 => some ⟨5, Dir.R, some 14⟩
  | 13, 3 => some ⟨1, Dir.L, some 11⟩
  | 13, 4 => some ⟨3, Dir.R, some 9⟩
  | 13, 5 => some ⟨8, Dir.R, some 10⟩
  | 13, 6 => some ⟨8, Dir.L, some 0⟩
  | 13, 7 => some ⟨8, Dir.L, some 14⟩
  | 13, 8 => some ⟨7, Dir.L, some 12⟩
  | 14, 0 => some ⟨3, Dir.R, some 14⟩
  | 14, 1 => some ⟨1, Dir.L, some 15⟩
  | 14, 2 => some ⟨8, Dir.L, some 14⟩
  | 14, 3 => some ⟨8, Dir.L, some 14⟩
  | 14, 4 => some ⟨0, Dir.R, some 2⟩
  | 14, 5 => some ⟨0, Dir.L, some 15⟩
  | 14, 6 => some ⟨4, Dir.L, some 11⟩
  | 14, 7 => some ⟨2, Dir.L, some 15⟩
  | 14, 8 => some ⟨2, Dir.R, some 7⟩
  | 15, 0 => some ⟨1, Dir.L, some 0⟩
  | 15, 1 => some ⟨4, Dir.R, some 0⟩
  | 15, 2 => some ⟨4, Dir.L, some 0⟩
  | 15, 3 => some ⟨1, Dir.L, some 5⟩
  | 15, 4 => some ⟨5, Dir.L, some 0⟩
  | 15, 5 => some ⟨8, Dir.L, some 8⟩
  | 15, 6 => some ⟨0, Dir.L, some 13⟩
  | 15, 7 => some ⟨4, Dir.L, some 8⟩
  | 15, 8 => some ⟨2, Dir.L, some 0⟩
  | _, _ => none

theorem valid_16_9 : ValidTM 16 9 tm_16_9 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 16 => rfl

def landmark_16_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 6, 6, 8, 7] }
theorem reaches_landmark_16_9 : steps tm_16_9 406 initConfig = some landmark_16_9 := by
  have h0 : steps tm_16_9 35 initConfig = some { st := some 11, left := [3], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_16_9 35 { st := some 11, left := [3], cur := 1, right := [] } = some { st := some 4, left := [3], cur := 7, right := [] } := rfl
  have h1 : steps tm_16_9 70 initConfig = some { st := some 4, left := [3], cur := 7, right := [] } := steps_add tm_16_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_9 35 { st := some 4, left := [3], cur := 7, right := [] } = some { st := some 1, left := [], cur := 0, right := [1, 2] } := rfl
  have h2 : steps tm_16_9 105 initConfig = some { st := some 1, left := [], cur := 0, right := [1, 2] } := steps_add tm_16_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_9 35 { st := some 1, left := [], cur := 0, right := [1, 2] } = some { st := some 4, left := [6], cur := 5, right := [] } := rfl
  have h3 : steps tm_16_9 140 initConfig = some { st := some 4, left := [6], cur := 5, right := [] } := steps_add tm_16_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_9 35 { st := some 4, left := [6], cur := 5, right := [] } = some { st := some 5, left := [3, 7], cur := 3, right := [] } := rfl
  have h4 : steps tm_16_9 175 initConfig = some { st := some 5, left := [3, 7], cur := 3, right := [] } := steps_add tm_16_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_9 35 { st := some 5, left := [3, 7], cur := 3, right := [] } = some { st := some 0, left := [], cur := 7, right := [8] } := rfl
  have h5 : steps tm_16_9 210 initConfig = some { st := some 0, left := [], cur := 7, right := [8] } := steps_add tm_16_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_16_9 35 { st := some 0, left := [], cur := 7, right := [8] } = some { st := some 0, left := [7], cur := 6, right := [5] } := rfl
  have h6 : steps tm_16_9 245 initConfig = some { st := some 0, left := [7], cur := 6, right := [5] } := steps_add tm_16_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_16_9 35 { st := some 0, left := [7], cur := 6, right := [5] } = some { st := some 4, left := [3], cur := 7, right := [0, 1, 2, 7] } := rfl
  have h7 : steps tm_16_9 280 initConfig = some { st := some 4, left := [3], cur := 7, right := [0, 1, 2, 7] } := steps_add tm_16_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_16_9 35 { st := some 4, left := [3], cur := 7, right := [0, 1, 2, 7] } = some { st := some 9, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 3] } := rfl
  have h8 : steps tm_16_9 315 initConfig = some { st := some 9, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 3] } := steps_add tm_16_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_16_9 35 { st := some 9, left := [3, 7, 7, 7], cur := 0, right := [0, 0, 3] } = some { st := some 0, left := [5, 6, 5, 7, 7, 7], cur := 3, right := [1, 1] } := rfl
  have h9 : steps tm_16_9 350 initConfig = some { st := some 0, left := [5, 6, 5, 7, 7, 7], cur := 3, right := [1, 1] } := steps_add tm_16_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_16_9 35 { st := some 0, left := [5, 6, 5, 7, 7, 7], cur := 3, right := [1, 1] } = some { st := some 3, left := [8, 3, 7, 7, 7], cur := 1, right := [] } := rfl
  have h10 : steps tm_16_9 385 initConfig = some { st := some 3, left := [8, 3, 7, 7, 7], cur := 1, right := [] } := steps_add tm_16_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_16_9 21 { st := some 3, left := [8, 3, 7, 7, 7], cur := 1, right := [] } = some { st := some 8, left := [2, 3], cur := 1, right := [4, 6, 6, 8, 7] } := rfl
  have h11 : steps tm_16_9 406 initConfig = some { st := some 8, left := [2, 3], cur := 1, right := [4, 6, 6, 8, 7] } := steps_add tm_16_9 385 21 initConfig _ _ h10 hstep11
  exact h11

/-! ### 16x9 — fwpw7_9 @ step 194 -/
def tm_16_9_1 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨0, Dir.L, some 4⟩
  | 0, 6 => some ⟨0, Dir.R, some 13⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨0, Dir.L, some 9⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => none
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 2, 8 => none
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 14⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 3, 8 => none
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 4⟩
  | 4, 5 => some ⟨1, Dir.R, some 5⟩
  | 4, 6 => some ⟨0, Dir.L, some 9⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 4, 8 => none
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 5, 8 => none
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.R, some 3⟩
  | 6, 5 => some ⟨0, Dir.L, some 8⟩
  | 6, 6 => some ⟨0, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 0⟩
  | 6, 8 => none
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨6, Dir.L, some 11⟩
  | 7, 8 => some ⟨2, Dir.R, some 13⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨0, Dir.R, some 9⟩
  | 8, 5 => some ⟨0, Dir.L, some 0⟩
  | 8, 6 => some ⟨1, Dir.L, some 2⟩
  | 8, 7 => some ⟨1, Dir.L, some 0⟩
  | 8, 8 => none
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨1, Dir.L, some 14⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 10⟩
  | 9, 5 => none
  | 9, 6 => none
  | 9, 7 => some ⟨1, Dir.L, some 10⟩
  | 9, 8 => none
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨0, Dir.L, some 13⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨6, Dir.L, some 14⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => none
  | 10, 7 => none
  | 10, 8 => none
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨1, Dir.L, some 15⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨0, Dir.R, some 13⟩
  | 11, 5 => none
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => none
  | 11, 8 => none
  | 12, 0 => some ⟨3, Dir.R, some 12⟩
  | 12, 1 => some ⟨4, Dir.L, some 8⟩
  | 12, 2 => some ⟨7, Dir.L, some 12⟩
  | 12, 3 => some ⟨7, Dir.L, some 12⟩
  | 12, 4 => none
  | 12, 5 => none
  | 12, 6 => none
  | 12, 7 => some ⟨2, Dir.R, some 7⟩
  | 12, 8 => none
  | 13, 0 => some ⟨1, Dir.R, none⟩
  | 13, 1 => some ⟨4, Dir.L, some 10⟩
  | 13, 2 => some ⟨1, Dir.L, some 12⟩
  | 13, 3 => some ⟨1, Dir.L, some 11⟩
  | 13, 4 => none
  | 13, 5 => none
  | 13, 6 => some ⟨7, Dir.L, some 15⟩
  | 13, 7 => some ⟨8, Dir.L, some 14⟩
  | 13, 8 => some ⟨7, Dir.L, some 12⟩
  | 14, 0 => some ⟨3, Dir.R, some 14⟩
  | 14, 1 => some ⟨4, Dir.R, some 0⟩
  | 14, 2 => some ⟨8, Dir.L, some 14⟩
  | 14, 3 => some ⟨8, Dir.L, some 14⟩
  | 14, 4 => none
  | 14, 5 => none
  | 14, 6 => none
  | 14, 7 => some ⟨2, Dir.R, some 15⟩
  | 14, 8 => some ⟨2, Dir.R, some 7⟩
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 1 => some ⟨0, Dir.L, some 0⟩
  | 15, 2 => some ⟨7, Dir.L, some 15⟩
  | 15, 3 => some ⟨7, Dir.L, some 15⟩
  | 15, 4 => none
  | 15, 5 => none
  | 15, 6 => none
  | 15, 7 => some ⟨2, Dir.R, some 13⟩
  | 15, 8 => none
  | _, _ => none

theorem valid_16_9_1 : ValidTM 16 9 tm_16_9_1 := by
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
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
      | 8 => exact ⟨by decide, by decide⟩
      | _ + 9 => omega
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
      | 8 => trivial
      | _ + 9 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 5 | 6 | 8 => trivial
      | _ + 9 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 5 => exact ⟨by decide, by decide⟩
      | 6 | 7 | 8 => trivial
      | _ + 9 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 4 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 5 | 7 | 8 => trivial
      | _ + 9 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 | 5 | 6 | 8 => trivial
      | _ + 9 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 6 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 8 => exact ⟨by decide, by decide⟩
      | 4 | 5 => trivial
      | _ + 9 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 8 => exact ⟨by decide, by decide⟩
      | 4 | 5 | 6 => trivial
      | _ + 9 => omega
    | 15 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | 3 => exact ⟨by decide, by decide⟩
      | 7 => exact ⟨by decide, by decide⟩
      | 4 | 5 | 6 | 8 => trivial
      | _ + 9 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | 15 =>
      match sym with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
      | _ + 9 => rfl
    | _ + 16 => rfl

def landmark_16_9_1 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 8, 6] }
theorem reaches_landmark_16_9_1 : steps tm_16_9_1 194 initConfig = some landmark_16_9_1 := by
  have h0 : steps tm_16_9_1 35 initConfig = some { st := some 5, left := [6], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_16_9_1 35 { st := some 5, left := [6], cur := 0, right := [] } = some { st := some 2, left := [2, 7], cur := 1, right := [1] } := rfl
  have h1 : steps tm_16_9_1 70 initConfig = some { st := some 2, left := [2, 7], cur := 1, right := [1] } := steps_add tm_16_9_1 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_9_1 35 { st := some 2, left := [2, 7], cur := 1, right := [1] } = some { st := some 2, left := [0, 0, 2, 3], cur := 0, right := [] } := rfl
  have h2 : steps tm_16_9_1 105 initConfig = some { st := some 2, left := [0, 0, 2, 3], cur := 0, right := [] } := steps_add tm_16_9_1 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_9_1 35 { st := some 2, left := [0, 0, 2, 3], cur := 0, right := [] } = some { st := some 0, left := [6, 7, 5, 3, 2, 3], cur := 0, right := [] } := rfl
  have h3 : steps tm_16_9_1 140 initConfig = some { st := some 0, left := [6, 7, 5, 3, 2, 3], cur := 0, right := [] } := steps_add tm_16_9_1 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_9_1 35 { st := some 0, left := [6, 7, 5, 3, 2, 3], cur := 0, right := [] } = some { st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 8, 6] } := rfl
  have h4 : steps tm_16_9_1 175 initConfig = some { st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 8, 6] } := steps_add tm_16_9_1 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_9_1 19 { st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 8, 6] } = some { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 8, 6] } := rfl
  have h5 : steps tm_16_9_1 194 initConfig = some { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 8, 6] } := steps_add tm_16_9_1 175 19 initConfig _ _ h4 hstep5
  exact h5

end BB.Landmarks2026_11_23.S9
