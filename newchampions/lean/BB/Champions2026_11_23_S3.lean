/-
  BB/Champions2026_11_23_S3.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 7 3-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_23.S3
open BB

/-! ### BB(7,3) — > f_{ω+1}(3) (`fw1_3` @ step 752) -/
def tm_7_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 6⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.L, some 5⟩
  | 3, 2 => some ⟨0, Dir.R, some 6⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 5, 0 => some ⟨2, Dir.R, some 6⟩
  | 5, 1 => some ⟨0, Dir.L, some 0⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | _, _ => none

theorem valid_7_3 : ValidTM 7 3 tm_7_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, trivial⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 7 => rfl

def landmark_7_3 : Config := { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2] }
theorem reaches_landmark_7_3 : steps tm_7_3 752 initConfig = some landmark_7_3 := by
  have h0 : steps tm_7_3 35 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 2, 1, 1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_7_3 35 { st := some 3, left := [], cur := 0, right := [1, 2, 1, 1, 1, 1, 2] } = some { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 2, 1, 2] } := rfl
  have h1 : steps tm_7_3 70 initConfig = some { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 2, 1, 2] } := steps_add tm_7_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_3 35 { st := some 6, left := [1, 1, 1, 1], cur := 1, right := [1, 2, 1, 2] } = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2] } := rfl
  have h2 : steps tm_7_3 105 initConfig = some { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2] } := steps_add tm_7_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_3 35 { st := some 4, left := [1, 1, 1, 1], cur := 2, right := [1, 1, 1, 2, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1] } := rfl
  have h3 : steps tm_7_3 140 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1] } := steps_add tm_7_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_3 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1] } = some { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } := rfl
  have h4 : steps tm_7_3 175 initConfig = some { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } := steps_add tm_7_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_7_3 35 { st := some 0, left := [2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] } = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1] } := rfl
  have h5 : steps tm_7_3 210 initConfig = some { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1] } := steps_add tm_7_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_7_3 35 { st := some 2, left := [1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1, 1, 1, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1] } := rfl
  have h6 : steps tm_7_3 245 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1] } := steps_add tm_7_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_7_3 35 { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1] } := rfl
  have h7 : steps tm_7_3 280 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1] } := steps_add tm_7_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_7_3 35 { st := some 6, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2, 1, 1, 1, 1, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1] } := rfl
  have h8 : steps tm_7_3 315 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1] } := steps_add tm_7_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_7_3 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 2, 1, 1, 1, 1, 1] } = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1] } := rfl
  have h9 : steps tm_7_3 350 initConfig = some { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1] } := steps_add tm_7_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_7_3 35 { st := some 6, left := [], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1] } := rfl
  have h10 : steps tm_7_3 385 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1] } := steps_add tm_7_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_7_3 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 2, 1, 1, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1] } := rfl
  have h11 : steps tm_7_3 420 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1] } := steps_add tm_7_3 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_7_3 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1] } := rfl
  have h12 : steps tm_7_3 455 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1] } := steps_add tm_7_3 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_7_3 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1] } := rfl
  have h13 : steps tm_7_3 490 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1] } := steps_add tm_7_3 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_7_3 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 2, 1, 1] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } := rfl
  have h14 : steps tm_7_3 525 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } := steps_add tm_7_3 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_7_3 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } := rfl
  have h15 : steps tm_7_3 560 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } := steps_add tm_7_3 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_7_3 35 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1] } = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2] } := rfl
  have h16 : steps tm_7_3 595 initConfig = some { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2] } := steps_add tm_7_3 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_7_3 35 { st := some 4, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 2] } = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } := rfl
  have h17 : steps tm_7_3 630 initConfig = some { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } := steps_add tm_7_3 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_7_3 35 { st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] } = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] } := rfl
  have h18 : steps tm_7_3 665 initConfig = some { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] } := steps_add tm_7_3 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_7_3 35 { st := some 0, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] } = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] } := rfl
  have h19 : steps tm_7_3 700 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] } := steps_add tm_7_3 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_7_3 35 { st := some 6, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] } = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } := rfl
  have h20 : steps tm_7_3 735 initConfig = some { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } := steps_add tm_7_3 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_7_3 17 { st := some 2, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2] } := rfl
  have h21 : steps tm_7_3 752 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 2] } := steps_add tm_7_3 735 17 initConfig _ _ h20 hstep21
  exact h21

/-! ### BB(10,3) — > f_{ω}(14) (`fw_3` @ step 313) -/
def tm_10_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 7⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨1, Dir.R, some 9⟩
  | 7, 0 => some ⟨1, Dir.R, some 6⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.R, some 9⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨0, Dir.L, some 9⟩
  | 8, 2 => some ⟨1, Dir.L, some 7⟩
  | 9, 0 => some ⟨1, Dir.R, some 8⟩
  | 9, 1 => some ⟨2, Dir.L, some 5⟩
  | 9, 2 => some ⟨1, Dir.R, some 8⟩
  | _, _ => none

theorem valid_10_3 : ValidTM 10 3 tm_10_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 10 => rfl

def landmark_10_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 1, 0, 0, 2] }
theorem reaches_landmark_10_3 : steps tm_10_3 313 initConfig = some landmark_10_3 := by
  have h0 : steps tm_10_3 35 initConfig = some { st := some 9, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_10_3 35 { st := some 9, left := [], cur := 1, right := [] } = some { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 2] } := rfl
  have h1 : steps tm_10_3 70 initConfig = some { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 2] } := steps_add tm_10_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_10_3 35 { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 2, 2] } := rfl
  have h2 : steps tm_10_3 105 initConfig = some { st := some 0, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 2, 2] } := steps_add tm_10_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_10_3 35 { st := some 0, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 2, 2] } = some { st := some 5, left := [1, 1, 2, 1, 1, 1, 1, 1, 1], cur := 2, right := [2] } := rfl
  have h3 : steps tm_10_3 140 initConfig = some { st := some 5, left := [1, 1, 2, 1, 1, 1, 1, 1, 1], cur := 2, right := [2] } := steps_add tm_10_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_10_3 35 { st := some 5, left := [1, 1, 2, 1, 1, 1, 1, 1, 1], cur := 2, right := [2] } = some { st := some 6, left := [1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h4 : steps tm_10_3 175 initConfig = some { st := some 6, left := [1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_10_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_10_3 35 { st := some 6, left := [1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 5, left := [], cur := 0, right := [2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h5 : steps tm_10_3 210 initConfig = some { st := some 5, left := [], cur := 0, right := [2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_10_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_10_3 35 { st := some 5, left := [], cur := 0, right := [2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 8, left := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 1, 0, 0, 2] } := rfl
  have h6 : steps tm_10_3 245 initConfig = some { st := some 8, left := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 1, 0, 0, 2] } := steps_add tm_10_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_10_3 35 { st := some 8, left := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 1, 0, 0, 2] } = some { st := some 8, left := [1], cur := 1, right := [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2] } := rfl
  have h7 : steps tm_10_3 280 initConfig = some { st := some 8, left := [1], cur := 1, right := [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2] } := steps_add tm_10_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_10_3 33 { st := some 8, left := [1], cur := 1, right := [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 1, 0, 0, 2] } := rfl
  have h8 : steps tm_10_3 313 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 1, 0, 0, 2] } := steps_add tm_10_3 280 33 initConfig _ _ h7 hstep8
  exact h8

/-! ### BB(11,3) — > f_{ω}(18) (`fw_3` @ step 1003) -/
def tm_11_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 7⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨0, Dir.R, some 10⟩
  | 7, 0 => some ⟨1, Dir.R, some 6⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 10⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨0, Dir.L, some 9⟩
  | 8, 2 => some ⟨0, Dir.R, some 0⟩
  | 9, 0 => some ⟨1, Dir.R, some 8⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨1, Dir.L, some 5⟩
  | 10, 0 => some ⟨1, Dir.R, some 9⟩
  | 10, 1 => some ⟨2, Dir.L, some 5⟩
  | 10, 2 => some ⟨0, Dir.R, some 8⟩
  | _, _ => none

theorem valid_11_3 : ValidTM 11 3 tm_11_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 11 => rfl

def landmark_11_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2] }
theorem reaches_landmark_11_3 : steps tm_11_3 1003 initConfig = some landmark_11_3 := by
  have h0 : steps tm_11_3 35 initConfig = some { st := some 9, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_11_3 35 { st := some 9, left := [], cur := 1, right := [] } = some { st := some 5, left := [1, 1], cur := 0, right := [2] } := rfl
  have h1 : steps tm_11_3 70 initConfig = some { st := some 5, left := [1, 1], cur := 0, right := [2] } := steps_add tm_11_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_11_3 35 { st := some 5, left := [1, 1], cur := 0, right := [2] } = some { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 0, 2] } := rfl
  have h2 : steps tm_11_3 105 initConfig = some { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 0, 2] } := steps_add tm_11_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_11_3 35 { st := some 5, left := [1], cur := 0, right := [2, 0, 0, 0, 2] } = some { st := some 6, left := [1, 1, 1, 1], cur := 0, right := [0, 2, 2, 2] } := rfl
  have h3 : steps tm_11_3 140 initConfig = some { st := some 6, left := [1, 1, 1, 1], cur := 0, right := [0, 2, 2, 2] } := steps_add tm_11_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_11_3 35 { st := some 6, left := [1, 1, 1, 1], cur := 0, right := [0, 2, 2, 2] } = some { st := some 8, left := [1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 2] } := rfl
  have h4 : steps tm_11_3 175 initConfig = some { st := some 8, left := [1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 2] } := steps_add tm_11_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_11_3 35 { st := some 8, left := [1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 2] } = some { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h5 : steps tm_11_3 210 initConfig = some { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_11_3 35 { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 10, left := [1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h6 : steps tm_11_3 245 initConfig = some { st := some 10, left := [1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_11_3 35 { st := some 10, left := [1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 9, left := [1, 0, 1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } := rfl
  have h7 : steps tm_11_3 280 initConfig = some { st := some 9, left := [1, 0, 1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_11_3 35 { st := some 9, left := [1, 0, 1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } = some { st := some 10, left := [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } := rfl
  have h8 : steps tm_11_3 315 initConfig = some { st := some 10, left := [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } := steps_add tm_11_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_11_3 35 { st := some 10, left := [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } = some { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := rfl
  have h9 : steps tm_11_3 350 initConfig = some { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := steps_add tm_11_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_11_3 35 { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } = some { st := some 9, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := rfl
  have h10 : steps tm_11_3 385 initConfig = some { st := some 9, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := steps_add tm_11_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_11_3 35 { st := some 9, left := [1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } = some { st := some 9, left := [1, 0, 1, 1, 1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h11 : steps tm_11_3 420 initConfig = some { st := some 9, left := [1, 0, 1, 1, 1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_11_3 35 { st := some 9, left := [1, 0, 1, 1, 1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 10, left := [1, 1, 0, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h12 : steps tm_11_3 455 initConfig = some { st := some 10, left := [1, 1, 0, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_11_3 35 { st := some 10, left := [1, 1, 0, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h13 : steps tm_11_3 490 initConfig = some { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_11_3 35 { st := some 6, left := [1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 7, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h14 : steps tm_11_3 525 initConfig = some { st := some 7, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_11_3 35 { st := some 7, left := [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 2, 0, 0, 0, 2] } := rfl
  have h15 : steps tm_11_3 560 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_11_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [2, 2, 0, 0, 0, 2] } = some { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h16 : steps tm_11_3 595 initConfig = some { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_11_3 35 { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 8, left := [1, 1], cur := 0, right := [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h17 : steps tm_11_3 630 initConfig = some { st := some 8, left := [1, 1], cur := 0, right := [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_11_3 35 { st := some 8, left := [1, 1], cur := 0, right := [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 9, left := [0, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h18 : steps tm_11_3 665 initConfig = some { st := some 9, left := [0, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_11_3 35 { st := some 9, left := [0, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 0, left := [1], cur := 2, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h19 : steps tm_11_3 700 initConfig = some { st := some 0, left := [1], cur := 2, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_11_3 35 { st := some 0, left := [1], cur := 2, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 10, left := [0, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h20 : steps tm_11_3 735 initConfig = some { st := some 10, left := [0, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_11_3 35 { st := some 10, left := [0, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 5, left := [0, 0, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h21 : steps tm_11_3 770 initConfig = some { st := some 5, left := [0, 0, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_11_3 35 { st := some 5, left := [0, 0, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 0, left := [2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h22 : steps tm_11_3 805 initConfig = some { st := some 0, left := [2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_11_3 35 { st := some 0, left := [2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h23 : steps tm_11_3 840 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_11_3 35 { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 9, left := [0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := rfl
  have h24 : steps tm_11_3 875 initConfig = some { st := some 9, left := [0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } := steps_add tm_11_3 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_11_3 35 { st := some 9, left := [0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2] } = some { st := some 5, left := [1, 0, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2] } := rfl
  have h25 : steps tm_11_3 910 initConfig = some { st := some 5, left := [1, 0, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2] } := steps_add tm_11_3 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_11_3 35 { st := some 5, left := [1, 0, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2] } = some { st := some 6, left := [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h26 : steps tm_11_3 945 initConfig = some { st := some 6, left := [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_11_3 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_11_3 35 { st := some 6, left := [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := rfl
  have h27 : steps tm_11_3 980 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := steps_add tm_11_3 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_11_3 23 { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h28 : steps tm_11_3 1003 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_11_3 980 23 initConfig _ _ h27 hstep28
  exact h28

/-! ### BB(12,3) — > f_{ω}(12) (`fw_3` @ step 418) -/
def tm_12_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 7⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨0, Dir.R, some 11⟩
  | 7, 0 => some ⟨1, Dir.R, some 6⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨0, Dir.L, some 9⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 9, 0 => some ⟨1, Dir.R, some 8⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨0, Dir.L, some 11⟩
  | 10, 0 => some ⟨1, Dir.R, some 9⟩
  | 10, 1 => some ⟨0, Dir.L, some 11⟩
  | 10, 2 => some ⟨2, Dir.L, some 7⟩
  | 11, 0 => some ⟨1, Dir.R, some 10⟩
  | 11, 1 => some ⟨2, Dir.L, some 5⟩
  | 11, 2 => some ⟨1, Dir.L, some 5⟩
  | _, _ => none

theorem valid_12_3 : ValidTM 12 3 tm_12_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 12 => rfl

def landmark_12_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2] }
theorem reaches_landmark_12_3 : steps tm_12_3 418 initConfig = some landmark_12_3 := by
  have h0 : steps tm_12_3 35 initConfig = some { st := some 9, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_12_3 35 { st := some 9, left := [], cur := 1, right := [] } = some { st := some 7, left := [1], cur := 0, right := [2] } := rfl
  have h1 : steps tm_12_3 70 initConfig = some { st := some 7, left := [1], cur := 0, right := [2] } := steps_add tm_12_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_3 35 { st := some 7, left := [1], cur := 0, right := [2] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h2 : steps tm_12_3 105 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_12_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 5, left := [1, 1], cur := 0, right := [2, 0, 0, 0, 2] } := rfl
  have h3 : steps tm_12_3 140 initConfig = some { st := some 5, left := [1, 1], cur := 0, right := [2, 0, 0, 0, 2] } := steps_add tm_12_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_12_3 35 { st := some 5, left := [1, 1], cur := 0, right := [2, 0, 0, 0, 2] } = some { st := some 7, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2] } := rfl
  have h4 : steps tm_12_3 175 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2] } := steps_add tm_12_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_12_3 35 { st := some 7, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [2] } = some { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 2] } := rfl
  have h5 : steps tm_12_3 210 initConfig = some { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 2] } := steps_add tm_12_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_12_3 35 { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 2] } := rfl
  have h6 : steps tm_12_3 245 initConfig = some { st := some 9, left := [1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 2] } := steps_add tm_12_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_12_3 35 { st := some 9, left := [1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 2] } = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } := rfl
  have h7 : steps tm_12_3 280 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } := steps_add tm_12_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_12_3 35 { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2] } = some { st := some 6, left := [1], cur := 0, right := [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h8 : steps tm_12_3 315 initConfig = some { st := some 6, left := [1], cur := 0, right := [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_12_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_12_3 35 { st := some 6, left := [1], cur := 0, right := [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 7, left := [], cur := 1, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h9 : steps tm_12_3 350 initConfig = some { st := some 7, left := [], cur := 1, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_12_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_12_3 35 { st := some 7, left := [], cur := 1, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 9, left := [2, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h10 : steps tm_12_3 385 initConfig = some { st := some 9, left := [2, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_12_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_12_3 33 { st := some 9, left := [2, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2] } := rfl
  have h11 : steps tm_12_3 418 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2] } := steps_add tm_12_3 385 33 initConfig _ _ h10 hstep11
  exact h11

/-! ### BB(13,3) — > f_{ω}(14) (`fw_3` @ step 626) -/
def tm_13_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 7⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨0, Dir.R, some 12⟩
  | 7, 0 => some ⟨1, Dir.R, some 6⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨0, Dir.L, some 9⟩
  | 8, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 0 => some ⟨1, Dir.R, some 8⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨2, Dir.R, some 7⟩
  | 10, 0 => some ⟨1, Dir.R, some 9⟩
  | 10, 1 => some ⟨0, Dir.L, some 11⟩
  | 10, 2 => some ⟨2, Dir.R, some 12⟩
  | 11, 0 => some ⟨1, Dir.R, some 10⟩
  | 11, 1 => some ⟨0, Dir.L, some 12⟩
  | 11, 2 => some ⟨0, Dir.L, some 9⟩
  | 12, 0 => some ⟨1, Dir.R, some 11⟩
  | 12, 1 => some ⟨2, Dir.L, some 5⟩
  | 12, 2 => some ⟨1, Dir.L, some 8⟩
  | _, _ => none

theorem valid_13_3 : ValidTM 13 3 tm_13_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 13 => rfl

def landmark_13_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] }
theorem reaches_landmark_13_3 : steps tm_13_3 626 initConfig = some landmark_13_3 := by
  have h0 : steps tm_13_3 35 initConfig = some { st := some 9, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_13_3 35 { st := some 9, left := [], cur := 1, right := [] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h1 : steps tm_13_3 70 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_13_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_13_3 35 { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 12, left := [0, 1, 1], cur := 1, right := [] } := rfl
  have h2 : steps tm_13_3 105 initConfig = some { st := some 12, left := [0, 1, 1], cur := 1, right := [] } := steps_add tm_13_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_13_3 35 { st := some 12, left := [0, 1, 1], cur := 1, right := [] } = some { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2] } := rfl
  have h3 : steps tm_13_3 140 initConfig = some { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2] } := steps_add tm_13_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_13_3 35 { st := some 8, left := [1, 1, 1], cur := 1, right := [0, 2] } = some { st := some 10, left := [1, 1, 1], cur := 1, right := [0, 0, 0, 2] } := rfl
  have h4 : steps tm_13_3 175 initConfig = some { st := some 10, left := [1, 1, 1], cur := 1, right := [0, 0, 0, 2] } := steps_add tm_13_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_13_3 35 { st := some 10, left := [1, 1, 1], cur := 1, right := [0, 0, 0, 2] } = some { st := some 10, left := [1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h5 : steps tm_13_3 210 initConfig = some { st := some 10, left := [1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_13_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_13_3 35 { st := some 10, left := [1], cur := 0, right := [0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1, 1, 0, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } := rfl
  have h6 : steps tm_13_3 245 initConfig = some { st := some 9, left := [1, 1, 1, 0, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } := steps_add tm_13_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_13_3 35 { st := some 9, left := [1, 1, 1, 0, 1, 1], cur := 0, right := [0, 2, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2] } := rfl
  have h7 : steps tm_13_3 280 initConfig = some { st := some 9, left := [1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2] } := steps_add tm_13_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_13_3 35 { st := some 9, left := [1, 1], cur := 1, right := [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2] } = some { st := some 8, left := [1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := rfl
  have h8 : steps tm_13_3 315 initConfig = some { st := some 8, left := [1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := steps_add tm_13_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_13_3 35 { st := some 8, left := [1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } = some { st := some 10, left := [1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h9 : steps tm_13_3 350 initConfig = some { st := some 10, left := [1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_13_3 35 { st := some 10, left := [1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 11, left := [1, 0, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h10 : steps tm_13_3 385 initConfig = some { st := some 11, left := [1, 0, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_13_3 35 { st := some 11, left := [1, 0, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 8, left := [1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h11 : steps tm_13_3 420 initConfig = some { st := some 8, left := [1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_13_3 35 { st := some 8, left := [1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h12 : steps tm_13_3 455 initConfig = some { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_13_3 35 { st := some 5, left := [], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 7, left := [1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h13 : steps tm_13_3 490 initConfig = some { st := some 7, left := [1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_13_3 35 { st := some 7, left := [1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 8, left := [1, 1, 1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h14 : steps tm_13_3 525 initConfig = some { st := some 8, left := [1, 1, 1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_13_3 35 { st := some 8, left := [1, 1, 1, 1, 0, 1, 1], cur := 1, right := [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 12, left := [], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h15 : steps tm_13_3 560 initConfig = some { st := some 12, left := [], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_13_3 35 { st := some 12, left := [], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 12, left := [2, 1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h16 : steps tm_13_3 595 initConfig = some { st := some 12, left := [2, 1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_13_3 31 { st := some 12, left := [2, 1, 1, 1, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h17 : steps tm_13_3 626 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_13_3 595 31 initConfig _ _ h16 hstep17
  exact h17

/-! ### BB(14,3) — > f_{ω×2}(1) (`fwm2_3` @ step 124) -/
def tm_14_3 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 1, 0 => some ⟨2, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨0, Dir.L, some 6⟩
  | 4, 0 => some ⟨0, Dir.L, some 5⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.R, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, none⟩
  | 5, 2 => some ⟨0, Dir.L, some 13⟩
  | 6, 0 => some ⟨0, Dir.R, some 2⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 0⟩
  | 8, 0 => some ⟨0, Dir.L, some 9⟩
  | 8, 1 => some ⟨0, Dir.L, some 2⟩
  | 8, 2 => some ⟨0, Dir.L, some 12⟩
  | 9, 0 => some ⟨0, Dir.L, some 4⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨0, Dir.L, some 11⟩
  | 10, 0 => some ⟨1, Dir.R, some 0⟩
  | 10, 1 => some ⟨0, Dir.L, some 11⟩
  | 10, 2 => some ⟨2, Dir.L, some 12⟩
  | 11, 0 => some ⟨1, Dir.L, some 10⟩
  | 11, 1 => some ⟨0, Dir.L, some 12⟩
  | 11, 2 => some ⟨1, Dir.R, some 13⟩
  | 12, 0 => some ⟨1, Dir.R, some 11⟩
  | 12, 1 => some ⟨0, Dir.L, some 13⟩
  | 12, 2 => some ⟨2, Dir.R, some 3⟩
  | 13, 0 => some ⟨2, Dir.L, some 10⟩
  | 13, 1 => some ⟨2, Dir.R, some 11⟩
  | 13, 2 => some ⟨1, Dir.R, some 1⟩
  | _, _ => none

theorem valid_14_3 : ValidTM 14 3 tm_14_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, trivial⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 14 => rfl

def landmark_14_3 : Config := { st := some 1, left := [1, 1, 1], cur := 0, right := [2, 1, 0, 0, 1, 2] }
theorem reaches_landmark_14_3 : steps tm_14_3 124 initConfig = some landmark_14_3 := by
  have h0 : steps tm_14_3 35 initConfig = some { st := some 10, left := [], cur := 0, right := [1, 0, 1] } := rfl
  have hstep1 : steps tm_14_3 35 { st := some 10, left := [], cur := 0, right := [1, 0, 1] } = some { st := some 13, left := [1, 1], cur := 1, right := [0, 1, 2] } := rfl
  have h1 : steps tm_14_3 70 initConfig = some { st := some 13, left := [1, 1], cur := 1, right := [0, 1, 2] } := steps_add tm_14_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_3 35 { st := some 13, left := [1, 1], cur := 1, right := [0, 1, 2] } = some { st := some 10, left := [], cur := 2, right := [1, 0, 0, 0, 0, 1, 2] } := rfl
  have h2 : steps tm_14_3 105 initConfig = some { st := some 10, left := [], cur := 2, right := [1, 0, 0, 0, 0, 1, 2] } := steps_add tm_14_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_3 19 { st := some 10, left := [], cur := 2, right := [1, 0, 0, 0, 0, 1, 2] } = some { st := some 1, left := [1, 1, 1], cur := 0, right := [2, 1, 0, 0, 1, 2] } := rfl
  have h3 : steps tm_14_3 124 initConfig = some { st := some 1, left := [1, 1, 1], cur := 0, right := [2, 1, 0, 0, 1, 2] } := steps_add tm_14_3 105 19 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(15,3) — > f_{ω}(18) (`fw_3` @ step 988) -/
def tm_15_3 : TM
  | 0, 0 => some ⟨0, Dir.L, some 5⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨0, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨1, Dir.L, some 2⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨1, Dir.R, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 6⟩
  | 5, 2 => some ⟨2, Dir.L, some 7⟩
  | 6, 0 => some ⟨1, Dir.R, some 5⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨0, Dir.R, some 14⟩
  | 7, 0 => some ⟨1, Dir.R, some 6⟩
  | 7, 1 => some ⟨0, Dir.L, some 8⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 0 => some ⟨1, Dir.R, some 7⟩
  | 8, 1 => some ⟨0, Dir.L, some 9⟩
  | 8, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 0 => some ⟨1, Dir.R, some 8⟩
  | 9, 1 => some ⟨0, Dir.L, some 10⟩
  | 9, 2 => some ⟨2, Dir.L, some 10⟩
  | 10, 0 => some ⟨1, Dir.R, some 9⟩
  | 10, 1 => some ⟨0, Dir.L, some 11⟩
  | 10, 2 => some ⟨2, Dir.R, some 8⟩
  | 11, 0 => some ⟨1, Dir.R, some 10⟩
  | 11, 1 => some ⟨0, Dir.L, some 12⟩
  | 11, 2 => some ⟨2, Dir.R, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, some 11⟩
  | 12, 1 => some ⟨0, Dir.L, some 13⟩
  | 12, 2 => some ⟨2, Dir.R, some 14⟩
  | 13, 0 => some ⟨1, Dir.R, some 12⟩
  | 13, 1 => some ⟨0, Dir.L, some 14⟩
  | 13, 2 => some ⟨0, Dir.L, some 10⟩
  | 14, 0 => some ⟨1, Dir.R, some 13⟩
  | 14, 1 => some ⟨2, Dir.L, some 5⟩
  | 14, 2 => some ⟨1, Dir.L, some 9⟩
  | _, _ => none

theorem valid_15_3 : ValidTM 15 3 tm_15_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 1 =>
      match sym with
      | 0 => exact ⟨by decide, trivial⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 2 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 3 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 4 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 5 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 6 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 7 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 8 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 9 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 10 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 11 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 12 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 13 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | 14 =>
      match sym with
      | 0 => exact ⟨by decide, by decide⟩
      | 1 => exact ⟨by decide, by decide⟩
      | 2 => exact ⟨by decide, by decide⟩
      | _ + 3 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 1 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 2 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 3 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 4 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 5 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 6 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 7 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 8 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 9 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 10 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 11 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 12 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 13 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | 14 =>
      match sym with
      | 0 | 1 | 2 => omega
      | _ + 3 => rfl
    | _ + 15 => rfl

def landmark_15_3 : Config := { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] }
theorem reaches_landmark_15_3 : steps tm_15_3 988 initConfig = some landmark_15_3 := by
  have h0 : steps tm_15_3 35 initConfig = some { st := some 9, left := [], cur := 1, right := [] } := rfl
  have hstep1 : steps tm_15_3 35 { st := some 9, left := [], cur := 1, right := [] } = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h1 : steps tm_15_3 70 initConfig = some { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_15_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_15_3 35 { st := some 6, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 9, left := [1, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h2 : steps tm_15_3 105 initConfig = some { st := some 9, left := [1, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_15_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_15_3 35 { st := some 9, left := [1, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [] } := rfl
  have h3 : steps tm_15_3 140 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [] } := steps_add tm_15_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_15_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [] } = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [] } := rfl
  have h4 : steps tm_15_3 175 initConfig = some { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [] } := steps_add tm_15_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_15_3 35 { st := some 7, left := [1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := rfl
  have h5 : steps tm_15_3 210 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } := steps_add tm_15_3 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_15_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1], cur := 1, right := [] } = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } := rfl
  have h6 : steps tm_15_3 245 initConfig = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } := steps_add tm_15_3 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_15_3 35 { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [] } = some { st := some 8, left := [], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h7 : steps tm_15_3 280 initConfig = some { st := some 8, left := [], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_15_3 35 { st := some 8, left := [], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 13, left := [1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2] } := rfl
  have h8 : steps tm_15_3 315 initConfig = some { st := some 13, left := [1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2] } := steps_add tm_15_3 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_15_3 35 { st := some 13, left := [1, 0, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := rfl
  have h9 : steps tm_15_3 350 initConfig = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } := steps_add tm_15_3 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_15_3 35 { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] } = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 2] } := rfl
  have h10 : steps tm_15_3 385 initConfig = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 2] } := steps_add tm_15_3 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_15_3 35 { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 2] } = some { st := some 7, left := [1, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h11 : steps tm_15_3 420 initConfig = some { st := some 7, left := [1, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_15_3 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_15_3 35 { st := some 7, left := [1, 1, 1, 1], cur := 1, right := [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 13, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := rfl
  have h12 : steps tm_15_3 455 initConfig = some { st := some 13, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } := steps_add tm_15_3 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_15_3 35 { st := some 13, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2] } = some { st := some 14, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 2] } := rfl
  have h13 : steps tm_15_3 490 initConfig = some { st := some 14, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 2] } := steps_add tm_15_3 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_15_3 35 { st := some 14, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 2] } = some { st := some 14, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h14 : steps tm_15_3 525 initConfig = some { st := some 14, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_15_3 35 { st := some 14, left := [1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 14, left := [0, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h15 : steps tm_15_3 560 initConfig = some { st := some 14, left := [0, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_15_3 35 { st := some 14, left := [0, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 10, left := [1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h16 : steps tm_15_3 595 initConfig = some { st := some 10, left := [1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_15_3 35 { st := some 10, left := [1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h17 : steps tm_15_3 630 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_15_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 13, left := [0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h18 : steps tm_15_3 665 initConfig = some { st := some 13, left := [0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_15_3 35 { st := some 13, left := [0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 10, left := [1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h19 : steps tm_15_3 700 initConfig = some { st := some 10, left := [1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_15_3 35 { st := some 10, left := [1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 5, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h20 : steps tm_15_3 735 initConfig = some { st := some 5, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_15_3 35 { st := some 5, left := [1, 1, 1, 1], cur := 2, right := [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 12, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h21 : steps tm_15_3 770 initConfig = some { st := some 12, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_15_3 35 { st := some 12, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h22 : steps tm_15_3 805 initConfig = some { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_15_3 35 { st := some 8, left := [], cur := 0, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h23 : steps tm_15_3 840 initConfig = some { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_15_3 35 { st := some 9, left := [1, 1, 1, 1, 1, 0, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 5, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h24 : steps tm_15_3 875 initConfig = some { st := some 5, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_15_3 35 { st := some 5, left := [1, 1, 1, 1, 1, 1], cur := 0, right := [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 10, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h25 : steps tm_15_3 910 initConfig = some { st := some 10, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_15_3 35 { st := some 10, left := [2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 9, left := [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h26 : steps tm_15_3 945 initConfig = some { st := some 9, left := [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_15_3 35 { st := some 9, left := [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 12, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h27 : steps tm_15_3 980 initConfig = some { st := some 12, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_15_3 8 { st := some 12, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := rfl
  have h28 : steps tm_15_3 988 initConfig = some { st := some 0, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] } := steps_add tm_15_3 980 8 initConfig _ _ h27 hstep28
  exact h28

end BB.Champions2026_11_23.S3
