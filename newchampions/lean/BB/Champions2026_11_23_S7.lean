/-
  BB/Champions2026_11_23_S7.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 3 7-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_23.S7
open BB

/-! ### BB(3,7) — > f_{ω+1}(14) (`fw1_6` @ step 312) -/
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

/-! ### BB(4,7) — > f_{ω+3}(2) (`fw3_7` @ step 108) -/
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

/-! ### BB(5,7) — > f_{ω×2+1}(2) (`fwm21_7` @ step 56) -/
def tm_5_7 : TM
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

def landmark_5_7 : Config := { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] }
theorem reaches_landmark_5_7 : steps tm_5_7 56 initConfig = some landmark_5_7 := by
  have h0 : steps tm_5_7 35 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 0, right := [2] } := rfl
  have hstep1 : steps tm_5_7 21 { st := some 0, left := [2, 2, 2, 2, 3], cur := 0, right := [2] } = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] } := rfl
  have h1 : steps tm_5_7 56 initConfig = some { st := some 1, left := [2, 2, 2, 2, 3], cur := 1, right := [2, 2] } := steps_add tm_5_7 35 21 initConfig _ _ h0 hstep1
  exact h1

end BB.Champions2026_11_23.S7
