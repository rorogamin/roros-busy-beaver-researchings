/-
  BB/Champions2026_11_23_S5.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 8 5-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_23.S5
open BB

/-! ### BB(3,5) — > f_{ω}(2) (`fw_4` @ step 263) -/
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

/-! ### BB(4,5) — > f_{ω+1}(3) (`fw1_4` @ step 308) -/
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

/-! ### BB(5,5) — > f_{ω+2}(3) (`fw2_5` @ step 50) -/
def tm_5_5 : TM
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

def landmark_5_5 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] }
theorem reaches_landmark_5_5 : steps tm_5_5 50 initConfig = some landmark_5_5 := by
  have h0 : steps tm_5_5 35 initConfig = some { st := some 4, left := [2, 3], cur := 2, right := [2, 4, 4, 4] } := rfl
  have hstep1 : steps tm_5_5 15 { st := some 4, left := [2, 3], cur := 2, right := [2, 4, 4, 4] } = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] } := rfl
  have h1 : steps tm_5_5 50 initConfig = some { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 2, 2, 4, 4, 4] } := steps_add tm_5_5 35 15 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(6,5) — > f_{ω×2}(2) (`fwm2_5` @ step 131) -/
def tm_6_5 : TM
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

def landmark_6_5 : Config := { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] }
theorem reaches_landmark_6_5 : steps tm_6_5 131 initConfig = some landmark_6_5 := by
  have h0 : steps tm_6_5 35 initConfig = some { st := some 4, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 2] } := rfl
  have hstep1 : steps tm_6_5 35 { st := some 4, left := [2, 2, 2, 3, 3], cur := 2, right := [3, 2] } = some { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } := rfl
  have h1 : steps tm_6_5 70 initConfig = some { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } := steps_add tm_6_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_5 35 { st := some 4, left := [2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2] } = some { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } := rfl
  have h2 : steps tm_6_5 105 initConfig = some { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } := steps_add tm_6_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_6_5 26 { st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 1] } = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] } := rfl
  have h3 : steps tm_6_5 131 initConfig = some { st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 1, right := [1] } := steps_add tm_6_5 105 26 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(8,5) — > f_{ω×2+1}(2) (`fwm21_5` @ step 82) -/
def tm_8_5 : TM
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

def landmark_8_5 : Config := { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] }
theorem reaches_landmark_8_5 : steps tm_8_5 82 initConfig = some landmark_8_5 := by
  have h0 : steps tm_8_5 35 initConfig = some { st := some 4, left := [3, 3, 3], cur := 4, right := [4, 4] } := rfl
  have hstep1 : steps tm_8_5 35 { st := some 4, left := [3, 3, 3], cur := 4, right := [4, 4] } = some { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } := rfl
  have h1 : steps tm_8_5 70 initConfig = some { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } := steps_add tm_8_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_5 12 { st := some 2, left := [2], cur := 3, right := [3, 3, 1, 4, 4] } = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := rfl
  have h2 : steps tm_8_5 82 initConfig = some { st := some 0, left := [2, 2, 2, 3], cur := 1, right := [1, 4, 4] } := steps_add tm_8_5 70 12 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(9,5) — > f_{ω×2+1}(1) (`fwm21_5` @ step 124) -/
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

/-! ### BB(10,5) — > f_{ω^2+2}(1) (`fwp22_5_sw` @ step 51) -/
def tm_10_5 : TM
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

def landmark_10_5 : Config := { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] }
theorem reaches_landmark_10_5 : steps tm_10_5 51 initConfig = some landmark_10_5 := by
  have h0 : steps tm_10_5 35 initConfig = some { st := some 3, left := [], cur := 4, right := [1, 1, 0, 4] } := rfl
  have hstep1 : steps tm_10_5 16 { st := some 3, left := [], cur := 4, right := [1, 1, 0, 4] } = some { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] } := rfl
  have h1 : steps tm_10_5 51 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 4, 4, 4, 0, 4] } := steps_add tm_10_5 35 16 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(12,5) — > f_{ω^ω}(4) (`fwpw_5` @ step 125) -/
def tm_12_5 : TM
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

def landmark_12_5 : Config := { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] }
theorem reaches_landmark_12_5 : steps tm_12_5 125 initConfig = some landmark_12_5 := by
  have h0 : steps tm_12_5 35 initConfig = some { st := some 2, left := [3, 2], cur := 2, right := [4, 2, 1, 1] } := rfl
  have hstep1 : steps tm_12_5 35 { st := some 2, left := [3, 2], cur := 2, right := [4, 2, 1, 1] } = some { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } := rfl
  have h1 : steps tm_12_5 70 initConfig = some { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } := steps_add tm_12_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_5 35 { st := some 9, left := [3, 2, 2, 2], cur := 0, right := [1, 4, 1, 1] } = some { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } := rfl
  have h2 : steps tm_12_5 105 initConfig = some { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } := steps_add tm_12_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_5 20 { st := some 5, left := [3, 0, 1, 2, 3, 3, 2, 2, 2, 2], cur := 0, right := [1] } = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] } := rfl
  have h3 : steps tm_12_5 125 initConfig = some { st := some 0, left := [2, 2, 2, 2, 3], cur := 1, right := [1, 1, 1, 4, 2, 1, 1] } := steps_add tm_12_5 105 20 initConfig _ _ h2 hstep3
  exact h3

end BB.Champions2026_11_23.S5
