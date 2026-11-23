/-
  BB/Champions2026_11_23_S4.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 11 4-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_23.S4
open BB

/-! ### BB(3,4) — > f_{ω}(3) (`fw_4` @ step 241) -/
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

/-! ### BB(4,4) — > f_{ω}(1) (`fw_4` @ step 374) -/
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

/-! ### BB(5,4) — > f_{ω+1}(13) (`fw1_4` @ step 236) -/
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

/-! ### BB(6,4) — > f_{ω+1}(1) (`fw1_4` @ step 210) -/
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

/-! ### BB(7,4) — > f_{ω+3}(1) (`fw3_4` @ step 68) -/
def tm_7_4 : TM
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

def landmark_7_4 : Config := { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] }
theorem reaches_landmark_7_4 : steps tm_7_4 68 initConfig = some landmark_7_4 := by
  have h0 : steps tm_7_4 35 initConfig = some { st := some 6, left := [2, 2, 1], cur := 0, right := [2, 3, 1, 1] } := rfl
  have hstep1 : steps tm_7_4 33 { st := some 6, left := [2, 2, 1], cur := 0, right := [2, 3, 1, 1] } = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] } := rfl
  have h1 : steps tm_7_4 68 initConfig = some { st := some 5, left := [1], cur := 0, right := [0, 0, 0, 1, 1, 2, 3, 1, 1] } := steps_add tm_7_4 35 33 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(8,4) — > f_{ω×2}(1) (`fwm2_3` @ step 90) -/
def tm_8_4 : TM
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

def landmark_8_4 : Config := { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] }
theorem reaches_landmark_8_4 : steps tm_8_4 90 initConfig = some landmark_8_4 := by
  have h0 : steps tm_8_4 35 initConfig = some { st := some 4, left := [2, 2], cur := 0, right := [1, 1, 1, 2] } := rfl
  have hstep1 : steps tm_8_4 35 { st := some 4, left := [2, 2], cur := 0, right := [1, 1, 1, 2] } = some { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } := rfl
  have h1 : steps tm_8_4 70 initConfig = some { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } := steps_add tm_8_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_8_4 20 { st := some 6, left := [0, 1], cur := 2, right := [0, 2, 0, 1, 1, 1, 1, 2] } = some { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] } := rfl
  have h2 : steps tm_8_4 90 initConfig = some { st := some 1, left := [1, 1], cur := 0, right := [2, 1, 0, 1, 1, 1, 1, 2] } := steps_add tm_8_4 70 20 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(9,4) — > f_{ω^2}(4) (`fwp2_4` @ step 23) -/
def tm_9_4 : TM
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

def landmark_9_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 3, 3] }
theorem reaches_landmark_9_4 : steps tm_9_4 23 initConfig = some landmark_9_4 := by
  have h0 : steps tm_9_4 23 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 3, 3] } := rfl
  exact h0

/-! ### BB(11,4) — > f_{ω^2+2}(1) (`fwp22_4` @ step 13) -/
def tm_11_4 : TM
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

def landmark_11_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 2] }
theorem reaches_landmark_11_4 : steps tm_11_4 13 initConfig = some landmark_11_4 := by
  have h0 : steps tm_11_4 13 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 1, 2] } := rfl
  exact h0

/-! ### BB(19,4) — > f_{ω^2+6}(1) (`fwp26_4` @ step 72) -/
def tm_19_4 : TM
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

def landmark_19_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] }
theorem reaches_landmark_19_4 : steps tm_19_4 72 initConfig = some landmark_19_4 := by
  have h0 : steps tm_19_4 35 initConfig = some { st := some 18, left := [1, 1], cur := 0, right := [] } := rfl
  have hstep1 : steps tm_19_4 35 { st := some 18, left := [1, 1], cur := 0, right := [] } = some { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := rfl
  have h1 : steps tm_19_4 70 initConfig = some { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := steps_add tm_19_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_19_4 2 { st := some 9, left := [], cur := 0, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := rfl
  have h2 : steps tm_19_4 72 initConfig = some { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 1] } := steps_add tm_19_4 70 2 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(20,4) — > f_{ω^2+5}(1) (`fwp25_4` @ step 141) -/
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

/-! ### BB(21,4) — > f_{ω^2+4}(2) (`fwp24_4` @ step 254) -/
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

end BB.Champions2026_11_23.S4
