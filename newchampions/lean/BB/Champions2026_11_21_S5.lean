/-
  BB/Champions2026_11_21_S5.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 7 5-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S5
open BB

/-! ### BB(7,5) — > f_{ω×2}(f_ω(16)) (`fwm2fw_5` @ step 146) -/
def tm_7_5 : TM
  | 0, 0 => some ⟨1, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 2⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 1, 0 => some ⟨2, Dir.R, some 5⟩
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
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨3, Dir.R, some 5⟩
  | 5, 2 => some ⟨4, Dir.L, some 4⟩
  | 5, 3 => some ⟨2, Dir.R, some 3⟩
  | 5, 4 => some ⟨4, Dir.L, some 2⟩
  | 6, 0 => some ⟨2, Dir.L, some 2⟩
  | 6, 1 => some ⟨2, Dir.R, some 1⟩
  | 6, 2 => some ⟨3, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.R, some 6⟩
  | 6, 4 => some ⟨0, Dir.L, some 0⟩
  | _, _ => none

theorem valid_7_5 : ValidTM 7 5 tm_7_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 7 => rfl

def landmark_7_5 : Config := { st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [] }
theorem reaches_landmark_7_5 : steps tm_7_5 146 initConfig = some landmark_7_5 := by
  have h0 : steps tm_7_5 35 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 3, 3, 3], cur := 2, right := [3, 3, 1] }) := rfl
  have hstep1 : steps tm_7_5 35 ({ st := some 6, left := [2, 2, 2, 2, 3, 3, 3], cur := 2, right := [3, 3, 1] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 1] }) := rfl
  have h1 : steps tm_7_5 70 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 1] }) := steps_add tm_7_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_5 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 1] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1] }) := rfl
  have h2 : steps tm_7_5 105 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1] }) := steps_add tm_7_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_7_5 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1] }) = some ({ st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 1] }) := rfl
  have h3 : steps tm_7_5 140 initConfig = some ({ st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 1] }) := steps_add tm_7_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_7_5 6 ({ st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 1] }) = some ({ st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [] }) := rfl
  have h4 : steps tm_7_5 146 initConfig = some ({ st := some 0, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [] }) := steps_add tm_7_5 140 6 initConfig _ _ h3 hstep4
  exact h4

/-! ### BB(11,5) — > f_{ω^2+2}(6) (`fwp22_5_sw` @ step 126) -/
def tm_11_5 : TM
  | 0, 0 => some ⟨4, Dir.L, some 6⟩
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
  | 3, 4 => some ⟨0, Dir.L, some 10⟩
  | 4, 0 => some ⟨3, Dir.R, some 3⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 0 => some ⟨4, Dir.R, some 2⟩
  | 5, 1 => some ⟨3, Dir.L, some 3⟩
  | 5, 2 => some ⟨2, Dir.L, some 4⟩
  | 5, 3 => some ⟨3, Dir.L, some 4⟩
  | 5, 4 => some ⟨3, Dir.L, some 8⟩
  | 6, 0 => some ⟨1, Dir.R, some 6⟩
  | 6, 1 => some ⟨1, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.R, some 6⟩
  | 6, 3 => some ⟨3, Dir.L, some 6⟩
  | 6, 4 => some ⟨4, Dir.R, some 0⟩
  | 7, 0 => some ⟨1, Dir.R, some 2⟩
  | 7, 1 => some ⟨2, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 1⟩
  | 7, 3 => some ⟨1, Dir.L, some 4⟩
  | 7, 4 => some ⟨1, Dir.R, some 10⟩
  | 8, 0 => some ⟨0, Dir.R, some 2⟩
  | 8, 1 => some ⟨3, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 8⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 9, 0 => some ⟨3, Dir.R, some 1⟩
  | 9, 1 => some ⟨4, Dir.L, some 9⟩
  | 9, 2 => some ⟨4, Dir.L, some 9⟩
  | 9, 3 => some ⟨4, Dir.L, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 0⟩
  | 10, 0 => some ⟨1, Dir.L, some 9⟩
  | 10, 1 => some ⟨4, Dir.R, some 9⟩
  | 10, 2 => some ⟨0, Dir.L, some 3⟩
  | 10, 3 => some ⟨4, Dir.L, some 6⟩
  | _, _ => none

theorem valid_11_5 : ValidTM 11 5 tm_11_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 11 => rfl

def landmark_11_5 : Config := { st := some 6, left := [], cur := 3, right := [3, 4, 4, 0, 0, 0, 0, 0, 0, 4] }
theorem reaches_landmark_11_5 : steps tm_11_5 126 initConfig = some landmark_11_5 := by
  have h0 : steps tm_11_5 35 initConfig = some ({ st := some 9, left := [], cur := 0, right := [1, 0, 0, 0, 0, 4] }) := rfl
  have hstep1 : steps tm_11_5 35 ({ st := some 9, left := [], cur := 0, right := [1, 0, 0, 0, 0, 4] }) = some ({ st := some 3, left := [2, 4, 1, 1, 1, 2, 3], cur := 4, right := [0, 4] }) := rfl
  have h1 : steps tm_11_5 70 initConfig = some ({ st := some 3, left := [2, 4, 1, 1, 1, 2, 3], cur := 4, right := [0, 4] }) := steps_add tm_11_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_11_5 35 ({ st := some 3, left := [2, 4, 1, 1, 1, 2, 3], cur := 4, right := [0, 4] }) = some ({ st := some 9, left := [3, 4, 2, 3], cur := 1, right := [0, 0, 0, 0, 4] }) := rfl
  have h2 : steps tm_11_5 105 initConfig = some ({ st := some 9, left := [3, 4, 2, 3], cur := 1, right := [0, 0, 0, 0, 4] }) := steps_add tm_11_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_11_5 21 ({ st := some 9, left := [3, 4, 2, 3], cur := 1, right := [0, 0, 0, 0, 4] }) = some ({ st := some 6, left := [], cur := 3, right := [3, 4, 4, 0, 0, 0, 0, 0, 0, 4] }) := rfl
  have h3 : steps tm_11_5 126 initConfig = some ({ st := some 6, left := [], cur := 3, right := [3, 4, 4, 0, 0, 0, 0, 0, 0, 4] }) := steps_add tm_11_5 105 21 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(13,5) — > f_{ω^ω+1}(9) (`fwpw1_5b` @ step 148) -/
def tm_13_5 : TM
  | 0, 0 => some ⟨4, Dir.L, some 7⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨1, Dir.R, none⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 0 => some ⟨3, Dir.L, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 2⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.L, some 11⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.R, some 7⟩
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
  | 7, 0 => some ⟨4, Dir.R, some 9⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨2, Dir.L, some 1⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨1, Dir.R, some 5⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨0, Dir.L, some 12⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 2 => some ⟨0, Dir.L, some 12⟩
  | _, _ => none

theorem valid_13_5 : ValidTM 13 5 tm_13_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 3 | 4 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 => trivial | _ + 5 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 12 => match sym with | 0 | 2 => exact ⟨by decide, by decide⟩ | 1 | 3 | 4 => trivial | _ + 5 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 13 => rfl

def landmark_13_5 : Config := { st := some 0, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }
theorem reaches_landmark_13_5 : steps tm_13_5 148 initConfig = some landmark_13_5 := by
  have h0 : steps tm_13_5 35 initConfig = some ({ st := some 3, left := [4, 2], cur := 2, right := [1, 1, 4, 0, 1] }) := rfl
  have hstep1 : steps tm_13_5 35 ({ st := some 3, left := [4, 2], cur := 2, right := [1, 1, 4, 0, 1] }) = some ({ st := some 9, left := [1, 2, 2], cur := 1, right := [1, 1, 0, 4, 1, 1] }) := rfl
  have h1 : steps tm_13_5 70 initConfig = some ({ st := some 9, left := [1, 2, 2], cur := 1, right := [1, 1, 0, 4, 1, 1] }) := steps_add tm_13_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_13_5 35 ({ st := some 9, left := [1, 2, 2], cur := 1, right := [1, 1, 0, 4, 1, 1] }) = some ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1] }) := rfl
  have h2 : steps tm_13_5 105 initConfig = some ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1] }) := steps_add tm_13_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_13_5 35 ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1] }) = some ({ st := some 7, left := [3], cur := 2, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }) := rfl
  have h3 : steps tm_13_5 140 initConfig = some ({ st := some 7, left := [3], cur := 2, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }) := steps_add tm_13_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_13_5 8 ({ st := some 7, left := [3], cur := 2, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }) = some ({ st := some 0, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }) := rfl
  have h4 : steps tm_13_5 148 initConfig = some ({ st := some 0, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }) := steps_add tm_13_5 140 8 initConfig _ _ h3 hstep4
  exact h4

/-! ### BB(14,5) — > f_{ω^ω+2}(21) (`fwpw2_5` @ step 409) -/
def tm_14_5 : TM
  | 0, 0 => some ⟨1, Dir.R, some 4⟩
  | 0, 1 => some ⟨1, Dir.L, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 6⟩
  | 0, 3 => some ⟨3, Dir.L, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 0⟩
  | 1, 0 => some ⟨2, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨2, Dir.L, some 12⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 9⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.L, some 9⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨4, Dir.L, some 0⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨2, Dir.R, some 12⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 11⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨4, Dir.L, some 11⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨2, Dir.L, some 3⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨1, Dir.L, some 9⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨2, Dir.R, some 13⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨2, Dir.R, some 2⟩
  | 12, 2 => some ⟨0, Dir.L, some 13⟩
  | 12, 3 => some ⟨4, Dir.R, some 5⟩
  | 13, 0 => some ⟨3, Dir.R, some 1⟩
  | 13, 2 => some ⟨0, Dir.L, some 13⟩
  | 13, 3 => some ⟨0, Dir.L, some 13⟩
  | 13, 4 => some ⟨2, Dir.L, some 6⟩
  | _, _ => none

theorem valid_14_5 : ValidTM 14 5 tm_14_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 4 => trivial | _ + 5 => omega
    | 13 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 5 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 14 => rfl

def landmark_14_5 : Config := { st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_14_5 : steps tm_14_5 409 initConfig = some landmark_14_5 := by
  have h0 : steps tm_14_5 35 initConfig = some ({ st := some 10, left := [3, 3], cur := 3, right := [3, 3, 4, 3] }) := rfl
  have hstep1 : steps tm_14_5 35 ({ st := some 10, left := [3, 3], cur := 3, right := [3, 3, 4, 3] }) = some ({ st := some 9, left := [2], cur := 2, right := [3, 3, 4, 3, 3, 2, 3, 4, 3] }) := rfl
  have h1 : steps tm_14_5 70 initConfig = some ({ st := some 9, left := [2], cur := 2, right := [3, 3, 4, 3, 3, 2, 3, 4, 3] }) := steps_add tm_14_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_5 35 ({ st := some 9, left := [2], cur := 2, right := [3, 3, 4, 3, 3, 2, 3, 4, 3] }) = some ({ st := some 9, left := [3, 3, 3, 3, 2, 2], cur := 4, right := [2, 3, 3, 3, 4, 3] }) := rfl
  have h2 : steps tm_14_5 105 initConfig = some ({ st := some 9, left := [3, 3, 3, 3, 2, 2], cur := 4, right := [2, 3, 3, 3, 4, 3] }) := steps_add tm_14_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_5 35 ({ st := some 9, left := [3, 3, 3, 3, 2, 2], cur := 4, right := [2, 3, 3, 3, 4, 3] }) = some ({ st := some 9, left := [2], cur := 3, right := [3, 4, 3, 3, 2, 3, 4, 3, 3, 3, 3, 4, 3] }) := rfl
  have h3 : steps tm_14_5 140 initConfig = some ({ st := some 9, left := [2], cur := 3, right := [3, 4, 3, 3, 2, 3, 4, 3, 3, 3, 3, 4, 3] }) := steps_add tm_14_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_5 35 ({ st := some 9, left := [2], cur := 3, right := [3, 4, 3, 3, 2, 3, 4, 3, 3, 3, 3, 4, 3] }) = some ({ st := some 10, left := [3, 2], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 4, 3, 3, 3, 3, 4, 3] }) := rfl
  have h4 : steps tm_14_5 175 initConfig = some ({ st := some 10, left := [3, 2], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 4, 3, 3, 3, 3, 4, 3] }) := steps_add tm_14_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_14_5 35 ({ st := some 10, left := [3, 2], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 4, 3, 3, 3, 3, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 3] }) := rfl
  have h5 : steps tm_14_5 210 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 3] }) := steps_add tm_14_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_14_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) := rfl
  have h6 : steps tm_14_5 245 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) := steps_add tm_14_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_14_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) = some ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 2, 2, 1, 4] }) := rfl
  have h7 : steps tm_14_5 280 initConfig = some ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 2, 2, 1, 4] }) := steps_add tm_14_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_14_5 35 ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 2, 2, 1, 4] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 1, 4] }) := rfl
  have h8 : steps tm_14_5 315 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 1, 4] }) := steps_add tm_14_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_14_5 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 1, 4] }) = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 2, 1, 4] }) := rfl
  have h9 : steps tm_14_5 350 initConfig = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 2, 1, 4] }) := steps_add tm_14_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_14_5 35 ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 2, 1, 4] }) = some ({ st := some 6, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h10 : steps tm_14_5 385 initConfig = some ({ st := some 6, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_14_5 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_14_5 24 ({ st := some 6, left := [], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h11 : steps tm_14_5 409 initConfig = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_14_5 385 24 initConfig _ _ h10 hstep11
  exact h11

/-! ### BB(15,5) — > f_{ω^ω+3}(27) (`fwpw3_5` @ step 825) -/
def tm_15_5 : TM
  | 0, 0 => some ⟨2, Dir.R, some 6⟩
  | 0, 1 => some ⟨1, Dir.L, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 6⟩
  | 0, 3 => some ⟨3, Dir.L, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 0⟩
  | 1, 0 => some ⟨2, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.R, some 7⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨4, Dir.L, some 0⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨2, Dir.R, some 12⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 11⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 10⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨2, Dir.L, some 7⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨4, Dir.L, some 9⟩
  | 12, 2 => some ⟨0, Dir.L, some 13⟩
  | 12, 4 => some ⟨2, Dir.L, some 14⟩
  | 13, 0 => some ⟨3, Dir.R, some 1⟩
  | 13, 2 => some ⟨0, Dir.L, some 13⟩
  | 13, 3 => some ⟨0, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.R, some 2⟩
  | 14, 2 => some ⟨2, Dir.L, some 14⟩
  | 14, 3 => some ⟨2, Dir.L, some 14⟩
  | 14, 4 => some ⟨2, Dir.L, some 3⟩
  | _, _ => none

theorem valid_15_5 : ValidTM 15 5 tm_15_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 12 => match sym with | 1 | 2 | 4 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 3 => trivial | _ + 5 => omega
    | 13 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 5 => omega
    | 14 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 5 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 15 => rfl

def landmark_15_5 : Config := { st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }
theorem reaches_landmark_15_5 : steps tm_15_5 825 initConfig = some landmark_15_5 := by
  have h0 : steps tm_15_5 35 initConfig = some ({ st := some 1, left := [], cur := 2, right := [1, 3, 4, 1, 4, 3] }) := rfl
  have hstep1 : steps tm_15_5 35 ({ st := some 1, left := [], cur := 2, right := [1, 3, 4, 1, 4, 3] }) = some ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 3, 4, 4, 1, 4, 3] }) := rfl
  have h1 : steps tm_15_5 70 initConfig = some ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 3, 4, 4, 1, 4, 3] }) := steps_add tm_15_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_15_5 35 ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 3, 4, 4, 1, 4, 3] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 4, 3] }) := rfl
  have h2 : steps tm_15_5 105 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 4, 3] }) := steps_add tm_15_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_15_5 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [3, 1, 4, 3] }) = some ({ st := some 4, left := [2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 3] }) := rfl
  have h3 : steps tm_15_5 140 initConfig = some ({ st := some 4, left := [2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 3] }) := steps_add tm_15_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_15_5 35 ({ st := some 4, left := [2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 3] }) = some ({ st := some 10, left := [2, 2, 2, 2, 2], cur := 2, right := [4, 4, 4, 4, 4, 4, 4, 3] }) := rfl
  have h4 : steps tm_15_5 175 initConfig = some ({ st := some 10, left := [2, 2, 2, 2, 2], cur := 2, right := [4, 4, 4, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_15_5 35 ({ st := some 10, left := [2, 2, 2, 2, 2], cur := 2, right := [4, 4, 4, 4, 4, 4, 4, 3] }) = some ({ st := some 7, left := [2, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) := rfl
  have h5 : steps tm_15_5 210 initConfig = some ({ st := some 7, left := [2, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_15_5 35 ({ st := some 7, left := [2, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) := rfl
  have h6 : steps tm_15_5 245 initConfig = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_15_5 35 ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 3] }) := rfl
  have h7 : steps tm_15_5 280 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_15_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3] }) := rfl
  have h8 : steps tm_15_5 315 initConfig = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_15_5 35 ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3] }) := rfl
  have h9 : steps tm_15_5 350 initConfig = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3] }) := steps_add tm_15_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_15_5 35 ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3] }) := rfl
  have h10 : steps tm_15_5 385 initConfig = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3] }) := steps_add tm_15_5 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_15_5 35 ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3] }) := rfl
  have h11 : steps tm_15_5 420 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3] }) := steps_add tm_15_5 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_15_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 3] }) := rfl
  have h12 : steps tm_15_5 455 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 3] }) := steps_add tm_15_5 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_15_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 3, 4, 3] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3] }) := rfl
  have h13 : steps tm_15_5 490 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3] }) := steps_add tm_15_5 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_15_5 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3] }) = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) := rfl
  have h14 : steps tm_15_5 525 initConfig = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) := steps_add tm_15_5 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_15_5 35 ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3] }) = some ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 2, 2, 1, 4] }) := rfl
  have h15 : steps tm_15_5 560 initConfig = some ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 2, 2, 1, 4] }) := steps_add tm_15_5 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_15_5 35 ({ st := some 8, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 2, 2, 1, 4] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4] }) := rfl
  have h16 : steps tm_15_5 595 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4] }) := steps_add tm_15_5 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_15_5 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4] }) = some ({ st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) := rfl
  have h17 : steps tm_15_5 630 initConfig = some ({ st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) := steps_add tm_15_5 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_15_5 35 ({ st := some 2, left := [], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4] }) := rfl
  have h18 : steps tm_15_5 665 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4] }) := steps_add tm_15_5 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_15_5 35 ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h19 : steps tm_15_5 700 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_5 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_15_5 35 ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h20 : steps tm_15_5 735 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_5 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_15_5 35 ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h21 : steps tm_15_5 770 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_5 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_15_5 35 ({ st := some 4, left := [2, 2, 2, 2, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 14, left := [2], cur := 4, right := [2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h22 : steps tm_15_5 805 initConfig = some ({ st := some 14, left := [2], cur := 4, right := [2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_5 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_15_5 20 ({ st := some 14, left := [2], cur := 4, right := [2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h23 : steps tm_15_5 825 initConfig = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_5 805 20 initConfig _ _ h22 hstep23
  exact h23

/-! ### BB(16,5) — > f_{ω^ω+4}(20) (`fwpw4_5` @ step 359) -/
def tm_16_5 : TM
  | 0, 0 => some ⟨3, Dir.L, some 6⟩
  | 0, 1 => some ⟨1, Dir.L, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 6⟩
  | 0, 3 => some ⟨3, Dir.L, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 0⟩
  | 1, 0 => some ⟨2, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨3, Dir.L, some 10⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨1, Dir.R, some 15⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨0, Dir.R, some 8⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨4, Dir.L, some 0⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨2, Dir.R, some 12⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 11⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨1, Dir.L, some 15⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨4, Dir.L, some 15⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.L, some 11⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨4, Dir.R, some 1⟩
  | 12, 2 => some ⟨0, Dir.L, some 13⟩
  | 12, 3 => some ⟨4, Dir.L, some 15⟩
  | 12, 4 => some ⟨2, Dir.L, some 14⟩
  | 13, 0 => some ⟨3, Dir.R, some 1⟩
  | 13, 2 => some ⟨0, Dir.L, some 13⟩
  | 13, 3 => some ⟨0, Dir.L, some 13⟩
  | 14, 0 => some ⟨0, Dir.R, some 2⟩
  | 14, 1 => some ⟨0, Dir.L, some 10⟩
  | 14, 2 => some ⟨2, Dir.L, some 14⟩
  | 14, 3 => some ⟨2, Dir.L, some 14⟩
  | 14, 4 => some ⟨2, Dir.R, some 15⟩
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 1 => some ⟨4, Dir.L, some 1⟩
  | 15, 2 => some ⟨4, Dir.L, some 15⟩
  | 15, 3 => some ⟨4, Dir.L, some 15⟩
  | 15, 4 => some ⟨2, Dir.R, some 12⟩
  | _, _ => none

theorem valid_16_5 : ValidTM 16 5 tm_16_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 12 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 5 => omega
    | 13 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 5 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 16 => rfl

def landmark_16_5 : Config := { st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem reaches_landmark_16_5 : steps tm_16_5 359 initConfig = some landmark_16_5 := by
  have h0 : steps tm_16_5 35 initConfig = some ({ st := some 2, left := [2, 2, 2], cur := 4, right := [4, 4, 1, 4] }) := rfl
  have hstep1 : steps tm_16_5 35 ({ st := some 2, left := [2, 2, 2], cur := 4, right := [4, 4, 1, 4] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 2, 2, 1, 4] }) := rfl
  have h1 : steps tm_16_5 70 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 2, 2, 1, 4] }) := steps_add tm_16_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_5 35 ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [1, 2, 2, 1, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2], cur := 3, right := [4, 4, 3, 2, 1, 4] }) := rfl
  have h2 : steps tm_16_5 105 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2], cur := 3, right := [4, 4, 3, 2, 1, 4] }) := steps_add tm_16_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_5 35 ({ st := some 4, left := [2, 2, 2, 2, 2], cur := 3, right := [4, 4, 3, 2, 1, 4] }) = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 3, 2, 1, 4] }) := rfl
  have h3 : steps tm_16_5 140 initConfig = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 3, 2, 1, 4] }) := steps_add tm_16_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_5 35 ({ st := some 11, left := [3, 3], cur := 3, right := [1, 3, 4, 4, 4, 4, 4, 3, 2, 1, 4] }) = some ({ st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 2, 1, 4] }) := rfl
  have h4 : steps tm_16_5 175 initConfig = some ({ st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 2, 1, 4] }) := steps_add tm_16_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_5 35 ({ st := some 1, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 3, 2, 1, 4] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 2, 1, 4] }) := rfl
  have h5 : steps tm_16_5 210 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 2, 1, 4] }) := steps_add tm_16_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_16_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 3, 2, 1, 4] }) = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4] }) := rfl
  have h6 : steps tm_16_5 245 initConfig = some ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4] }) := steps_add tm_16_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_16_5 35 ({ st := some 11, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3] }) := rfl
  have h7 : steps tm_16_5 280 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3] }) := steps_add tm_16_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_16_5 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3] }) = some ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h8 : steps tm_16_5 315 initConfig = some ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_16_5 35 ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) = some ({ st := some 7, left := [2, 3], cur := 0, right := [0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h9 : steps tm_16_5 350 initConfig = some ({ st := some 7, left := [2, 3], cur := 0, right := [0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_16_5 9 ({ st := some 7, left := [2, 3], cur := 0, right := [0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h10 : steps tm_16_5 359 initConfig = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_5 350 9 initConfig _ _ h9 hstep10
  exact h10

/-! ### BB(18,5) — > f_{ε_0}(56) (`fe0_5` @ step 2040) -/
def tm_18_5 : TM
  | 0, 0 => some ⟨4, Dir.R, some 15⟩
  | 0, 2 => some ⟨0, Dir.R, some 5⟩
  | 0, 3 => some ⟨0, Dir.R, some 3⟩
  | 0, 4 => some ⟨1, Dir.L, some 16⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 1⟩
  | 1, 2 => some ⟨2, Dir.L, some 2⟩
  | 1, 3 => some ⟨4, Dir.L, some 6⟩
  | 1, 4 => some ⟨3, Dir.R, some 17⟩
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 2⟩
  | 2, 3 => some ⟨3, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨1, Dir.L, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨2, Dir.R, some 3⟩
  | 4, 0 => some ⟨3, Dir.L, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 4 => some ⟨2, Dir.L, some 10⟩
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 6, 0 => some ⟨0, Dir.R, some 8⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨3, Dir.R, some 8⟩
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 6, 4 => some ⟨1, Dir.R, some 8⟩
  | 7, 0 => some ⟨2, Dir.L, some 0⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.L, some 7⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.R, some 5⟩
  | 8, 0 => some ⟨3, Dir.R, some 13⟩
  | 8, 1 => some ⟨4, Dir.R, some 2⟩
  | 8, 2 => some ⟨0, Dir.L, some 0⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 8, 4 => some ⟨2, Dir.L, some 1⟩
  | 9, 0 => some ⟨2, Dir.R, some 14⟩
  | 9, 1 => some ⟨1, Dir.L, some 14⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => some ⟨1, Dir.L, some 7⟩
  | 10, 0 => some ⟨2, Dir.L, some 11⟩
  | 10, 1 => some ⟨3, Dir.R, some 17⟩
  | 10, 2 => some ⟨2, Dir.R, some 10⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 14⟩
  | 11, 1 => some ⟨2, Dir.R, some 14⟩
  | 11, 2 => some ⟨2, Dir.L, some 11⟩
  | 11, 3 => some ⟨3, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 11⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 1 => some ⟨1, Dir.L, some 17⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.R, some 12⟩
  | 13, 0 => some ⟨4, Dir.L, some 9⟩
  | 13, 1 => some ⟨1, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 4 => some ⟨1, Dir.L, some 14⟩
  | 14, 0 => some ⟨1, Dir.R, some 1⟩
  | 14, 1 => some ⟨4, Dir.R, some 15⟩
  | 14, 2 => some ⟨1, Dir.R, some 10⟩
  | 14, 3 => some ⟨0, Dir.R, some 12⟩
  | 14, 4 => some ⟨4, Dir.L, some 13⟩
  | 15, 0 => some ⟨4, Dir.L, some 9⟩
  | 15, 1 => some ⟨1, Dir.R, some 15⟩
  | 15, 2 => some ⟨2, Dir.R, some 15⟩
  | 15, 3 => some ⟨3, Dir.R, some 15⟩
  | 15, 4 => some ⟨0, Dir.R, some 15⟩
  | 16, 0 => some ⟨1, Dir.R, some 1⟩
  | 16, 1 => some ⟨1, Dir.L, some 16⟩
  | 16, 2 => some ⟨2, Dir.L, some 16⟩
  | 16, 3 => some ⟨3, Dir.L, some 16⟩
  | 16, 4 => some ⟨1, Dir.L, some 16⟩
  | 17, 0 => some ⟨2, Dir.R, some 10⟩
  | 17, 1 => some ⟨4, Dir.L, some 17⟩
  | 17, 2 => some ⟨3, Dir.L, some 3⟩
  | 17, 3 => some ⟨0, Dir.R, some 0⟩
  | 17, 4 => some ⟨4, Dir.L, some 6⟩
  | _, _ => none

theorem valid_18_5 : ValidTM 18 5 tm_18_5 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 5 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 5 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 5 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 16 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | 17 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | _ + 5 => omega
    | _ + 18 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 16 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | 17 => match sym with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
    | _ + 18 => rfl

def landmark_18_5 : Config := { st := some 1, left := [1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_18_5 : steps tm_18_5 2040 initConfig = some landmark_18_5 := by
  have h0 : steps tm_18_5 35 initConfig = some ({ st := some 11, left := [0, 2, 4, 2, 4, 1], cur := 4, right := [3] }) := rfl
  have hstep1 : steps tm_18_5 35 ({ st := some 11, left := [0, 2, 4, 2, 4, 1], cur := 4, right := [3] }) = some ({ st := some 4, left := [2, 3, 3, 3, 1, 3, 3], cur := 3, right := [1, 1] }) := rfl
  have h1 : steps tm_18_5 70 initConfig = some ({ st := some 4, left := [2, 3, 3, 3, 1, 3, 3], cur := 3, right := [1, 1] }) := steps_add tm_18_5 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_18_5 35 ({ st := some 4, left := [2, 3, 3, 3, 1, 3, 3], cur := 3, right := [1, 1] }) = some ({ st := some 10, left := [2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 1, right := [1, 2, 4] }) := rfl
  have h2 : steps tm_18_5 105 initConfig = some ({ st := some 10, left := [2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 1, right := [1, 2, 4] }) := steps_add tm_18_5 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_18_5 35 ({ st := some 10, left := [2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 1, right := [1, 2, 4] }) = some ({ st := some 9, left := [0, 3, 2, 1, 4, 2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 3, right := [4] }) := rfl
  have h3 : steps tm_18_5 140 initConfig = some ({ st := some 9, left := [0, 3, 2, 1, 4, 2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 3, right := [4] }) := steps_add tm_18_5 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_18_5 35 ({ st := some 9, left := [0, 3, 2, 1, 4, 2, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 3, right := [4] }) = some ({ st := some 0, left := [3, 2, 4, 1, 1, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 2, right := [3, 1] }) := rfl
  have h4 : steps tm_18_5 175 initConfig = some ({ st := some 0, left := [3, 2, 4, 1, 1, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 2, right := [3, 1] }) := steps_add tm_18_5 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_18_5 35 ({ st := some 0, left := [3, 2, 4, 1, 1, 2, 3, 3, 3, 1, 3, 3, 3, 4], cur := 2, right := [3, 1] }) = some ({ st := some 16, left := [4], cur := 3, right := [3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) := rfl
  have h5 : steps tm_18_5 210 initConfig = some ({ st := some 16, left := [4], cur := 3, right := [3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) := steps_add tm_18_5 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_18_5 35 ({ st := some 16, left := [4], cur := 3, right := [3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) = some ({ st := some 3, left := [3, 3, 2, 3, 3, 2, 3], cur := 1, right := [3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) := rfl
  have h6 : steps tm_18_5 245 initConfig = some ({ st := some 3, left := [3, 3, 2, 3, 3, 2, 3], cur := 1, right := [3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) := steps_add tm_18_5 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_18_5 35 ({ st := some 3, left := [3, 3, 2, 3, 3, 2, 3], cur := 1, right := [3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3] }) = some ({ st := some 15, left := [3, 4], cur := 3, right := [2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 1] }) := rfl
  have h7 : steps tm_18_5 280 initConfig = some ({ st := some 15, left := [3, 4], cur := 3, right := [2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 1] }) := steps_add tm_18_5 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_18_5 35 ({ st := some 15, left := [3, 4], cur := 3, right := [2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3, 1] }) = some ({ st := some 1, left := [3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 4], cur := 3, right := [2, 2, 2] }) := rfl
  have h8 : steps tm_18_5 315 initConfig = some ({ st := some 1, left := [3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 4], cur := 3, right := [2, 2, 2] }) := steps_add tm_18_5 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_18_5 35 ({ st := some 1, left := [3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 4], cur := 3, right := [2, 2, 2] }) = some ({ st := some 5, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [2, 1, 1, 0, 4, 2, 2, 2, 2, 2] }) := rfl
  have h9 : steps tm_18_5 350 initConfig = some ({ st := some 5, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [2, 1, 1, 0, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_18_5 35 ({ st := some 5, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [2, 1, 1, 0, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 15, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 4], cur := 3, right := [3, 2, 1, 0, 0, 4, 2, 2, 2, 2, 2] }) := rfl
  have h10 : steps tm_18_5 385 initConfig = some ({ st := some 15, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 4], cur := 3, right := [3, 2, 1, 0, 0, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_18_5 35 ({ st := some 15, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 4], cur := 3, right := [3, 2, 1, 0, 0, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 5, left := [3, 3, 2, 3, 3, 2, 2, 2], cur := 2, right := [3, 3, 1, 3, 3, 3, 0, 4, 2, 0, 4, 2, 2, 2, 2, 2] }) := rfl
  have h11 : steps tm_18_5 420 initConfig = some ({ st := some 5, left := [3, 3, 2, 3, 3, 2, 2, 2], cur := 2, right := [3, 3, 1, 3, 3, 3, 0, 4, 2, 0, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_18_5 35 ({ st := some 5, left := [3, 3, 2, 3, 3, 2, 2, 2], cur := 2, right := [3, 3, 1, 3, 3, 3, 0, 4, 2, 0, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 4, left := [2], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 4, 2, 2, 2, 2, 2] }) := rfl
  have h12 : steps tm_18_5 455 initConfig = some ({ st := some 4, left := [2], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_18_5 35 ({ st := some 4, left := [2], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 9, left := [0, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 4] }) := rfl
  have h13 : steps tm_18_5 490 initConfig = some ({ st := some 9, left := [0, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 4] }) := steps_add tm_18_5 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_18_5 35 ({ st := some 9, left := [0, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 4] }) = some ({ st := some 11, left := [2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2] }) := rfl
  have h14 : steps tm_18_5 525 initConfig = some ({ st := some 11, left := [2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2] }) := steps_add tm_18_5 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_18_5 35 ({ st := some 11, left := [2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2] }) = some ({ st := some 13, left := [2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2] }) := rfl
  have h15 : steps tm_18_5 560 initConfig = some ({ st := some 13, left := [2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_18_5 35 ({ st := some 13, left := [2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 3, 4], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 9, left := [2, 4], cur := 1, right := [4, 4, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) := rfl
  have h16 : steps tm_18_5 595 initConfig = some ({ st := some 9, left := [2, 4], cur := 1, right := [4, 4, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_18_5 35 ({ st := some 9, left := [2, 4], cur := 1, right := [4, 4, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 3, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) := rfl
  have h17 : steps tm_18_5 630 initConfig = some ({ st := some 3, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_18_5 35 ({ st := some 3, left := [3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2] }) = some ({ st := some 4, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h18 : steps tm_18_5 665 initConfig = some ({ st := some 4, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_18_5 35 ({ st := some 4, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3], cur := 3, right := [3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 15, left := [3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h19 : steps tm_18_5 700 initConfig = some ({ st := some 15, left := [3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_18_5 35 ({ st := some 15, left := [3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [2, 2, 0, 4, 2] }) := rfl
  have h20 : steps tm_18_5 735 initConfig = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [2, 2, 0, 4, 2] }) := steps_add tm_18_5 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_18_5 35 ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 4], cur := 2, right := [2, 2, 0, 4, 2] }) = some ({ st := some 5, left := [2], cur := 3, right := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h21 : steps tm_18_5 770 initConfig = some ({ st := some 5, left := [2], cur := 3, right := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_18_5 35 ({ st := some 5, left := [2], cur := 3, right := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 2, right := [0, 4, 2] }) := rfl
  have h22 : steps tm_18_5 805 initConfig = some ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 2, right := [0, 4, 2] }) := steps_add tm_18_5 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_18_5 35 ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 2, right := [0, 4, 2] }) = some ({ st := some 4, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h23 : steps tm_18_5 840 initConfig = some ({ st := some 4, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_18_5 35 ({ st := some 4, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2], cur := 3, right := [1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 15, left := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h24 : steps tm_18_5 875 initConfig = some ({ st := some 15, left := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_18_5 35 ({ st := some 15, left := [3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 8, left := [3, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 4, right := [] }) := rfl
  have h25 : steps tm_18_5 910 initConfig = some ({ st := some 8, left := [3, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 4, right := [] }) := steps_add tm_18_5 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_18_5 35 ({ st := some 8, left := [3, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 4, right := [] }) = some ({ st := some 6, left := [2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h26 : steps tm_18_5 945 initConfig = some ({ st := some 6, left := [2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_18_5 35 ({ st := some 6, left := [2, 2, 1, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 7, left := [4], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h27 : steps tm_18_5 980 initConfig = some ({ st := some 7, left := [4], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_18_5 35 ({ st := some 7, left := [4], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 10, left := [2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h28 : steps tm_18_5 1015 initConfig = some ({ st := some 10, left := [2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_18_5 35 ({ st := some 10, left := [2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 4, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 2, right := [3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h29 : steps tm_18_5 1050 initConfig = some ({ st := some 4, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 2, right := [3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_18_5 35 ({ st := some 4, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2], cur := 2, right := [3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 15, left := [3, 2, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h30 : steps tm_18_5 1085 initConfig = some ({ st := some 15, left := [3, 2, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_18_5 35 ({ st := some 15, left := [3, 2, 3, 2, 3, 4], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 1] }) := rfl
  have h31 : steps tm_18_5 1120 initConfig = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 1] }) := steps_add tm_18_5 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_18_5 35 ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 1] }) = some ({ st := some 7, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h32 : steps tm_18_5 1155 initConfig = some ({ st := some 7, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_18_5 35 ({ st := some 7, left := [3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 5, left := [2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h33 : steps tm_18_5 1190 initConfig = some ({ st := some 5, left := [2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_18_5 35 ({ st := some 5, left := [2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [0, 4, 2] }) := rfl
  have h34 : steps tm_18_5 1225 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [0, 4, 2] }) := steps_add tm_18_5 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_18_5 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 2, right := [0, 4, 2] }) = some ({ st := some 4, left := [1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 3, right := [3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h35 : steps tm_18_5 1260 initConfig = some ({ st := some 4, left := [1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 3, right := [3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_18_5 35 ({ st := some 4, left := [1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2], cur := 3, right := [3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 15, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h36 : steps tm_18_5 1295 initConfig = some ({ st := some 15, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_18_5 35 ({ st := some 15, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 1, 3, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [3, 2, 3, 3, 1] }) := rfl
  have h37 : steps tm_18_5 1330 initConfig = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [3, 2, 3, 3, 1] }) := steps_add tm_18_5 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_18_5 35 ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [3, 2, 3, 3, 1] }) = some ({ st := some 8, left := [3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h38 : steps tm_18_5 1365 initConfig = some ({ st := some 8, left := [3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_18_5 35 ({ st := some 8, left := [3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 6, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h39 : steps tm_18_5 1400 initConfig = some ({ st := some 6, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_18_5 35 ({ st := some 6, left := [3, 3, 2, 3, 3, 3, 1, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 7, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h40 : steps tm_18_5 1435 initConfig = some ({ st := some 7, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_18_5 35 ({ st := some 7, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 6, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h41 : steps tm_18_5 1470 initConfig = some ({ st := some 6, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_18_5 35 ({ st := some 6, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 0, right := [] }) := rfl
  have h42 : steps tm_18_5 1505 initConfig = some ({ st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 0, right := [] }) := steps_add tm_18_5 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_18_5 35 ({ st := some 3, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 0, right := [] }) = some ({ st := some 4, left := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h43 : steps tm_18_5 1540 initConfig = some ({ st := some 4, left := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_18_5 35 ({ st := some 4, left := [3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 15, left := [2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h44 : steps tm_18_5 1575 initConfig = some ({ st := some 15, left := [2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_18_5 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_18_5 35 ({ st := some 15, left := [2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 1] }) := rfl
  have h45 : steps tm_18_5 1610 initConfig = some ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 1] }) := steps_add tm_18_5 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_18_5 35 ({ st := some 15, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 1] }) = some ({ st := some 7, left := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h46 : steps tm_18_5 1645 initConfig = some ({ st := some 7, left := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_18_5 35 ({ st := some 7, left := [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 5, left := [2, 3, 2, 3, 2], cur := 3, right := [2, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h47 : steps tm_18_5 1680 initConfig = some ({ st := some 5, left := [2, 3, 2, 3, 2], cur := 3, right := [2, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_18_5 35 ({ st := some 5, left := [2, 3, 2, 3, 2], cur := 3, right := [2, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := rfl
  have h48 : steps tm_18_5 1715 initConfig = some ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) := steps_add tm_18_5 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_18_5 35 ({ st := some 5, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4, 2] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h49 : steps tm_18_5 1750 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_18_5 35 ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 4, left := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h50 : steps tm_18_5 1785 initConfig = some ({ st := some 4, left := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_18_5 35 ({ st := some 4, left := [3, 2, 3, 2, 3, 2, 3, 2, 3, 2], cur := 3, right := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 15, left := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := rfl
  have h51 : steps tm_18_5 1820 initConfig = some ({ st := some 15, left := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) := steps_add tm_18_5 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_18_5 35 ({ st := some 15, left := [2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 1] }) = some ({ st := some 15, left := [3, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 1, right := [] }) := rfl
  have h52 : steps tm_18_5 1855 initConfig = some ({ st := some 15, left := [3, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 1, right := [] }) := steps_add tm_18_5 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_18_5 35 ({ st := some 15, left := [3, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 1, right := [] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h53 : steps tm_18_5 1890 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_18_5 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h54 : steps tm_18_5 1925 initConfig = some ({ st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_18_5 35 ({ st := some 1, left := [2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 8, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h55 : steps tm_18_5 1960 initConfig = some ({ st := some 8, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_18_5 35 ({ st := some 8, left := [3, 2, 3, 3, 2, 3, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 4, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 6, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h56 : steps tm_18_5 1995 initConfig = some ({ st := some 6, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_18_5 35 ({ st := some 6, left := [2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 4], cur := 3, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 1, left := [2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h57 : steps tm_18_5 2030 initConfig = some ({ st := some 1, left := [2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_18_5 10 ({ st := some 1, left := [2, 3, 4], cur := 3, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 1, left := [1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h58 : steps tm_18_5 2040 initConfig = some ({ st := some 1, left := [1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_18_5 2030 10 initConfig _ _ h57 hstep58
  exact h58

end BB.Champions2026_11_21.S5
