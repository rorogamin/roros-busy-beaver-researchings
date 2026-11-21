/-
  BB/Champions2026_11_21_S8.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 8 8-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S8
open BB

/-! ### BB(5,8) — > f_{ω×2+1}(18) (`fwm21_8_blank` @ step 447) -/
def tm_5_8 : TM
  | 0, 0 => some ⟨4, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.R, some 2⟩
  | 0, 5 => some ⟨6, Dir.L, some 2⟩
  | 0, 6 => some ⟨7, Dir.L, some 3⟩
  | 0, 7 => some ⟨3, Dir.L, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨2, Dir.L, some 0⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 1⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.L, some 0⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 2⟩
  | 4, 0 => some ⟨7, Dir.L, some 2⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.R, some 0⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | _, _ => none

theorem valid_5_8 : ValidTM 5 8 tm_5_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 5 => rfl

def landmark_5_8 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem reaches_landmark_5_8 : steps tm_5_8 447 initConfig = some landmark_5_8 := by
  have h0 : steps tm_5_8 35 initConfig = some ({ st := some 3, left := [5], cur := 6, right := [4, 6, 4, 5, 4] }) := rfl
  have hstep1 : steps tm_5_8 35 ({ st := some 3, left := [5], cur := 6, right := [4, 6, 4, 5, 4] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 6, 5, 4] }) := rfl
  have h1 : steps tm_5_8 70 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 6, 5, 4] }) := steps_add tm_5_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_8 35 ({ st := some 3, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 6, 5, 4] }) = some ({ st := some 4, left := [6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 6, 5, 4] }) := rfl
  have h2 : steps tm_5_8 105 initConfig = some ({ st := some 4, left := [6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 6, 5, 4] }) := steps_add tm_5_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_8 35 ({ st := some 4, left := [6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 6, 5, 4] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 5, 4] }) := rfl
  have h3 : steps tm_5_8 140 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 5, 4] }) := steps_add tm_5_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_8 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 5, 4] }) = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 6, 5, 4] }) := rfl
  have h4 : steps tm_5_8 175 initConfig = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 6, 5, 4] }) := steps_add tm_5_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_8 35 ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 6, 5, 4] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 5, 4] }) := rfl
  have h5 : steps tm_5_8 210 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 5, 4] }) := steps_add tm_5_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_8 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 5, 4] }) = some ({ st := some 4, left := [6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 6, 5, 4] }) := rfl
  have h6 : steps tm_5_8 245 initConfig = some ({ st := some 4, left := [6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 6, 5, 4] }) := steps_add tm_5_8 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_8 35 ({ st := some 4, left := [6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 6, 5, 4] }) = some ({ st := some 2, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [1, 1, 1, 1, 1, 1, 3, 4] }) := rfl
  have h7 : steps tm_5_8 280 initConfig = some ({ st := some 2, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [1, 1, 1, 1, 1, 1, 3, 4] }) := steps_add tm_5_8 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_5_8 35 ({ st := some 2, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [1, 1, 1, 1, 1, 1, 3, 4] }) = some ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7] }) := rfl
  have h8 : steps tm_5_8 315 initConfig = some ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7] }) := steps_add tm_5_8 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_5_8 35 ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7] }) = some ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h9 : steps tm_5_8 350 initConfig = some ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_8 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_5_8 35 ({ st := some 0, left := [3, 3, 3, 3, 3, 3, 3], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 0, left := [], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h10 : steps tm_5_8 385 initConfig = some ({ st := some 0, left := [], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_8 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_5_8 35 ({ st := some 0, left := [], cur := 3, right := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 2, left := [6], cur := 5, right := [3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h11 : steps tm_5_8 420 initConfig = some ({ st := some 2, left := [6], cur := 5, right := [3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_8 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_5_8 27 ({ st := some 2, left := [6], cur := 5, right := [3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h12 : steps tm_5_8 447 initConfig = some ({ st := some 1, left := [2, 3], cur := 1, right := [1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_8 420 27 initConfig _ _ h11 hstep12
  exact h12

/-! ### BB(10,8) — > f_{ω^ω+2}(28) (`fwpw2_8_blank` @ step 325) -/
def tm_10_8 : TM
  | 0, 0 => some ⟨5, Dir.L, some 9⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨4, Dir.L, some 8⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨5, Dir.L, some 9⟩
  | 0, 6 => some ⟨6, Dir.R, some 3⟩
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
  | 3, 1 => some ⟨6, Dir.R, some 4⟩
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
  | 4, 4 => some ⟨7, Dir.L, some 3⟩
  | 4, 5 => some ⟨6, Dir.L, some 9⟩
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
  | 6, 5 => some ⟨1, Dir.L, some 3⟩
  | 6, 6 => some ⟨2, Dir.L, some 2⟩
  | 6, 7 => some ⟨6, Dir.L, some 2⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 5 => some ⟨1, Dir.R, some 4⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 5 => some ⟨5, Dir.L, some 6⟩
  | 9, 6 => some ⟨5, Dir.L, some 1⟩
  | 9, 7 => some ⟨5, Dir.R, some 9⟩
  | _, _ => none

theorem valid_10_8 : ValidTM 10 8 tm_10_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 6 | 7 => trivial | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 | 6 | 7 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 8 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 10 => rfl

def landmark_10_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_10_8 : steps tm_10_8 325 initConfig = some landmark_10_8 := by
  have h0 : steps tm_10_8 35 initConfig = some ({ st := some 1, left := [], cur := 7, right := [1, 6, 5, 5, 5] }) := rfl
  have hstep1 : steps tm_10_8 35 ({ st := some 1, left := [], cur := 7, right := [1, 6, 5, 5, 5] }) = some ({ st := some 9, left := [5, 6, 6, 5, 7, 7], cur := 6, right := [5, 5] }) := rfl
  have h1 : steps tm_10_8 70 initConfig = some ({ st := some 9, left := [5, 6, 6, 5, 7, 7], cur := 6, right := [5, 5] }) := steps_add tm_10_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_10_8 35 ({ st := some 9, left := [5, 6, 6, 5, 7, 7], cur := 6, right := [5, 5] }) = some ({ st := some 2, left := [6, 7, 7], cur := 5, right := [3, 0, 5, 5, 5, 5, 5] }) := rfl
  have h2 : steps tm_10_8 105 initConfig = some ({ st := some 2, left := [6, 7, 7], cur := 5, right := [3, 0, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_10_8 35 ({ st := some 2, left := [6, 7, 7], cur := 5, right := [3, 0, 5, 5, 5, 5, 5] }) = some ({ st := some 3, left := [7], cur := 7, right := [1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h3 : steps tm_10_8 140 initConfig = some ({ st := some 3, left := [7], cur := 7, right := [1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_10_8 35 ({ st := some 3, left := [7], cur := 7, right := [1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 1, left := [], cur := 0, right := [7, 1, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h4 : steps tm_10_8 175 initConfig = some ({ st := some 1, left := [], cur := 0, right := [7, 1, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_10_8 35 ({ st := some 1, left := [], cur := 0, right := [7, 1, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 9, left := [6, 6, 5, 7], cur := 7, right := [6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h5 : steps tm_10_8 210 initConfig = some ({ st := some 9, left := [6, 6, 5, 7], cur := 7, right := [6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_10_8 35 ({ st := some 9, left := [6, 6, 5, 7], cur := 7, right := [6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 1, left := [], cur := 0, right := [1, 3, 1, 3, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h6 : steps tm_10_8 245 initConfig = some ({ st := some 1, left := [], cur := 0, right := [1, 3, 1, 3, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_10_8 35 ({ st := some 1, left := [], cur := 0, right := [1, 3, 1, 3, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 0, left := [7], cur := 1, right := [2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h7 : steps tm_10_8 280 initConfig = some ({ st := some 0, left := [7], cur := 1, right := [2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_10_8 35 ({ st := some 0, left := [7], cur := 1, right := [2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 9, left := [], cur := 3, right := [2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h8 : steps tm_10_8 315 initConfig = some ({ st := some 9, left := [], cur := 3, right := [2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_10_8 10 ({ st := some 9, left := [], cur := 3, right := [2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h9 : steps tm_10_8 325 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_10_8 315 10 initConfig _ _ h8 hstep9
  exact h9

/-! ### BB(11,8) — > f_{ω^ω+3}(11) (`fwpw3_8_blank` @ step 200) -/
def tm_11_8 : TM
  | 0, 0 => some ⟨2, Dir.L, some 2⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨6, Dir.L, some 4⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨6, Dir.R, some 1⟩
  | 0, 6 => some ⟨6, Dir.L, some 0⟩
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
  | 4, 5 => some ⟨6, Dir.R, some 2⟩
  | 4, 6 => some ⟨6, Dir.L, some 9⟩
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
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 5 => some ⟨6, Dir.R, some 8⟩
  | 8, 6 => some ⟨5, Dir.R, some 0⟩
  | 8, 7 => some ⟨5, Dir.R, some 9⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨6, Dir.R, some 4⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 5 => some ⟨7, Dir.R, some 4⟩
  | 9, 6 => some ⟨3, Dir.L, some 8⟩
  | 9, 7 => some ⟨6, Dir.R, some 7⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨2, Dir.L, some 7⟩
  | 10, 7 => some ⟨3, Dir.R, some 4⟩
  | _, _ => none

theorem valid_11_8 : ValidTM 11 8 tm_11_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 7 => trivial | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 10 => match sym with | 0 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 8 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 11 => rfl

def landmark_11_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }
theorem reaches_landmark_11_8 : steps tm_11_8 200 initConfig = some landmark_11_8 := by
  have h0 : steps tm_11_8 35 initConfig = some ({ st := some 2, left := [6, 3, 7, 7], cur := 2, right := [5, 6] }) := rfl
  have hstep1 : steps tm_11_8 35 ({ st := some 2, left := [6, 3, 7, 7], cur := 2, right := [5, 6] }) = some ({ st := some 0, left := [6, 6, 6, 5, 6, 7, 7], cur := 3, right := [2] }) := rfl
  have h1 : steps tm_11_8 70 initConfig = some ({ st := some 0, left := [6, 6, 6, 5, 6, 7, 7], cur := 3, right := [2] }) := steps_add tm_11_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_11_8 35 ({ st := some 0, left := [6, 6, 6, 5, 6, 7, 7], cur := 3, right := [2] }) = some ({ st := some 2, left := [7], cur := 7, right := [3, 3, 3, 3, 6, 6, 6, 6] }) := rfl
  have h2 : steps tm_11_8 105 initConfig = some ({ st := some 2, left := [7], cur := 7, right := [3, 3, 3, 3, 6, 6, 6, 6] }) := steps_add tm_11_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_11_8 35 ({ st := some 2, left := [7], cur := 7, right := [3, 3, 3, 3, 6, 6, 6, 6] }) = some ({ st := some 8, left := [6, 7], cur := 3, right := [6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h3 : steps tm_11_8 140 initConfig = some ({ st := some 8, left := [6, 7], cur := 3, right := [6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_11_8 35 ({ st := some 8, left := [6, 7], cur := 3, right := [6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 0, left := [5], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h4 : steps tm_11_8 175 initConfig = some ({ st := some 0, left := [5], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_8 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_11_8 25 ({ st := some 0, left := [5], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h5 : steps tm_11_8 200 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_8 175 25 initConfig _ _ h4 hstep5
  exact h5

/-! ### BB(12,8) — > f_{ω^ω+4}(5) (`fwpw4_8_blank` @ step 74) -/
def tm_12_8 : TM
  | 0, 0 => some ⟨7, Dir.L, some 10⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨0, Dir.L, some 4⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨2, Dir.R, some 1⟩
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
  | 6, 7 => some ⟨0, Dir.L, some 3⟩
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
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨7, Dir.L, some 5⟩
  | 10, 7 => some ⟨0, Dir.L, some 0⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | _, _ => none

theorem valid_12_8 : ValidTM 12 8 tm_12_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 10 => match sym with | 0 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 8 => omega
    | 11 => match sym with | 0 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 7 => trivial | _ + 8 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 12 => rfl

def landmark_12_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }
theorem reaches_landmark_12_8 : steps tm_12_8 74 initConfig = some landmark_12_8 := by
  have h0 : steps tm_12_8 35 initConfig = some ({ st := some 0, left := [7, 7, 7, 7, 3, 7], cur := 0, right := [] }) := rfl
  have hstep1 : steps tm_12_8 35 ({ st := some 0, left := [7, 7, 7, 7, 3, 7], cur := 0, right := [] }) = some ({ st := some 4, left := [3], cur := 2, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }) := rfl
  have h1 : steps tm_12_8 70 initConfig = some ({ st := some 4, left := [3], cur := 2, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }) := steps_add tm_12_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_8 4 ({ st := some 4, left := [3], cur := 2, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }) := rfl
  have h2 : steps tm_12_8 74 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7] }) := steps_add tm_12_8 70 4 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(13,8) — > f_{ω^ω+4}(9) (`fwpw4_8_blank` @ step 124) -/
def tm_13_8 : TM
  | 0, 0 => some ⟨7, Dir.L, some 8⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
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
  | 8, 7 => some ⟨4, Dir.R, some 9⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 7 => some ⟨3, Dir.L, some 11⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨3, Dir.R, some 12⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 12, 0 => some ⟨3, Dir.R, some 4⟩
  | 12, 1 => some ⟨1, Dir.L, some 6⟩
  | 12, 3 => some ⟨7, Dir.L, some 12⟩
  | 12, 4 => some ⟨1, Dir.R, some 4⟩
  | 12, 7 => some ⟨4, Dir.R, some 9⟩
  | _, _ => none

theorem valid_13_8 : ValidTM 13 8 tm_13_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 2 | 5 | 6 => trivial | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 10 => match sym with | 0 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 1 | 4 | 6 | 7 => trivial | _ + 8 => omega
    | 11 => match sym with | 0 | 2 | 3 | 4 | 6 => exact ⟨by decide, by decide⟩ | 1 | 5 | 7 => trivial | _ + 8 => omega
    | 12 => match sym with | 0 | 1 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 2 | 5 | 6 => trivial | _ + 8 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 13 => rfl

def landmark_13_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem reaches_landmark_13_8 : steps tm_13_8 124 initConfig = some landmark_13_8 := by
  have h0 : steps tm_13_8 35 initConfig = some ({ st := some 12, left := [7, 3, 4, 3], cur := 3, right := [7, 7, 7, 7] }) := rfl
  have hstep1 : steps tm_13_8 35 ({ st := some 12, left := [7, 3, 4, 3], cur := 3, right := [7, 7, 7, 7] }) = some ({ st := some 9, left := [4, 7, 7, 7, 7, 1, 3], cur := 7, right := [7, 7, 7, 7] }) := rfl
  have h1 : steps tm_13_8 70 initConfig = some ({ st := some 9, left := [4, 7, 7, 7, 7, 1, 3], cur := 7, right := [7, 7, 7, 7] }) := steps_add tm_13_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_13_8 35 ({ st := some 9, left := [4, 7, 7, 7, 7, 1, 3], cur := 7, right := [7, 7, 7, 7] }) = some ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h2 : steps tm_13_8 105 initConfig = some ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_13_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_13_8 19 ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h3 : steps tm_13_8 124 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_13_8 105 19 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(14,8) — > f_{ω^ω+5}(6) (`fwpw5_8` @ step 167) -/
def tm_14_8 : TM
  | 0, 0 => some ⟨6, Dir.L, some 8⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨7, Dir.R, some 13⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨1, Dir.R, some 3⟩
  | 0, 6 => some ⟨4, Dir.R, some 3⟩
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
  | 3, 1 => some ⟨2, Dir.L, some 4⟩
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
  | 4, 4 => some ⟨5, Dir.L, some 10⟩
  | 4, 5 => some ⟨2, Dir.R, some 7⟩
  | 4, 6 => some ⟨5, Dir.R, some 9⟩
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
  | 6, 5 => some ⟨6, Dir.L, some 0⟩
  | 6, 6 => some ⟨4, Dir.R, some 1⟩
  | 6, 7 => some ⟨5, Dir.R, some 10⟩
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
  | 8, 4 => some ⟨7, Dir.L, some 12⟩
  | 8, 5 => some ⟨1, Dir.L, some 0⟩
  | 8, 6 => some ⟨6, Dir.R, some 9⟩
  | 8, 7 => some ⟨1, Dir.R, some 12⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨4, Dir.L, some 13⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨1, Dir.R, some 12⟩
  | 9, 5 => some ⟨3, Dir.R, some 4⟩
  | 9, 6 => some ⟨6, Dir.R, some 7⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨6, Dir.R, some 3⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨6, Dir.R, some 9⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨0, Dir.L, some 8⟩
  | 10, 7 => some ⟨4, Dir.R, some 9⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨3, Dir.L, some 5⟩
  | 11, 5 => some ⟨1, Dir.R, some 0⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨0, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨3, Dir.L, some 6⟩
  | 12, 2 => some ⟨0, Dir.L, some 6⟩
  | 12, 3 => some ⟨7, Dir.L, some 11⟩
  | 12, 4 => some ⟨6, Dir.R, some 4⟩
  | 12, 6 => some ⟨7, Dir.L, some 13⟩
  | 12, 7 => some ⟨6, Dir.L, some 11⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 1 => some ⟨3, Dir.R, some 11⟩
  | 13, 2 => some ⟨7, Dir.L, some 13⟩
  | 13, 3 => some ⟨7, Dir.L, some 13⟩
  | 13, 6 => some ⟨3, Dir.L, some 0⟩
  | 13, 7 => some ⟨2, Dir.R, some 7⟩
  | _, _ => none

theorem valid_14_8 : ValidTM 14 8 tm_14_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 7 => trivial | _ + 8 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 11 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 8 => omega
    | 12 => match sym with | 1 | 2 | 3 | 4 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 5 => trivial | _ + 8 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 8 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 14 => rfl

def landmark_14_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 6, 6, 6, 6, 6, 6] }
theorem reaches_landmark_14_8 : steps tm_14_8 167 initConfig = some landmark_14_8 := by
  have h0 : steps tm_14_8 35 initConfig = some ({ st := some 0, left := [3], cur := 2, right := [3, 4, 4, 1] }) := rfl
  have hstep1 : steps tm_14_8 35 ({ st := some 0, left := [3], cur := 2, right := [3, 4, 4, 1] }) = some ({ st := some 7, left := [6, 2, 2, 3], cur := 2, right := [2, 2] }) := rfl
  have h1 : steps tm_14_8 70 initConfig = some ({ st := some 7, left := [6, 2, 2, 3], cur := 2, right := [2, 2] }) := steps_add tm_14_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_8 35 ({ st := some 7, left := [6, 2, 2, 3], cur := 2, right := [2, 2] }) = some ({ st := some 6, left := [7, 7, 3, 3], cur := 1, right := [0, 1, 4] }) := rfl
  have h2 : steps tm_14_8 105 initConfig = some ({ st := some 6, left := [7, 7, 3, 3], cur := 1, right := [0, 1, 4] }) := steps_add tm_14_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_8 35 ({ st := some 6, left := [7, 7, 3, 3], cur := 1, right := [0, 1, 4] }) = some ({ st := some 8, left := [7, 3, 3], cur := 1, right := [6, 6, 6, 6, 6, 6] }) := rfl
  have h3 : steps tm_14_8 140 initConfig = some ({ st := some 8, left := [7, 3, 3], cur := 1, right := [6, 6, 6, 6, 6, 6] }) := steps_add tm_14_8 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_8 27 ({ st := some 8, left := [7, 3, 3], cur := 1, right := [6, 6, 6, 6, 6, 6] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 6, 6, 6, 6, 6, 6] }) := rfl
  have h4 : steps tm_14_8 167 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 6, 6, 6, 6, 6, 6] }) := steps_add tm_14_8 140 27 initConfig _ _ h3 hstep4
  exact h4

/-! ### BB(15,8) — > f_{ω^ω+6}(8) (`fwpw6_8` @ step 106) -/
def tm_15_8 : TM
  | 0, 0 => some ⟨6, Dir.L, some 3⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨2, Dir.L, some 8⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
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
  | 4, 6 => some ⟨7, Dir.R, some 2⟩
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
  | 8, 4 => some ⟨7, Dir.L, some 14⟩
  | 8, 5 => some ⟨0, Dir.R, some 2⟩
  | 8, 7 => some ⟨4, Dir.R, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨7, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 7 => some ⟨2, Dir.L, some 1⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 5 => some ⟨6, Dir.L, some 14⟩
  | 12, 6 => some ⟨7, Dir.L, some 13⟩
  | 12, 7 => some ⟨6, Dir.L, some 11⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 2 => some ⟨7, Dir.L, some 13⟩
  | 13, 3 => some ⟨7, Dir.L, some 13⟩
  | 13, 6 => some ⟨2, Dir.R, some 14⟩
  | 13, 7 => some ⟨2, Dir.R, some 7⟩
  | 14, 0 => some ⟨3, Dir.R, some 13⟩
  | 14, 2 => some ⟨6, Dir.L, some 14⟩
  | 14, 3 => some ⟨6, Dir.L, some 14⟩
  | 14, 4 => some ⟨2, Dir.L, some 8⟩
  | 14, 6 => some ⟨2, Dir.R, some 12⟩
  | 14, 7 => some ⟨7, Dir.L, some 8⟩
  | _, _ => none

theorem valid_15_8 : ValidTM 15 8 tm_15_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 | 7 => trivial | _ + 8 => omega
    | 10 => match sym with | 0 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 1 | 6 => trivial | _ + 8 => omega
    | 11 => match sym with | 0 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 7 => trivial | _ + 8 => omega
    | 12 => match sym with | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 1 | 2 | 3 | 4 => trivial | _ + 8 => omega
    | 13 => match sym with | 0 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 => trivial | _ + 8 => omega
    | 14 => match sym with | 0 | 2 | 3 | 4 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 5 => trivial | _ + 8 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 15 => rfl

def landmark_15_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_15_8 : steps tm_15_8 106 initConfig = some landmark_15_8 := by
  have h0 : steps tm_15_8 35 initConfig = some ({ st := some 10, left := [2, 4, 7], cur := 3, right := [5, 5, 5, 5] }) := rfl
  have hstep1 : steps tm_15_8 35 ({ st := some 10, left := [2, 4, 7], cur := 3, right := [5, 5, 5, 5] }) = some ({ st := some 10, left := [2, 3, 4, 2, 4], cur := 2, right := [5, 5, 5, 5, 5] }) := rfl
  have h1 : steps tm_15_8 70 initConfig = some ({ st := some 10, left := [2, 3, 4, 2, 4], cur := 2, right := [5, 5, 5, 5, 5] }) := steps_add tm_15_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_15_8 35 ({ st := some 10, left := [2, 3, 4, 2, 4], cur := 2, right := [5, 5, 5, 5, 5] }) = some ({ st := some 8, left := [3], cur := 2, right := [1, 4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h2 : steps tm_15_8 105 initConfig = some ({ st := some 8, left := [3], cur := 2, right := [1, 4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_15_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_15_8 1 ({ st := some 8, left := [3], cur := 2, right := [1, 4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h3 : steps tm_15_8 106 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 2, 2, 7, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_15_8 105 1 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(16,8) — > f_{ω^ω+7}(8) (`fwpw7_8` @ step 138) -/
def tm_16_8 : TM
  | 0, 0 => some ⟨5, Dir.L, some 13⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 6 => some ⟨3, Dir.L, some 1⟩
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
  | 3, 1 => some ⟨1, Dir.R, some 12⟩
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
  | 6, 4 => some ⟨2, Dir.R, some 11⟩
  | 6, 5 => some ⟨2, Dir.R, some 5⟩
  | 6, 7 => some ⟨1, Dir.R, some 9⟩
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
  | 8, 5 => some ⟨7, Dir.R, some 11⟩
  | 8, 7 => some ⟨2, Dir.L, some 13⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨7, Dir.L, some 8⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨3, Dir.R, some 10⟩
  | 9, 5 => some ⟨0, Dir.R, some 6⟩
  | 9, 6 => some ⟨5, Dir.R, some 4⟩
  | 9, 7 => some ⟨6, Dir.R, some 3⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨1, Dir.R, some 8⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨3, Dir.L, some 14⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨1, Dir.R, some 11⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨5, Dir.L, some 13⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 5 => some ⟨4, Dir.R, some 14⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨4, Dir.R, some 15⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨1, Dir.R, some 10⟩
  | 12, 2 => some ⟨5, Dir.L, some 15⟩
  | 12, 4 => some ⟨6, Dir.R, some 11⟩
  | 12, 5 => some ⟨6, Dir.L, some 14⟩
  | 12, 6 => some ⟨7, Dir.L, some 13⟩
  | 12, 7 => some ⟨6, Dir.L, some 11⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 1 => some ⟨0, Dir.R, some 6⟩
  | 13, 2 => some ⟨7, Dir.L, some 13⟩
  | 13, 3 => some ⟨7, Dir.L, some 13⟩
  | 13, 5 => some ⟨1, Dir.R, some 0⟩
  | 13, 6 => some ⟨2, Dir.R, some 14⟩
  | 13, 7 => some ⟨2, Dir.R, some 7⟩
  | 14, 0 => some ⟨3, Dir.R, some 13⟩
  | 14, 1 => some ⟨3, Dir.R, some 6⟩
  | 14, 2 => some ⟨6, Dir.L, some 14⟩
  | 14, 3 => some ⟨6, Dir.L, some 14⟩
  | 14, 4 => some ⟨1, Dir.R, some 2⟩
  | 14, 5 => some ⟨2, Dir.R, some 15⟩
  | 14, 6 => some ⟨2, Dir.R, some 12⟩
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 1 => some ⟨6, Dir.R, some 13⟩
  | 15, 2 => some ⟨5, Dir.L, some 15⟩
  | 15, 3 => some ⟨5, Dir.L, some 15⟩
  | 15, 5 => some ⟨2, Dir.R, some 12⟩
  | 15, 6 => some ⟨5, Dir.R, some 4⟩
  | _, _ => none

theorem valid_16_8 : ValidTM 16 8 tm_16_8 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 3 | 4 | 6 | 7 => exact ⟨by decide, by decide⟩ | 2 | 5 => trivial | _ + 8 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 8 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 8 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 8 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 5 | 7 => exact ⟨by decide, by decide⟩ | 4 | 6 => trivial | _ + 8 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | _ + 8 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 7 => trivial | _ + 8 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 12 => match sym with | 1 | 2 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 3 => trivial | _ + 8 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 8 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 7 => trivial | _ + 8 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 => exact ⟨by decide, by decide⟩ | 4 | 7 => trivial | _ + 8 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _ + 8 => rfl
    | _ + 16 => rfl

def landmark_16_8 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_16_8 : steps tm_16_8 138 initConfig = some landmark_16_8 := by
  have h0 : steps tm_16_8 35 initConfig = some ({ st := some 13, left := [4, 1, 2, 2], cur := 7, right := [5, 2] }) := rfl
  have hstep1 : steps tm_16_8 35 ({ st := some 13, left := [4, 1, 2, 2], cur := 7, right := [5, 2] }) = some ({ st := some 1, left := [3, 4, 1, 2, 2, 2, 2], cur := 1, right := [2, 2] }) := rfl
  have h1 : steps tm_16_8 70 initConfig = some ({ st := some 1, left := [3, 4, 1, 2, 2, 2, 2], cur := 1, right := [2, 2] }) := steps_add tm_16_8 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_8 35 ({ st := some 1, left := [3, 4, 1, 2, 2, 2, 2], cur := 1, right := [2, 2] }) = some ({ st := some 9, left := [2, 2, 2, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h2 : steps tm_16_8 105 initConfig = some ({ st := some 9, left := [2, 2, 2, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_16_8 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_8 33 ({ st := some 9, left := [2, 2, 2, 2], cur := 1, right := [2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h3 : steps tm_16_8 138 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 6, 7, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_16_8 105 33 initConfig _ _ h2 hstep3
  exact h3

end BB.Champions2026_11_21.S8
