/-
  BB/Champions2026_11_21_S7.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 3 7-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S7
open BB

/-! ### BB(6,7) — > f_{ω×2+1}(f_{ω+1}^3(2)) (`fwm21tfw1_7` @ step 51) -/
def tm_6_7 : TM
  | 0, 0 => some ⟨5, Dir.L, some 5⟩
  | 0, 1 => some ⟨6, Dir.L, some 0⟩
  | 0, 2 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨4, Dir.R, some 5⟩
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
  | 5, 0 => some ⟨3, Dir.L, some 2⟩
  | 5, 1 => some ⟨3, Dir.R, some 0⟩
  | 5, 3 => some ⟨3, Dir.L, some 3⟩
  | 5, 4 => some ⟨3, Dir.L, some 0⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.R, some 4⟩
  | _, _ => none

theorem valid_6_7 : ValidTM 6 7 tm_6_7 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 2 => trivial | _ + 7 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 6 => rfl

def landmark_6_7 : Config := { st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] }
theorem reaches_landmark_6_7 : steps tm_6_7 51 initConfig = some landmark_6_7 := by
  have h0 : steps tm_6_7 35 initConfig = some ({ st := some 3, left := [], cur := 6, right := [4, 6, 4, 4, 3, 5] }) := rfl
  have hstep1 : steps tm_6_7 16 ({ st := some 3, left := [], cur := 6, right := [4, 6, 4, 4, 3, 5] }) = some ({ st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] }) := rfl
  have h1 : steps tm_6_7 51 initConfig = some ({ st := some 1, left := [2, 3], cur := 1, right := [1, 2, 4, 4, 3, 5] }) := steps_add tm_6_7 35 16 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(13,7) — > f_{ω^ω+2}(8) (`fwpw2_6` @ step 129) -/
def tm_13_7 : TM
  | 0, 0 => some ⟨1, Dir.L, some 7⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 5 => some ⟨5, Dir.L, some 2⟩
  | 0, 6 => some ⟨3, Dir.L, some 9⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 7⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 5 => some ⟨2, Dir.L, some 12⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨5, Dir.L, some 4⟩
  | 2, 5 => some ⟨1, Dir.L, some 1⟩
  | 2, 6 => some ⟨5, Dir.R, some 10⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨6, Dir.L, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨5, Dir.L, some 12⟩
  | 4, 5 => some ⟨6, Dir.L, some 0⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 5, 6 => some ⟨4, Dir.L, some 5⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨3, Dir.L, some 10⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 7, 6 => some ⟨2, Dir.R, some 4⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 8, 6 => some ⟨4, Dir.R, some 3⟩
  | 9, 0 => some ⟨6, Dir.L, some 5⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 9, 6 => some ⟨2, Dir.R, some 3⟩
  | 10, 0 => some ⟨6, Dir.R, some 8⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 0⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 6 => some ⟨6, Dir.L, some 5⟩
  | 12, 0 => some ⟨0, Dir.R, some 2⟩
  | 12, 1 => some ⟨6, Dir.R, some 1⟩
  | 12, 2 => some ⟨2, Dir.L, some 12⟩
  | 12, 3 => some ⟨2, Dir.L, some 12⟩
  | _, _ => none

theorem valid_13_7 : ValidTM 13 7 tm_13_7 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 7 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 6 => trivial | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 6 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 7 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 7 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 6 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 7 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 6 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 7 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 6 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 7 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 7 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 7 => omega
    | 12 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 7 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 13 => rfl

def landmark_13_7 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_13_7 : steps tm_13_7 129 initConfig = some landmark_13_7 := by
  have h0 : steps tm_13_7 35 initConfig = some ({ st := some 2, left := [], cur := 4, right := [3, 3, 1, 1, 0, 4] }) := rfl
  have hstep1 : steps tm_13_7 35 ({ st := some 2, left := [], cur := 4, right := [3, 3, 1, 1, 0, 4] }) = some ({ st := some 0, left := [1, 1, 1, 3, 3], cur := 2, right := [1, 1, 1, 0, 4] }) := rfl
  have h1 : steps tm_13_7 70 initConfig = some ({ st := some 0, left := [1, 1, 1, 3, 3], cur := 2, right := [1, 1, 1, 0, 4] }) := steps_add tm_13_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_13_7 35 ({ st := some 0, left := [1, 1, 1, 3, 3], cur := 2, right := [1, 1, 1, 0, 4] }) = some ({ st := some 1, left := [6, 1, 3, 3], cur := 2, right := [5, 5, 5, 5, 5, 5] }) := rfl
  have h2 : steps tm_13_7 105 initConfig = some ({ st := some 1, left := [6, 1, 3, 3], cur := 2, right := [5, 5, 5, 5, 5, 5] }) := steps_add tm_13_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_13_7 24 ({ st := some 1, left := [6, 1, 3, 3], cur := 2, right := [5, 5, 5, 5, 5, 5] }) = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5, 5, 5] }) := rfl
  have h3 : steps tm_13_7 129 initConfig = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5, 5, 5] }) := steps_add tm_13_7 105 24 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(14,7) — > f_{ω^ω+3}(22) (`fwpw3_7` @ step 629) -/
def tm_14_7 : TM
  | 0, 0 => some ⟨0, Dir.L, some 10⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 6 => some ⟨4, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 7⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 5 => some ⟨2, Dir.L, some 12⟩
  | 1, 6 => some ⟨5, Dir.L, some 13⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 7⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 5 => some ⟨2, Dir.L, some 10⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 5 => some ⟨1, Dir.L, some 9⟩
  | 4, 6 => some ⟨5, Dir.R, some 3⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 5, 5 => some ⟨6, Dir.L, some 5⟩
  | 5, 6 => some ⟨6, Dir.L, some 13⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨6, Dir.L, some 0⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨0, Dir.L, some 6⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 5 => some ⟨6, Dir.L, some 4⟩
  | 11, 0 => some ⟨3, Dir.R, some 0⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨0, Dir.R, some 2⟩
  | 12, 2 => some ⟨2, Dir.L, some 12⟩
  | 12, 3 => some ⟨2, Dir.L, some 12⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 1 => some ⟨5, Dir.R, some 3⟩
  | 13, 2 => some ⟨5, Dir.L, some 13⟩
  | 13, 3 => some ⟨5, Dir.L, some 13⟩
  | 13, 4 => some ⟨6, Dir.L, some 10⟩
  | 13, 5 => some ⟨2, Dir.R, some 1⟩
  | _, _ => none

theorem valid_14_7 : ValidTM 14 7 tm_14_7 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 7 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 7 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 | 6 => trivial | _ + 7 => omega
    | 3 => match sym with | 0 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 1 | 4 | 6 => trivial | _ + 7 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 7 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | _ + 7 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 7 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 | 5 | 6 => trivial | _ + 7 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 7 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 7 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 | 6 => trivial | _ + 7 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 => trivial | _ + 7 => omega
    | 12 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 => trivial | _ + 7 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 7 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega | _ + 7 => rfl
    | _ + 14 => rfl

def landmark_14_7 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }
theorem reaches_landmark_14_7 : steps tm_14_7 629 initConfig = some landmark_14_7 := by
  have h0 : steps tm_14_7 35 initConfig = some ({ st := some 9, left := [1, 2, 2], cur := 0, right := [3, 5, 5] }) := rfl
  have hstep1 : steps tm_14_7 35 ({ st := some 9, left := [1, 2, 2], cur := 0, right := [3, 5, 5] }) = some ({ st := some 1, left := [2, 3, 3, 3, 3], cur := 3, right := [4, 1, 0, 5] }) := rfl
  have h1 : steps tm_14_7 70 initConfig = some ({ st := some 1, left := [2, 3, 3, 3, 3], cur := 3, right := [4, 1, 0, 5] }) := steps_add tm_14_7 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_7 35 ({ st := some 1, left := [2, 3, 3, 3, 3], cur := 3, right := [4, 1, 0, 5] }) = some ({ st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 0, 5] }) := rfl
  have h2 : steps tm_14_7 105 initConfig = some ({ st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 0, 5] }) := steps_add tm_14_7 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_7 35 ({ st := some 0, left := [3], cur := 2, right := [1, 1, 1, 1, 1, 1, 3, 0, 5] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2], cur := 4, right := [4, 4, 4, 4, 1, 5] }) := rfl
  have h3 : steps tm_14_7 140 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2], cur := 4, right := [4, 4, 4, 4, 1, 5] }) := steps_add tm_14_7 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_7 35 ({ st := some 6, left := [2, 2, 2, 2, 2], cur := 4, right := [4, 4, 4, 4, 1, 5] }) = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 5] }) := rfl
  have h4 : steps tm_14_7 175 initConfig = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 5] }) := steps_add tm_14_7 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_14_7 35 ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 5] }) = some ({ st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 5] }) := rfl
  have h5 : steps tm_14_7 210 initConfig = some ({ st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 5] }) := steps_add tm_14_7 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_14_7 35 ({ st := some 0, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 5] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 5] }) := rfl
  have h6 : steps tm_14_7 245 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 5] }) := steps_add tm_14_7 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_14_7 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 5] }) = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5] }) := rfl
  have h7 : steps tm_14_7 280 initConfig = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5] }) := steps_add tm_14_7 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_14_7 35 ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5] }) = some ({ st := some 0, left := [3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5] }) := rfl
  have h8 : steps tm_14_7 315 initConfig = some ({ st := some 0, left := [3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5] }) := steps_add tm_14_7 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_14_7 35 ({ st := some 0, left := [3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5] }) = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5] }) := rfl
  have h9 : steps tm_14_7 350 initConfig = some ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5] }) := steps_add tm_14_7 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_14_7 35 ({ st := some 11, left := [], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5] }) = some ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 5] }) := rfl
  have h10 : steps tm_14_7 385 initConfig = some ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 5] }) := steps_add tm_14_7 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_14_7 35 ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 3, 5] }) = some ({ st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5] }) := rfl
  have h11 : steps tm_14_7 420 initConfig = some ({ st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5] }) := steps_add tm_14_7 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_14_7 35 ({ st := some 0, left := [3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 4, 6] }) := rfl
  have h12 : steps tm_14_7 455 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 4, 6] }) := steps_add tm_14_7 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_14_7 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 4, 6] }) = some ({ st := some 9, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 4, 6] }) := rfl
  have h13 : steps tm_14_7 490 initConfig = some ({ st := some 9, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 4, 6] }) := steps_add tm_14_7 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_14_7 35 ({ st := some 9, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 4, 6] }) = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h14 : steps tm_14_7 525 initConfig = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_14_7 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_14_7 35 ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h15 : steps tm_14_7 560 initConfig = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_14_7 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_14_7 35 ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 10, left := [2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h16 : steps tm_14_7 595 initConfig = some ({ st := some 10, left := [2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_14_7 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_14_7 34 ({ st := some 10, left := [2, 2], cur := 2, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h17 : steps tm_14_7 629 initConfig = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_14_7 595 34 initConfig _ _ h16 hstep17
  exact h17

end BB.Champions2026_11_21.S7
