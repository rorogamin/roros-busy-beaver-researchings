/-
  BB/Champions2026_11_21_S4.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 8 4-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S4
open BB

/-! ### BB(10,4) — > f_{ω^2}^3(4) (`fwp21_4` @ step 31) -/
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
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | _ + 10 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 10 => rfl

def landmark_10_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 3, 3, 0, 0, 0, 1] }
theorem reaches_landmark_10_4 : steps tm_10_4 31 initConfig = some landmark_10_4 := rfl

/-! ### BB(12,4) — > f_{ω^2+2}(f_ω(2)) (`fwp22fw_4` @ step 9) -/
def tm_12_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨2, Dir.L, some 11⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.L, some 6⟩
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
  | _, _ => none

theorem valid_12_4 : ValidTM 12 4 tm_12_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | 3 => trivial | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | 3 => trivial | _ + 4 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 12 => rfl

def landmark_12_4 : Config := { st := some 6, left := [1, 1], cur := 1, right := [1] }
theorem reaches_landmark_12_4 : steps tm_12_4 9 initConfig = some landmark_12_4 := rfl

/-! ### BB(13,4) — > f_{ω^2+3}(f_ω(2)) (`fwp23fw_4` @ step 9) -/
def tm_13_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨3, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.L, some 6⟩
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
  | 8, 3 => some ⟨1, Dir.R, none⟩
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
  | 12, 0 => some ⟨0, Dir.L, some 11⟩
  | 12, 1 => some ⟨2, Dir.L, some 12⟩
  | 12, 2 => some ⟨2, Dir.L, some 12⟩
  | _, _ => none

theorem valid_13_4 : ValidTM 13 4 tm_13_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | 3 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | 3 => trivial | _ + 4 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 13 => rfl

def landmark_13_4 : Config := { st := some 6, left := [1, 1], cur := 1, right := [1] }
theorem reaches_landmark_13_4 : steps tm_13_4 9 initConfig = some landmark_13_4 := rfl

/-! ### BB(14,4) — > f_{ω^2+4}(7) (`fwp24_4` @ step 58) -/
def tm_14_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨3, Dir.L, some 12⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨2, Dir.L, some 5⟩
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
  | 12, 1 => some ⟨3, Dir.L, some 12⟩
  | 12, 2 => some ⟨3, Dir.L, some 12⟩
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
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 14 => rfl

def landmark_14_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem reaches_landmark_14_4 : steps tm_14_4 58 initConfig = some landmark_14_4 := by
  have h0 : steps tm_14_4 35 initConfig = some ({ st := some 4, left := [], cur := 0, right := [1, 1, 1, 1, 1, 2] }) := rfl
  have hstep1 : steps tm_14_4 23 ({ st := some 4, left := [], cur := 0, right := [1, 1, 1, 1, 1, 2] }) = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h1 : steps tm_14_4 58 initConfig = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_14_4 35 23 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(15,4) — > f_{ω^2+5}(3) (`fwp25_4` @ step 17) -/
def tm_15_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨2, Dir.L, some 12⟩
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
  | 12, 1 => some ⟨2, Dir.L, some 8⟩
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
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => trivial | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 15 => rfl

def landmark_15_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 3, 2, 2, 2] }
theorem reaches_landmark_15_4 : steps tm_15_4 17 initConfig = some landmark_15_4 := rfl

/-! ### BB(16,4) — > f_{ω^2+6}(1) (`fwp26_4` @ step 303) -/
def tm_16_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨1, Dir.L, some 15⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.L, some 6⟩
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
  | _, _ => none

theorem valid_16_4 : ValidTM 16 4 tm_16_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 16 => rfl

def landmark_16_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }
theorem reaches_landmark_16_4 : steps tm_16_4 303 initConfig = some landmark_16_4 := by
  have h0 : steps tm_16_4 35 initConfig = some ({ st := some 2, left := [1], cur := 1, right := [1, 2, 1, 2, 1] }) := rfl
  have hstep1 : steps tm_16_4 35 ({ st := some 2, left := [1], cur := 1, right := [1, 2, 1, 2, 1] }) = some ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) := rfl
  have h1 : steps tm_16_4 70 initConfig = some ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) := steps_add tm_16_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_4 35 ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) = some ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) := rfl
  have h2 : steps tm_16_4 105 initConfig = some ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) := steps_add tm_16_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_4 35 ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) = some ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) := rfl
  have h3 : steps tm_16_4 140 initConfig = some ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) := steps_add tm_16_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_4 35 ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) = some ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) := rfl
  have h4 : steps tm_16_4 175 initConfig = some ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) := steps_add tm_16_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_4 35 ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) = some ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) := rfl
  have h5 : steps tm_16_4 210 initConfig = some ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) := steps_add tm_16_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_16_4 35 ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) = some ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) := rfl
  have h6 : steps tm_16_4 245 initConfig = some ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) := steps_add tm_16_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_16_4 35 ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) = some ({ st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2, 1] }) := rfl
  have h7 : steps tm_16_4 280 initConfig = some ({ st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2, 1] }) := steps_add tm_16_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_16_4 23 ({ st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [2, 2, 1] }) = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := rfl
  have h8 : steps tm_16_4 303 initConfig = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] }) := steps_add tm_16_4 280 23 initConfig _ _ h7 hstep8
  exact h8

/-! ### BB(17,4) — > f_{ω^2+6}(17) (`fwp26_4` @ step 304) -/
def tm_17_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨1, Dir.L, some 16⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨1, Dir.L, some 6⟩
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
  | 16, 0 => some ⟨1, Dir.L, some 15⟩
  | 16, 1 => some ⟨1, Dir.L, some 16⟩
  | 16, 2 => some ⟨1, Dir.L, some 16⟩
  | _, _ => none

theorem valid_17_4 : ValidTM 17 4 tm_17_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 16 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | 3 => trivial | _ + 4 => omega
    | _ + 17 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 16 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 17 => rfl

def landmark_17_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }
theorem reaches_landmark_17_4 : steps tm_17_4 304 initConfig = some landmark_17_4 := by
  have h0 : steps tm_17_4 35 initConfig = some ({ st := some 2, left := [1], cur := 1, right := [1, 2, 1, 2, 1] }) := rfl
  have hstep1 : steps tm_17_4 35 ({ st := some 2, left := [1], cur := 1, right := [1, 2, 1, 2, 1] }) = some ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) := rfl
  have h1 : steps tm_17_4 70 initConfig = some ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) := steps_add tm_17_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_17_4 35 ({ st := some 0, left := [1, 1, 1], cur := 2, right := [1, 1, 1, 2] }) = some ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) := rfl
  have h2 : steps tm_17_4 105 initConfig = some ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) := steps_add tm_17_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_17_4 35 ({ st := some 7, left := [1, 1], cur := 2, right := [1, 2, 1, 1, 1, 1, 2] }) = some ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) := rfl
  have h3 : steps tm_17_4 140 initConfig = some ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) := steps_add tm_17_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_17_4 35 ({ st := some 2, left := [1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] }) = some ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) := rfl
  have h4 : steps tm_17_4 175 initConfig = some ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) := steps_add tm_17_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_17_4 35 ({ st := some 2, left := [1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 2, 1, 1, 2] }) = some ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) := rfl
  have h5 : steps tm_17_4 210 initConfig = some ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) := steps_add tm_17_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_17_4 35 ({ st := some 7, left := [], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2] }) = some ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) := rfl
  have h6 : steps tm_17_4 245 initConfig = some ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) := steps_add tm_17_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_17_4 35 ({ st := some 0, left := [1, 1, 1, 1], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 2, 2] }) = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] }) := rfl
  have h7 : steps tm_17_4 280 initConfig = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] }) := steps_add tm_17_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_17_4 24 ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1, 1] }) = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h8 : steps tm_17_4 304 initConfig = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_17_4 280 24 initConfig _ _ h7 hstep8
  exact h8

/-! ### BB(18,4) — > f_{ω^2+6}(39) (`fwp26_4` @ step 634) -/
def tm_18_4 : TM
  | 0, 0 => some ⟨1, Dir.L, some 3⟩
  | 0, 1 => some ⟨2, Dir.R, some 6⟩
  | 0, 2 => some ⟨2, Dir.L, some 0⟩
  | 0, 3 => some ⟨3, Dir.L, some 6⟩
  | 1, 0 => some ⟨1, Dir.R, some 16⟩
  | 1, 1 => some ⟨2, Dir.L, some 7⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 1, 3 => some ⟨2, Dir.R, some 5⟩
  | 2, 0 => some ⟨2, Dir.L, some 4⟩
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
  | 16, 0 => some ⟨2, Dir.R, some 17⟩
  | 16, 1 => some ⟨2, Dir.R, some 16⟩
  | 16, 2 => some ⟨1, Dir.L, some 16⟩
  | 16, 3 => some ⟨1, Dir.L, some 8⟩
  | 17, 0 => some ⟨1, Dir.L, some 16⟩
  | 17, 3 => some ⟨3, Dir.L, some 15⟩
  | _, _ => none

theorem valid_18_4 : ValidTM 18 4 tm_18_4 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 4 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 16 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | _ + 4 => omega
    | 17 => match sym with | 0 | 3 => exact ⟨by decide, by decide⟩ | 1 | 2 => trivial | _ + 4 => omega
    | _ + 18 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 16 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | 17 => match sym with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl
    | _ + 18 => rfl

def landmark_18_4 : Config := { st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }
theorem reaches_landmark_18_4 : steps tm_18_4 634 initConfig = some landmark_18_4 := by
  have h0 : steps tm_18_4 35 initConfig = some ({ st := some 16, left := [2, 2, 2, 3], cur := 2, right := [1, 1, 1, 1, 1] }) := rfl
  have hstep1 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 3], cur := 2, right := [1, 1, 1, 1, 1] }) = some ({ st := some 4, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] }) := rfl
  have h1 : steps tm_18_4 70 initConfig = some ({ st := some 4, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] }) := steps_add tm_18_4 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_18_4 35 ({ st := some 4, left := [3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] }) = some ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) := rfl
  have h2 : steps tm_18_4 105 initConfig = some ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) := steps_add tm_18_4 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) = some ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h3 : steps tm_18_4 140 initConfig = some ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_18_4 35 ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h4 : steps tm_18_4 175 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h5 : steps tm_18_4 210 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h6 : steps tm_18_4 245 initConfig = some ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_18_4 35 ({ st := some 16, left := [2, 1, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h7 : steps tm_18_4 280 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) := rfl
  have h8 : steps tm_18_4 315 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) := steps_add tm_18_4 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h9 : steps tm_18_4 350 initConfig = some ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h10 : steps tm_18_4 385 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h11 : steps tm_18_4 420 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h12 : steps tm_18_4 455 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h13 : steps tm_18_4 490 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h14 : steps tm_18_4 525 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h15 : steps tm_18_4 560 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h16 : steps tm_18_4 595 initConfig = some ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_18_4 35 ({ st := some 16, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 8, left := [1], cur := 0, right := [0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h17 : steps tm_18_4 630 initConfig = some ({ st := some 8, left := [1], cur := 0, right := [0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_18_4 4 ({ st := some 8, left := [1], cur := 0, right := [0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h18 : steps tm_18_4 634 initConfig = some ({ st := some 6, left := [], cur := 3, right := [3, 0, 0, 0, 0, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_18_4 630 4 initConfig _ _ h17 hstep18
  exact h18

end BB.Champions2026_11_21.S4
