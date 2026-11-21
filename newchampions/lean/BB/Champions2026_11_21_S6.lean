/-
  BB/Champions2026_11_21_S6.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 7 6-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S6
open BB

/-! ### BB(6,6) — > f_{ω×2+1}(2) (`fwm21_6 (Lean 4)` @ step 100) -/
def tm_6_6 : TM
  | 0, 0 => some ⟨5, Dir.R, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨4, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨1, Dir.R, none⟩
  | 1, 0 => some ⟨5, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨3, Dir.R, some 3⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨2, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.L, some 4⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨2, Dir.L, some 4⟩
  | 4, 5 => some ⟨2, Dir.L, some 0⟩
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨1, Dir.R, none⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨1, Dir.R, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | _, _ => none

theorem valid_6_6 : ValidTM 6 6 tm_6_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 1 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | _ + 6 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 6 => rfl

def landmark_6_6 : Config := { st := some 1, left := [3, 3, 3], cur := 3, right := [1, 3, 1, 4, 1, 1, 2, 2, 5] }
theorem reaches_landmark_6_6 : steps tm_6_6 100 initConfig = some landmark_6_6 := by
  have h0 : steps tm_6_6 35 initConfig = some ({ st := some 3, left := [5], cur := 2, right := [1, 1, 1, 2, 2, 5] }) := rfl
  have hstep1 : steps tm_6_6 35 ({ st := some 3, left := [5], cur := 2, right := [1, 1, 1, 2, 2, 5] }) = some ({ st := some 3, left := [2, 3], cur := 2, right := [1, 4, 1, 1, 2, 2, 5] }) := rfl
  have h1 : steps tm_6_6 70 initConfig = some ({ st := some 3, left := [2, 3], cur := 2, right := [1, 4, 1, 1, 2, 2, 5] }) := steps_add tm_6_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_6_6 30 ({ st := some 3, left := [2, 3], cur := 2, right := [1, 4, 1, 1, 2, 2, 5] }) = some ({ st := some 1, left := [3, 3, 3], cur := 3, right := [1, 3, 1, 4, 1, 1, 2, 2, 5] }) := rfl
  have h2 : steps tm_6_6 100 initConfig = some ({ st := some 1, left := [3, 3, 3], cur := 3, right := [1, 3, 1, 4, 1, 1, 2, 2, 5] }) := steps_add tm_6_6 70 30 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(7,6) — > f_{ω^2+1}(2) (`fwp21_6 (Lean 4)` @ step 100) -/
def tm_7_6 : TM
  | 0, 0 => some ⟨1, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨2, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨4, Dir.L, some 5⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨1, Dir.R, none⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.R, none⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨4, Dir.R, some 5⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨2, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.R, some 6⟩
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨5, Dir.R, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 0⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨1, Dir.R, some 3⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | _, _ => none

theorem valid_7_6 : ValidTM 7 6 tm_7_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | _ + 7 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 7 => rfl

def landmark_7_6 : Config := { st := some 5, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 3, 2, 2] }
theorem reaches_landmark_7_6 : steps tm_7_6 100 initConfig = some landmark_7_6 := by
  have h0 : steps tm_7_6 35 initConfig = some ({ st := some 0, left := [2, 2, 3], cur := 4, right := [2, 2] }) := rfl
  have hstep1 : steps tm_7_6 35 ({ st := some 0, left := [2, 2, 3], cur := 4, right := [2, 2] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [4, 2, 2] }) := rfl
  have h1 : steps tm_7_6 70 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [4, 2, 2] }) := steps_add tm_7_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_7_6 30 ({ st := some 1, left := [3, 3, 3, 3, 3], cur := 3, right := [4, 2, 2] }) = some ({ st := some 5, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 3, 2, 2] }) := rfl
  have h2 : steps tm_7_6 100 initConfig = some ({ st := some 5, left := [3, 3], cur := 3, right := [1, 1, 1, 1, 3, 2, 2] }) := steps_add tm_7_6 70 30 initConfig _ _ h1 hstep2
  exact h2

/-! ### BB(13,6) — > f_{ω^ω+2}(6) (`fwpw2_6` @ step 67) -/
def tm_13_6 : TM
  | 0, 0 => some ⟨1, Dir.L, some 5⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨1, Dir.R, some 12⟩
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
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.R, some 10⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 5 => some ⟨0, Dir.L, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨1, Dir.R, some 12⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 5, 5 => some ⟨1, Dir.L, some 0⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨3, Dir.L, some 3⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨1, Dir.R, some 7⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 4⟩
  | 11, 0 => some ⟨3, Dir.R, some 0⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨0, Dir.R, some 2⟩
  | 12, 1 => some ⟨5, Dir.L, some 12⟩
  | 12, 2 => some ⟨2, Dir.L, some 12⟩
  | 12, 3 => some ⟨2, Dir.L, some 12⟩
  | 12, 4 => some ⟨4, Dir.L, some 5⟩
  | _, _ => none

theorem valid_13_6 : ValidTM 13 6 tm_13_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 10 => match sym with | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 0 | 5 => trivial | _ + 6 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 13 => rfl

def landmark_13_6 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5] }
theorem reaches_landmark_13_6 : steps tm_13_6 67 initConfig = some landmark_13_6 := by
  have h0 : steps tm_13_6 35 initConfig = some ({ st := some 9, left := [1, 1, 2], cur := 1, right := [1, 4, 5, 5] }) := rfl
  have hstep1 : steps tm_13_6 32 ({ st := some 9, left := [1, 1, 2], cur := 1, right := [1, 4, 5, 5] }) = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5] }) := rfl
  have h1 : steps tm_13_6 67 initConfig = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 5, 5] }) := steps_add tm_13_6 35 32 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(14,6) — > f_{ω^ω+2}(27) (`fwpw2_5` @ step 423) -/
def tm_14_6 : TM
  | 0, 0 => some ⟨5, Dir.R, some 10⟩
  | 0, 1 => some ⟨1, Dir.L, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 6⟩
  | 0, 3 => some ⟨3, Dir.L, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 0⟩
  | 0, 5 => some ⟨5, Dir.L, some 7⟩
  | 1, 0 => some ⟨2, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨2, Dir.R, some 9⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨5, Dir.R, some 2⟩
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
  | 7, 5 => some ⟨1, Dir.R, some 5⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 8, 5 => some ⟨1, Dir.R, some 11⟩
  | 9, 0 => some ⟨1, Dir.L, some 4⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 9, 5 => some ⟨2, Dir.L, some 0⟩
  | 10, 0 => some ⟨3, Dir.L, some 0⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨2, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.L, some 6⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨5, Dir.L, some 8⟩
  | 11, 5 => some ⟨0, Dir.R, some 1⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨0, Dir.R, some 0⟩
  | 12, 2 => some ⟨0, Dir.L, some 13⟩
  | 12, 3 => some ⟨5, Dir.R, some 4⟩
  | 13, 0 => some ⟨3, Dir.R, some 1⟩
  | 13, 2 => some ⟨0, Dir.L, some 13⟩
  | 13, 3 => some ⟨0, Dir.L, some 13⟩
  | _, _ => none

theorem valid_14_6 : ValidTM 14 6 tm_14_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 3 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 => trivial | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 12 => match sym with | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 13 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 => trivial | _ + 6 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 14 => rfl

def landmark_14_6 : Config := { st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_14_6 : steps tm_14_6 423 initConfig = some landmark_14_6 := by
  have h0 : steps tm_14_6 35 initConfig = some ({ st := some 9, left := [1, 2, 2, 2], cur := 0, right := [1, 4, 0, 1] }) := rfl
  have hstep1 : steps tm_14_6 35 ({ st := some 9, left := [1, 2, 2, 2], cur := 0, right := [1, 4, 0, 1] }) = some ({ st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 4] }) := rfl
  have h1 : steps tm_14_6 70 initConfig = some ({ st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 4] }) := steps_add tm_14_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_6 35 ({ st := some 2, left := [2, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 4] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 4, right := [] }) := rfl
  have h2 : steps tm_14_6 105 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 4, right := [] }) := steps_add tm_14_6 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_6 35 ({ st := some 4, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 4, right := [] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 4] }) := rfl
  have h3 : steps tm_14_6 140 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 4] }) := steps_add tm_14_6 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_6 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 4] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 1, 4] }) := rfl
  have h4 : steps tm_14_6 175 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 1, 4] }) := steps_add tm_14_6 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_14_6 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 1, 4] }) = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) := rfl
  have h5 : steps tm_14_6 210 initConfig = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) := steps_add tm_14_6 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_14_6 35 ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) = some ({ st := some 4, left := [2, 2, 3, 3, 3, 3, 3, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] }) := rfl
  have h6 : steps tm_14_6 245 initConfig = some ({ st := some 4, left := [2, 2, 3, 3, 3, 3, 3, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] }) := steps_add tm_14_6 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_14_6 35 ({ st := some 4, left := [2, 2, 3, 3, 3, 3, 3, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 0, right := [] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) := rfl
  have h7 : steps tm_14_6 280 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) := steps_add tm_14_6 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_14_6 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 4] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4] }) := rfl
  have h8 : steps tm_14_6 315 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4] }) := steps_add tm_14_6 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_14_6 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4] }) = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) := rfl
  have h9 : steps tm_14_6 350 initConfig = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) := steps_add tm_14_6 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_14_6 35 ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4] }) = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h10 : steps tm_14_6 385 initConfig = some ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_14_6 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_14_6 35 ({ st := some 6, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 2, left := [], cur := 0, right := [3, 3, 1, 4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h11 : steps tm_14_6 420 initConfig = some ({ st := some 2, left := [], cur := 0, right := [3, 3, 1, 4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_14_6 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_14_6 3 ({ st := some 2, left := [], cur := 0, right := [3, 3, 1, 4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h12 : steps tm_14_6 423 initConfig = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_14_6 420 3 initConfig _ _ h11 hstep12
  exact h12

/-! ### BB(15,6) — > f_{ω^ω+3}(35) (`fwpw3_5` @ step 902) -/
def tm_15_6 : TM
  | 0, 0 => some ⟨1, Dir.R, some 9⟩
  | 0, 1 => some ⟨1, Dir.L, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 6⟩
  | 0, 3 => some ⟨3, Dir.L, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 0⟩
  | 1, 0 => some ⟨2, Dir.R, some 7⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨3, Dir.L, some 9⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨0, Dir.L, some 13⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 5 => some ⟨4, Dir.R, some 6⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨1, Dir.L, some 11⟩
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
  | 6, 5 => some ⟨0, Dir.R, some 12⟩
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
  | 9, 0 => some ⟨4, Dir.R, some 8⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 10, 0 => some ⟨0, Dir.R, some 6⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 1⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨4, Dir.R, some 2⟩
  | 12, 2 => some ⟨0, Dir.L, some 13⟩
  | 12, 4 => some ⟨2, Dir.L, some 14⟩
  | 13, 0 => some ⟨3, Dir.R, some 1⟩
  | 13, 2 => some ⟨0, Dir.L, some 13⟩
  | 13, 3 => some ⟨0, Dir.L, some 13⟩
  | 13, 4 => some ⟨5, Dir.R, some 1⟩
  | 14, 0 => some ⟨0, Dir.R, some 2⟩
  | 14, 2 => some ⟨2, Dir.L, some 14⟩
  | 14, 3 => some ⟨2, Dir.L, some 14⟩
  | _, _ => none

theorem valid_15_6 : ValidTM 15 6 tm_15_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 3 => match sym with | 0 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 1 | 4 => trivial | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 12 => match sym with | 1 | 2 | 4 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 3 | 5 => trivial | _ + 6 => omega
    | 13 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 | 5 => trivial | _ + 6 => omega
    | 14 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 => trivial | _ + 6 => omega
    | _ + 15 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 15 => rfl

def landmark_15_6 : Config := { st := some 7, left := [2, 2, 3], cur := 1, right := [4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }
theorem reaches_landmark_15_6 : steps tm_15_6 902 initConfig = some landmark_15_6 := by
  have h0 : steps tm_15_6 35 initConfig = some ({ st := some 9, left := [3, 3, 3, 3, 3], cur := 3, right := [3, 2, 1, 4] }) := rfl
  have hstep1 : steps tm_15_6 35 ({ st := some 9, left := [3, 3, 3, 3, 3], cur := 3, right := [3, 2, 1, 4] }) = some ({ st := some 8, left := [3, 3, 3, 3, 1], cur := 3, right := [3, 4, 2, 1, 4, 1] }) := rfl
  have h1 : steps tm_15_6 70 initConfig = some ({ st := some 8, left := [3, 3, 3, 3, 1], cur := 3, right := [3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_15_6 35 ({ st := some 8, left := [3, 3, 3, 3, 1], cur := 3, right := [3, 4, 2, 1, 4, 1] }) = some ({ st := some 5, left := [3, 3, 4, 3, 2, 2, 2], cur := 3, right := [3, 2, 4, 2, 1, 4, 1] }) := rfl
  have h2 : steps tm_15_6 105 initConfig = some ({ st := some 5, left := [3, 3, 4, 3, 2, 2, 2], cur := 3, right := [3, 2, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_15_6 35 ({ st := some 5, left := [3, 3, 4, 3, 2, 2, 2], cur := 3, right := [3, 2, 4, 2, 1, 4, 1] }) = some ({ st := some 9, left := [3, 2, 2, 2], cur := 3, right := [3, 4, 3, 3, 2, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h3 : steps tm_15_6 140 initConfig = some ({ st := some 9, left := [3, 2, 2, 2], cur := 3, right := [3, 4, 3, 3, 2, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_15_6 35 ({ st := some 9, left := [3, 2, 2, 2], cur := 3, right := [3, 4, 3, 3, 2, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 9, left := [2], cur := 2, right := [2, 3, 3, 3, 3, 3, 4, 2, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h4 : steps tm_15_6 175 initConfig = some ({ st := some 9, left := [2], cur := 2, right := [2, 3, 3, 3, 3, 3, 4, 2, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_15_6 35 ({ st := some 9, left := [2], cur := 2, right := [2, 3, 3, 3, 3, 3, 4, 2, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 9, left := [3, 2, 2], cur := 4, right := [3, 3, 3, 3, 2, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h5 : steps tm_15_6 210 initConfig = some ({ st := some 9, left := [3, 2, 2], cur := 4, right := [3, 3, 3, 3, 2, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_15_6 35 ({ st := some 9, left := [3, 2, 2], cur := 4, right := [3, 3, 3, 3, 2, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 9, left := [3, 3, 2, 2], cur := 3, right := [4, 3, 3, 2, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h6 : steps tm_15_6 245 initConfig = some ({ st := some 9, left := [3, 3, 2, 2], cur := 3, right := [4, 3, 3, 2, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_15_6 35 ({ st := some 9, left := [3, 3, 2, 2], cur := 3, right := [4, 3, 3, 2, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 9, left := [3, 3, 3, 2, 2], cur := 3, right := [3, 4, 2, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h7 : steps tm_15_6 280 initConfig = some ({ st := some 9, left := [3, 3, 3, 2, 2], cur := 3, right := [3, 4, 2, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_15_6 35 ({ st := some 9, left := [3, 3, 3, 2, 2], cur := 3, right := [3, 4, 2, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 8, left := [3, 3, 4, 3, 2], cur := 3, right := [2, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h8 : steps tm_15_6 315 initConfig = some ({ st := some 8, left := [3, 3, 4, 3, 2], cur := 3, right := [2, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_15_6 35 ({ st := some 8, left := [3, 3, 4, 3, 2], cur := 3, right := [2, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 8, left := [], cur := 2, right := [3, 3, 3, 4, 3, 2, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h9 : steps tm_15_6 350 initConfig = some ({ st := some 8, left := [], cur := 2, right := [3, 3, 3, 4, 3, 2, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_15_6 35 ({ st := some 8, left := [], cur := 2, right := [3, 3, 3, 4, 3, 2, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 7, left := [2, 2, 2, 3], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h10 : steps tm_15_6 385 initConfig = some ({ st := some 7, left := [2, 2, 2, 3], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_15_6 35 ({ st := some 7, left := [2, 2, 2, 3], cur := 3, right := [3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h11 : steps tm_15_6 420 initConfig = some ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_15_6 35 ({ st := some 11, left := [3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h12 : steps tm_15_6 455 initConfig = some ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_15_6 35 ({ st := some 11, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := rfl
  have h13 : steps tm_15_6 490 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) := steps_add tm_15_6 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_15_6 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3, 3, 3, 3, 3, 4, 2, 1, 4, 1] }) = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1] }) := rfl
  have h14 : steps tm_15_6 525 initConfig = some ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1] }) := steps_add tm_15_6 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_15_6 35 ({ st := some 11, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1] }) = some ({ st := some 7, left := [2, 5, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] }) := rfl
  have h15 : steps tm_15_6 560 initConfig = some ({ st := some 7, left := [2, 5, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] }) := steps_add tm_15_6 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_15_6 35 ({ st := some 7, left := [2, 5, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [] }) = some ({ st := some 8, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4, 0, 3] }) := rfl
  have h16 : steps tm_15_6 595 initConfig = some ({ st := some 8, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4, 0, 3] }) := steps_add tm_15_6 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_15_6 35 ({ st := some 8, left := [], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 4, 0, 3] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) := rfl
  have h17 : steps tm_15_6 630 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) := steps_add tm_15_6 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_15_6 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) := rfl
  have h18 : steps tm_15_6 665 initConfig = some ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) := steps_add tm_15_6 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_15_6 35 ({ st := some 7, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 4, 0, 3] }) = some ({ st := some 0, left := [2, 5, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [4] }) := rfl
  have h19 : steps tm_15_6 700 initConfig = some ({ st := some 0, left := [2, 5, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [4] }) := steps_add tm_15_6 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_15_6 35 ({ st := some 0, left := [2, 5, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 2, right := [4] }) = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4] }) := rfl
  have h20 : steps tm_15_6 735 initConfig = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4] }) := steps_add tm_15_6 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_15_6 35 ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4] }) = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h21 : steps tm_15_6 770 initConfig = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_6 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_15_6 35 ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h22 : steps tm_15_6 805 initConfig = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_6 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_15_6 35 ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h23 : steps tm_15_6 840 initConfig = some ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_6 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_15_6 35 ({ st := some 5, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 5, left := [4, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h24 : steps tm_15_6 875 initConfig = some ({ st := some 5, left := [4, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_6 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_15_6 27 ({ st := some 5, left := [4, 2, 2, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := rfl
  have h25 : steps tm_15_6 902 initConfig = some ({ st := some 7, left := [2, 2, 3], cur := 1, right := [4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] }) := steps_add tm_15_6 875 27 initConfig _ _ h24 hstep25
  exact h25

/-! ### BB(16,6) — > f_{ω^ω+4}(25) (`fwpw4_6` @ step 414) -/
def tm_16_6 : TM
  | 0, 0 => some ⟨4, Dir.L, some 11⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 4 => some ⟨3, Dir.L, some 4⟩
  | 0, 5 => some ⟨0, Dir.L, some 10⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨4, Dir.L, some 7⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨3, Dir.L, some 11⟩
  | 1, 5 => some ⟨2, Dir.R, some 13⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨5, Dir.L, some 10⟩
  | 2, 5 => some ⟨5, Dir.L, some 4⟩
  | 3, 0 => some ⟨2, Dir.R, some 4⟩
  | 3, 1 => some ⟨4, Dir.R, some 10⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 4, 0 => some ⟨3, Dir.R, some 0⟩
  | 4, 1 => some ⟨2, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨5, Dir.L, some 11⟩
  | 4, 5 => some ⟨5, Dir.R, some 7⟩
  | 5, 0 => some ⟨1, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 6⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 6⟩
  | 5, 5 => some ⟨0, Dir.R, some 6⟩
  | 6, 0 => some ⟨2, Dir.R, some 9⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 6, 3 => some ⟨2, Dir.L, some 8⟩
  | 6, 4 => some ⟨4, Dir.L, some 10⟩
  | 7, 0 => some ⟨4, Dir.R, some 8⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨4, Dir.L, some 7⟩
  | 7, 5 => some ⟨2, Dir.L, some 11⟩
  | 8, 0 => some ⟨2, Dir.R, some 2⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨3, Dir.L, some 6⟩
  | 8, 3 => some ⟨3, Dir.L, some 8⟩
  | 8, 4 => some ⟨4, Dir.L, some 8⟩
  | 9, 0 => some ⟨2, Dir.R, some 7⟩
  | 9, 1 => some ⟨1, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 9, 3 => some ⟨3, Dir.R, some 9⟩
  | 9, 4 => some ⟨4, Dir.R, some 5⟩
  | 9, 5 => some ⟨5, Dir.L, some 10⟩
  | 10, 0 => some ⟨5, Dir.L, some 5⟩
  | 10, 1 => some ⟨1, Dir.L, some 10⟩
  | 10, 2 => some ⟨3, Dir.L, some 4⟩
  | 10, 3 => some ⟨3, Dir.L, some 10⟩
  | 10, 4 => some ⟨3, Dir.L, some 3⟩
  | 11, 0 => some ⟨3, Dir.R, some 0⟩
  | 11, 1 => some ⟨1, Dir.L, some 11⟩
  | 11, 2 => some ⟨1, Dir.L, some 11⟩
  | 11, 3 => some ⟨1, Dir.L, some 11⟩
  | 11, 4 => some ⟨1, Dir.R, some 12⟩
  | 12, 0 => some ⟨0, Dir.R, some 2⟩
  | 12, 1 => some ⟨5, Dir.L, some 13⟩
  | 12, 2 => some ⟨2, Dir.L, some 12⟩
  | 12, 3 => some ⟨2, Dir.L, some 12⟩
  | 13, 0 => some ⟨1, Dir.R, none⟩
  | 13, 1 => some ⟨2, Dir.L, some 11⟩
  | 13, 2 => some ⟨0, Dir.R, some 15⟩
  | 13, 3 => some ⟨4, Dir.L, some 15⟩
  | 13, 4 => some ⟨5, Dir.L, some 14⟩
  | 13, 5 => some ⟨2, Dir.L, some 12⟩
  | 14, 0 => some ⟨3, Dir.R, some 14⟩
  | 14, 1 => some ⟨3, Dir.L, some 7⟩
  | 14, 2 => some ⟨5, Dir.L, some 14⟩
  | 14, 3 => some ⟨5, Dir.L, some 14⟩
  | 14, 4 => some ⟨2, Dir.R, some 15⟩
  | 14, 5 => some ⟨2, Dir.R, some 1⟩
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 1 => some ⟨4, Dir.R, some 6⟩
  | 15, 2 => some ⟨4, Dir.L, some 15⟩
  | 15, 3 => some ⟨4, Dir.L, some 15⟩
  | 15, 4 => some ⟨2, Dir.R, some 13⟩
  | _, _ => none

theorem valid_16_6 : ValidTM 16 6 tm_16_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 12 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 13 => match sym with | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 6 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 16 => rfl

def landmark_16_6 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 2, 5, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem reaches_landmark_16_6 : steps tm_16_6 414 initConfig = some landmark_16_6 := by
  have h0 : steps tm_16_6 35 initConfig = some ({ st := some 2, left := [2, 2, 2, 3], cur := 1, right := [5, 1, 2, 5, 1, 4] }) := rfl
  have hstep1 : steps tm_16_6 35 ({ st := some 2, left := [2, 2, 2, 3], cur := 1, right := [5, 1, 2, 5, 1, 4] }) = some ({ st := some 5, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 5, 1, 2, 5, 1, 4] }) := rfl
  have h1 : steps tm_16_6 70 initConfig = some ({ st := some 5, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 5, 1, 2, 5, 1, 4] }) := steps_add tm_16_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_6 35 ({ st := some 5, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 5, 1, 2, 5, 1, 4] }) = some ({ st := some 2, left := [], cur := 2, right := [3, 3, 1, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) := rfl
  have h2 : steps tm_16_6 105 initConfig = some ({ st := some 2, left := [], cur := 2, right := [3, 3, 1, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) := steps_add tm_16_6 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_6 35 ({ st := some 2, left := [], cur := 2, right := [3, 3, 1, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) = some ({ st := some 4, left := [2], cur := 1, right := [1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) := rfl
  have h3 : steps tm_16_6 140 initConfig = some ({ st := some 4, left := [2], cur := 1, right := [1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) := steps_add tm_16_6 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_6 35 ({ st := some 4, left := [2], cur := 1, right := [1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5, 3, 3, 5, 1, 4] }) = some ({ st := some 11, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := rfl
  have h4 : steps tm_16_6 175 initConfig = some ({ st := some 11, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := steps_add tm_16_6 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_6 35 ({ st := some 11, left := [3, 1, 4, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) = some ({ st := some 11, left := [2, 2, 2, 2, 2], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := rfl
  have h5 : steps tm_16_6 210 initConfig = some ({ st := some 11, left := [2, 2, 2, 2, 2], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := steps_add tm_16_6 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_16_6 35 ({ st := some 11, left := [2, 2, 2, 2, 2], cur := 2, right := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) = some ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := rfl
  have h6 : steps tm_16_6 245 initConfig = some ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) := steps_add tm_16_6 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_16_6 35 ({ st := some 3, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4] }) = some ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5] }) := rfl
  have h7 : steps tm_16_6 280 initConfig = some ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5] }) := steps_add tm_16_6 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_16_6 35 ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5] }) = some ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3] }) := rfl
  have h8 : steps tm_16_6 315 initConfig = some ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3] }) := steps_add tm_16_6 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_16_6 35 ({ st := some 10, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [3] }) = some ({ st := some 0, left := [], cur := 2, right := [1, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h9 : steps tm_16_6 350 initConfig = some ({ st := some 0, left := [], cur := 2, right := [1, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_6 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_16_6 35 ({ st := some 0, left := [], cur := 2, right := [1, 3, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) = some ({ st := some 15, left := [3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h10 : steps tm_16_6 385 initConfig = some ({ st := some 15, left := [3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_6 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_16_6 29 ({ st := some 15, left := [3], cur := 2, right := [4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 2, 5, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := rfl
  have h11 : steps tm_16_6 414 initConfig = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [4, 2, 2, 5, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) := steps_add tm_16_6 385 29 initConfig _ _ h10 hstep11
  exact h11

/-! ### BB(17,6) — > f_{ε_0}(24) (`fe0_5` @ step 536) -/
def tm_17_6 : TM
  | 0, 0 => some ⟨1, Dir.L, some 9⟩
  | 0, 2 => some ⟨0, Dir.R, some 5⟩
  | 0, 3 => some ⟨0, Dir.R, some 3⟩
  | 0, 4 => some ⟨1, Dir.L, some 16⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨1, Dir.R, some 1⟩
  | 1, 2 => some ⟨2, Dir.L, some 2⟩
  | 2, 0 => some ⟨0, Dir.L, some 8⟩
  | 2, 1 => some ⟨4, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 2⟩
  | 2, 3 => some ⟨3, Dir.R, some 2⟩
  | 2, 4 => some ⟨2, Dir.R, some 2⟩
  | 3, 0 => some ⟨1, Dir.L, some 4⟩
  | 3, 1 => some ⟨1, Dir.R, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 3⟩
  | 3, 3 => some ⟨3, Dir.R, some 3⟩
  | 3, 4 => some ⟨2, Dir.L, some 4⟩
  | 4, 0 => some ⟨3, Dir.L, some 0⟩
  | 4, 1 => some ⟨1, Dir.L, some 4⟩
  | 4, 2 => some ⟨2, Dir.L, some 4⟩
  | 4, 3 => some ⟨3, Dir.L, some 4⟩
  | 4, 5 => some ⟨1, Dir.L, some 16⟩
  | 5, 0 => some ⟨0, Dir.L, some 6⟩
  | 5, 1 => some ⟨1, Dir.R, some 5⟩
  | 5, 2 => some ⟨2, Dir.R, some 5⟩
  | 5, 3 => some ⟨3, Dir.R, some 5⟩
  | 6, 0 => some ⟨0, Dir.R, some 8⟩
  | 6, 1 => some ⟨0, Dir.L, some 7⟩
  | 6, 3 => some ⟨3, Dir.R, some 8⟩
  | 7, 0 => some ⟨2, Dir.L, some 0⟩
  | 7, 1 => some ⟨1, Dir.L, some 7⟩
  | 7, 2 => some ⟨2, Dir.L, some 7⟩
  | 7, 3 => some ⟨3, Dir.L, some 7⟩
  | 7, 4 => some ⟨2, Dir.L, some 7⟩
  | 8, 0 => some ⟨3, Dir.R, some 13⟩
  | 8, 2 => some ⟨0, Dir.L, some 0⟩
  | 8, 3 => some ⟨0, Dir.L, some 8⟩
  | 8, 4 => some ⟨1, Dir.L, some 7⟩
  | 9, 0 => some ⟨2, Dir.R, some 14⟩
  | 9, 1 => some ⟨4, Dir.R, some 7⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨3, Dir.L, some 9⟩
  | 9, 4 => some ⟨5, Dir.R, some 3⟩
  | 10, 0 => some ⟨2, Dir.L, some 11⟩
  | 10, 1 => some ⟨5, Dir.R, some 14⟩
  | 10, 2 => some ⟨2, Dir.R, some 10⟩
  | 10, 3 => some ⟨3, Dir.R, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 10⟩
  | 11, 0 => some ⟨3, Dir.R, some 14⟩
  | 11, 1 => some ⟨2, Dir.R, some 14⟩
  | 11, 2 => some ⟨2, Dir.L, some 11⟩
  | 11, 3 => some ⟨3, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.L, some 11⟩
  | 12, 0 => some ⟨3, Dir.L, some 11⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 12, 3 => some ⟨3, Dir.R, some 12⟩
  | 12, 4 => some ⟨4, Dir.R, some 12⟩
  | 13, 0 => some ⟨4, Dir.L, some 9⟩
  | 13, 1 => some ⟨1, Dir.L, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 13⟩
  | 13, 3 => some ⟨3, Dir.L, some 13⟩
  | 13, 4 => some ⟨1, Dir.L, some 14⟩
  | 13, 5 => some ⟨5, Dir.R, some 3⟩
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
  | _, _ => none

theorem valid_17_6 : ValidTM 17 6 tm_17_6 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 | 5 => trivial | _ + 6 => omega
    | 1 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 3 | 4 | 5 => trivial | _ + 6 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 6 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 6 => omega
    | 6 => match sym with | 0 | 1 | 3 => exact ⟨by decide, by decide⟩ | 2 | 4 | 5 => trivial | _ + 6 => omega
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 8 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 | 5 => trivial | _ + 6 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 12 => match sym with | 0 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 1 | 5 => trivial | _ + 6 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨by decide, by decide⟩ | _ + 6 => omega
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | 16 => match sym with | 0 | 1 | 2 | 3 | 4 => exact ⟨by decide, by decide⟩ | 5 => trivial | _ + 6 => omega
    | _ + 17 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | 16 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 => omega | _ + 6 => rfl
    | _ + 17 => rfl

def landmark_17_6 : Config := { st := some 1, left := [1, 1, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_17_6 : steps tm_17_6 536 initConfig = some landmark_17_6 := by
  have h0 : steps tm_17_6 35 initConfig = some ({ st := some 15, left := [2, 4, 2], cur := 1, right := [2, 2, 1] }) := rfl
  have hstep1 : steps tm_17_6 35 ({ st := some 15, left := [2, 4, 2], cur := 1, right := [2, 2, 1] }) = some ({ st := some 7, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 4] }) := rfl
  have h1 : steps tm_17_6 70 initConfig = some ({ st := some 7, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 4] }) := steps_add tm_17_6 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_17_6 35 ({ st := some 7, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 4] }) = some ({ st := some 13, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 4] }) := rfl
  have h2 : steps tm_17_6 105 initConfig = some ({ st := some 13, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 4] }) := steps_add tm_17_6 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_17_6 35 ({ st := some 13, left := [2, 2, 2, 4, 2], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 4] }) = some ({ st := some 11, left := [5, 1], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2] }) := rfl
  have h3 : steps tm_17_6 140 initConfig = some ({ st := some 11, left := [5, 1], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2] }) := steps_add tm_17_6 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_17_6 35 ({ st := some 11, left := [5, 1], cur := 1, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2] }) = some ({ st := some 10, left := [2, 2, 2, 2, 1, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2] }) := rfl
  have h4 : steps tm_17_6 175 initConfig = some ({ st := some 10, left := [2, 2, 2, 2, 1, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2] }) := steps_add tm_17_6 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_17_6 35 ({ st := some 10, left := [2, 2, 2, 2, 1, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2] }) = some ({ st := some 10, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5, 1], cur := 2, right := [2, 2] }) := rfl
  have h5 : steps tm_17_6 210 initConfig = some ({ st := some 10, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5, 1], cur := 2, right := [2, 2] }) := steps_add tm_17_6 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_17_6 35 ({ st := some 10, left := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5, 1], cur := 2, right := [2, 2] }) = some ({ st := some 11, left := [2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2] }) := rfl
  have h6 : steps tm_17_6 245 initConfig = some ({ st := some 11, left := [2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2] }) := steps_add tm_17_6 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_17_6 35 ({ st := some 11, left := [2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2] }) = some ({ st := some 11, left := [2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2, 2] }) := rfl
  have h7 : steps tm_17_6 280 initConfig = some ({ st := some 11, left := [2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_17_6 35 ({ st := some 11, left := [2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 4, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 14, left := [2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h8 : steps tm_17_6 315 initConfig = some ({ st := some 14, left := [2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_17_6 35 ({ st := some 14, left := [2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 10, left := [4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h9 : steps tm_17_6 350 initConfig = some ({ st := some 10, left := [4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_17_6 35 ({ st := some 10, left := [4, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2] }) := rfl
  have h10 : steps tm_17_6 385 initConfig = some ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2] }) := steps_add tm_17_6 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_17_6 35 ({ st := some 10, left := [2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2] }) = some ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2] }) := rfl
  have h11 : steps tm_17_6 420 initConfig = some ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2] }) := steps_add tm_17_6 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_17_6 35 ({ st := some 11, left := [2, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2] }) = some ({ st := some 11, left := [2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h12 : steps tm_17_6 455 initConfig = some ({ st := some 11, left := [2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_17_6 35 ({ st := some 11, left := [2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 13, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h13 : steps tm_17_6 490 initConfig = some ({ st := some 13, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_17_6 35 ({ st := some 13, left := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 1], cur := 2, right := [4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 4, left := [2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h14 : steps tm_17_6 525 initConfig = some ({ st := some 4, left := [2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_17_6 11 ({ st := some 4, left := [2, 2, 2, 2, 2, 5, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) = some ({ st := some 1, left := [1, 1, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h15 : steps tm_17_6 536 initConfig = some ({ st := some 1, left := [1, 1, 1], cur := 2, right := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_17_6 525 11 initConfig _ _ h14 hstep15
  exact h15

end BB.Champions2026_11_21.S6
