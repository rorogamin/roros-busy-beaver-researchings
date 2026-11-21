/-
  BB/Champions2026_11_21_S3.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 6 3-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S3
open BB

/-! ### BB(8,3) — > f_{ω+2}(4) (`fw2_3` @ step 44) -/
def tm_8_3 : TM
  | 0, 0 => some ⟨2, Dir.L, some 7⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 4⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, none⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, some 0⟩
  | 7, 1 => some ⟨1, Dir.R, some 3⟩
  | 7, 2 => some ⟨0, Dir.R, some 7⟩
  | _, _ => none

theorem valid_8_3 : ValidTM 8 3 tm_8_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 => exact ⟨by decide, by decide⟩ | 2 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | _ + 8 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 8 => rfl

def landmark_8_3 : Config := { st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 2] }
theorem reaches_landmark_8_3 : steps tm_8_3 44 initConfig = some landmark_8_3 := by
  have h0 : steps tm_8_3 35 initConfig = some ({ st := some 4, left := [0, 1], cur := 2, right := [1, 1, 1, 2] }) := rfl
  have hstep1 : steps tm_8_3 9 ({ st := some 4, left := [0, 1], cur := 2, right := [1, 1, 1, 2] }) = some ({ st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 2] }) := rfl
  have h1 : steps tm_8_3 44 initConfig = some ({ st := some 5, left := [1], cur := 0, right := [1, 1, 1, 1, 2] }) := steps_add tm_8_3 35 9 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(9,3) — > f_{ω+3}(4) (`fw3_3` @ step 39) -/
def tm_9_3 : TM
  | 0, 0 => some ⟨2, Dir.L, some 8⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 4⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 5⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.R, some 2⟩
  | 3, 1 => some ⟨0, Dir.L, some 3⟩
  | 3, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 6⟩
  | 5, 0 => some ⟨0, Dir.L, some 0⟩
  | 5, 1 => some ⟨0, Dir.L, some 3⟩
  | 5, 2 => some ⟨1, Dir.R, some 7⟩
  | 6, 0 => some ⟨1, Dir.L, some 3⟩
  | 6, 1 => some ⟨2, Dir.R, some 0⟩
  | 6, 2 => some ⟨2, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨2, Dir.L, some 0⟩
  | 7, 2 => some ⟨2, Dir.L, some 8⟩
  | 8, 0 => some ⟨1, Dir.R, some 3⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨2, Dir.L, some 7⟩
  | _, _ => none

theorem valid_9_3 : ValidTM 9 3 tm_9_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | _ + 9 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 8 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 9 => rfl

def landmark_9_3 : Config := { st := some 5, left := [1], cur := 0, right := [1, 1, 1, 2, 2, 2, 2] }
theorem reaches_landmark_9_3 : steps tm_9_3 39 initConfig = some landmark_9_3 := by
  have h0 : steps tm_9_3 35 initConfig = some ({ st := some 3, left := [1], cur := 1, right := [1, 1, 1, 2, 2, 2, 2] }) := rfl
  have hstep1 : steps tm_9_3 4 ({ st := some 3, left := [1], cur := 1, right := [1, 1, 1, 2, 2, 2, 2] }) = some ({ st := some 5, left := [1], cur := 0, right := [1, 1, 1, 2, 2, 2, 2] }) := rfl
  have h1 : steps tm_9_3 39 initConfig = some ({ st := some 5, left := [1], cur := 0, right := [1, 1, 1, 2, 2, 2, 2] }) := steps_add tm_9_3 35 4 initConfig _ _ h0 hstep1
  exact h1

/-! ### BB(16,3) — > f_{ω^2}(2) (`fwp2_3` @ step 8) -/
def tm_16_3 : TM
  | 0, 0 => some ⟨1, Dir.R, some 11⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.L, some 5⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨0, Dir.R, some 2⟩
  | 5, 1 => some ⟨0, Dir.R, some 2⟩
  | 5, 2 => some ⟨2, Dir.R, some 13⟩
  | 6, 0 => some ⟨0, Dir.R, some 9⟩
  | 6, 1 => some ⟨2, Dir.R, some 7⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.L, some 8⟩
  | 7, 1 => some ⟨2, Dir.R, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 15⟩
  | 8, 0 => some ⟨1, Dir.L, some 0⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨0, Dir.L, some 6⟩
  | 9, 0 => some ⟨0, Dir.R, some 10⟩
  | 9, 1 => some ⟨2, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 10, 0 => some ⟨1, Dir.R, none⟩
  | 10, 1 => some ⟨1, Dir.R, some 10⟩
  | 10, 2 => some ⟨2, Dir.R, some 1⟩
  | 11, 0 => some ⟨1, Dir.R, some 7⟩
  | 11, 1 => some ⟨1, Dir.R, some 15⟩
  | 11, 2 => some ⟨0, Dir.L, some 7⟩
  | 12, 0 => some ⟨0, Dir.R, some 12⟩
  | 12, 1 => some ⟨2, Dir.L, some 4⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 13, 0 => some ⟨2, Dir.R, some 13⟩
  | 13, 1 => some ⟨2, Dir.R, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 11⟩
  | 14, 0 => some ⟨0, Dir.R, some 12⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨2, Dir.L, some 14⟩
  | 15, 1 => some ⟨2, Dir.L, some 14⟩
  | 15, 2 => some ⟨2, Dir.L, some 15⟩
  | _, _ => none

theorem valid_16_3 : ValidTM 16 3 tm_16_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 9 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 10 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 11 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 12 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 13 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 14 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 15 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 8 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 9 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 10 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 11 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 12 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 13 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 14 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 15 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 16 => rfl

def landmark_16_3 : Config := { st := some 15, left := [1, 1], cur := 1, right := [1, 1] }
theorem reaches_landmark_16_3 : steps tm_16_3 8 initConfig = some landmark_16_3 := rfl

/-! ### BB(17,3) — > f_{ω^2}(6) (`fwp2_3` @ step 15) -/
def tm_17_3 : TM
  | 0, 0 => some ⟨0, Dir.R, some 7⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.L, some 5⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨0, Dir.R, some 2⟩
  | 5, 1 => some ⟨0, Dir.R, some 2⟩
  | 5, 2 => some ⟨2, Dir.R, some 13⟩
  | 6, 0 => some ⟨0, Dir.R, some 9⟩
  | 6, 1 => some ⟨2, Dir.R, some 7⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.L, some 8⟩
  | 7, 1 => some ⟨2, Dir.R, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 15⟩
  | 8, 0 => some ⟨1, Dir.L, some 16⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨0, Dir.L, some 6⟩
  | 9, 0 => some ⟨0, Dir.R, some 10⟩
  | 9, 1 => some ⟨2, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 10, 0 => some ⟨1, Dir.R, none⟩
  | 10, 1 => some ⟨1, Dir.R, some 10⟩
  | 10, 2 => some ⟨2, Dir.R, some 1⟩
  | 11, 0 => some ⟨2, Dir.R, some 0⟩
  | 11, 1 => some ⟨1, Dir.R, some 16⟩
  | 11, 2 => some ⟨0, Dir.L, some 7⟩
  | 12, 0 => some ⟨0, Dir.R, some 12⟩
  | 12, 1 => some ⟨2, Dir.L, some 4⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 13, 0 => some ⟨2, Dir.R, some 13⟩
  | 13, 1 => some ⟨2, Dir.R, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 11⟩
  | 14, 0 => some ⟨0, Dir.R, some 12⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨2, Dir.L, some 14⟩
  | 15, 1 => some ⟨2, Dir.L, some 14⟩
  | 15, 2 => some ⟨2, Dir.L, some 15⟩
  | 16, 0 => some ⟨1, Dir.R, some 11⟩
  | 16, 1 => some ⟨0, Dir.R, some 8⟩
  | 16, 2 => some ⟨1, Dir.R, some 15⟩
  | _, _ => none

theorem valid_17_3 : ValidTM 17 3 tm_17_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 9 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 10 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 11 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 12 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 13 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 14 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 15 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 16 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | _ + 17 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 8 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 9 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 10 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 11 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 12 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 13 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 14 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 15 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 16 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 17 => rfl

def landmark_17_3 : Config := { st := some 15, left := [1, 1, 1, 1, 1, 1], cur := 1, right := [1] }
theorem reaches_landmark_17_3 : steps tm_17_3 15 initConfig = some landmark_17_3 := rfl

/-! ### BB(18,3) — > f_{ω^2}(17) (`fwp2_3` @ step 205) -/
def tm_18_3 : TM
  | 0, 0 => some ⟨2, Dir.L, some 11⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.L, some 5⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨0, Dir.R, some 2⟩
  | 5, 1 => some ⟨0, Dir.R, some 2⟩
  | 5, 2 => some ⟨2, Dir.R, some 13⟩
  | 6, 0 => some ⟨0, Dir.R, some 9⟩
  | 6, 1 => some ⟨2, Dir.R, some 7⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.L, some 8⟩
  | 7, 1 => some ⟨2, Dir.R, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 15⟩
  | 8, 0 => some ⟨1, Dir.L, some 16⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨0, Dir.L, some 6⟩
  | 9, 0 => some ⟨0, Dir.R, some 10⟩
  | 9, 1 => some ⟨2, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 10, 0 => some ⟨1, Dir.R, none⟩
  | 10, 1 => some ⟨1, Dir.R, some 10⟩
  | 10, 2 => some ⟨2, Dir.R, some 1⟩
  | 11, 0 => some ⟨2, Dir.L, some 17⟩
  | 11, 1 => some ⟨0, Dir.R, some 0⟩
  | 11, 2 => some ⟨0, Dir.L, some 7⟩
  | 12, 0 => some ⟨0, Dir.R, some 12⟩
  | 12, 1 => some ⟨2, Dir.L, some 4⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 13, 0 => some ⟨2, Dir.R, some 13⟩
  | 13, 1 => some ⟨2, Dir.R, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 11⟩
  | 14, 0 => some ⟨0, Dir.R, some 12⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨2, Dir.L, some 14⟩
  | 15, 1 => some ⟨2, Dir.L, some 14⟩
  | 15, 2 => some ⟨2, Dir.L, some 15⟩
  | 16, 0 => some ⟨1, Dir.R, some 16⟩
  | 16, 1 => some ⟨0, Dir.L, some 16⟩
  | 16, 2 => some ⟨2, Dir.R, some 17⟩
  | 17, 0 => some ⟨1, Dir.L, some 7⟩
  | 17, 2 => some ⟨0, Dir.L, some 13⟩
  | _, _ => none

theorem valid_18_3 : ValidTM 18 3 tm_18_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 9 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 10 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 11 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 12 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 13 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 14 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 15 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 16 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 17 => match sym with | 0 | 2 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 3 => omega
    | _ + 18 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 8 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 9 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 10 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 11 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 12 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 13 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 14 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 15 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 16 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 17 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 18 => rfl

def landmark_18_3 : Config := { st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1] }
theorem reaches_landmark_18_3 : steps tm_18_3 205 initConfig = some landmark_18_3 := by
  have h0 : steps tm_18_3 35 initConfig = some ({ st := some 13, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] }) := rfl
  have hstep1 : steps tm_18_3 35 ({ st := some 13, left := [1, 1, 1, 1, 1, 1, 1], cur := 2, right := [] }) = some ({ st := some 16, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 2] }) := rfl
  have h1 : steps tm_18_3 70 initConfig = some ({ st := some 16, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 2] }) := steps_add tm_18_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_18_3 35 ({ st := some 16, left := [1], cur := 0, right := [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 2] }) = some ({ st := some 16, left := [1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2] }) := rfl
  have h2 : steps tm_18_3 105 initConfig = some ({ st := some 16, left := [1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2] }) := steps_add tm_18_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_18_3 35 ({ st := some 16, left := [1, 1], cur := 0, right := [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2] }) = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 1, 0, 2] }) := rfl
  have h3 : steps tm_18_3 140 initConfig = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 1, 0, 2] }) := steps_add tm_18_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_18_3 35 ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 1, 0, 2] }) = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] }) := rfl
  have h4 : steps tm_18_3 175 initConfig = some ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] }) := steps_add tm_18_3 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_18_3 30 ({ st := some 16, left := [1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [0, 0, 0, 0, 0, 0, 0, 0, 2] }) = some ({ st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1] }) := rfl
  have h5 : steps tm_18_3 205 initConfig = some ({ st := some 15, left := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cur := 1, right := [1, 1] }) := steps_add tm_18_3 175 30 initConfig _ _ h4 hstep5
  exact h5

/-! ### BB(22,3) — > f_{ω^2+1}(14) (`fwp21_3` @ step 150) -/
def tm_22_3 : TM
  | 0, 0 => some ⟨1, Dir.L, some 19⟩
  | 0, 1 => some ⟨1, Dir.L, some 4⟩
  | 0, 2 => some ⟨2, Dir.R, some 0⟩
  | 1, 0 => some ⟨0, Dir.L, some 6⟩
  | 1, 1 => some ⟨2, Dir.L, some 4⟩
  | 1, 2 => some ⟨2, Dir.R, some 1⟩
  | 2, 0 => some ⟨1, Dir.R, some 2⟩
  | 2, 1 => some ⟨1, Dir.R, some 2⟩
  | 2, 2 => some ⟨2, Dir.R, some 1⟩
  | 3, 0 => some ⟨0, Dir.L, some 5⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨2, Dir.L, some 3⟩
  | 4, 0 => some ⟨1, Dir.R, some 2⟩
  | 4, 1 => some ⟨2, Dir.L, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 3⟩
  | 5, 0 => some ⟨0, Dir.R, some 2⟩
  | 5, 1 => some ⟨0, Dir.R, some 2⟩
  | 5, 2 => some ⟨2, Dir.R, some 13⟩
  | 6, 0 => some ⟨0, Dir.R, some 9⟩
  | 6, 1 => some ⟨2, Dir.R, some 7⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 7, 0 => some ⟨1, Dir.L, some 8⟩
  | 7, 1 => some ⟨2, Dir.R, some 7⟩
  | 7, 2 => some ⟨1, Dir.L, some 15⟩
  | 8, 0 => some ⟨0, Dir.L, some 16⟩
  | 8, 1 => some ⟨1, Dir.L, some 8⟩
  | 8, 2 => some ⟨0, Dir.L, some 6⟩
  | 9, 0 => some ⟨0, Dir.R, some 10⟩
  | 9, 1 => some ⟨2, Dir.R, some 9⟩
  | 9, 2 => some ⟨2, Dir.R, some 9⟩
  | 10, 0 => some ⟨0, Dir.R, some 11⟩
  | 10, 1 => some ⟨1, Dir.R, some 10⟩
  | 10, 2 => some ⟨2, Dir.R, some 1⟩
  | 11, 0 => some ⟨1, Dir.R, none⟩
  | 11, 1 => some ⟨0, Dir.L, some 8⟩
  | 11, 2 => some ⟨0, Dir.L, some 7⟩
  | 12, 0 => some ⟨0, Dir.R, some 12⟩
  | 12, 1 => some ⟨2, Dir.L, some 4⟩
  | 12, 2 => some ⟨2, Dir.R, some 12⟩
  | 13, 0 => some ⟨2, Dir.R, some 13⟩
  | 13, 1 => some ⟨2, Dir.R, some 13⟩
  | 13, 2 => some ⟨2, Dir.L, some 11⟩
  | 14, 0 => some ⟨0, Dir.R, some 12⟩
  | 14, 1 => some ⟨0, Dir.L, some 15⟩
  | 14, 2 => some ⟨0, Dir.L, some 15⟩
  | 15, 0 => some ⟨2, Dir.L, some 14⟩
  | 15, 1 => some ⟨2, Dir.L, some 14⟩
  | 15, 2 => some ⟨2, Dir.L, some 15⟩
  | 16, 0 => some ⟨1, Dir.L, some 17⟩
  | 16, 1 => some ⟨1, Dir.L, some 16⟩
  | 16, 2 => some ⟨1, Dir.L, some 16⟩
  | 17, 0 => some ⟨1, Dir.R, some 18⟩
  | 17, 1 => some ⟨1, Dir.L, some 15⟩
  | 17, 2 => some ⟨1, Dir.L, some 16⟩
  | 18, 0 => some ⟨0, Dir.L, some 17⟩
  | 18, 1 => some ⟨1, Dir.R, some 18⟩
  | 18, 2 => some ⟨1, Dir.R, some 3⟩
  | 19, 0 => some ⟨2, Dir.L, some 16⟩
  | 19, 2 => some ⟨1, Dir.R, some 20⟩
  | 20, 0 => some ⟨2, Dir.R, some 21⟩
  | 20, 1 => some ⟨2, Dir.R, some 20⟩
  | 20, 2 => some ⟨1, Dir.L, some 20⟩
  | 21, 0 => some ⟨1, Dir.L, some 20⟩
  | 21, 1 => some ⟨1, Dir.L, some 11⟩
  | _, _ => none

theorem valid_22_3 : ValidTM 22 3 tm_22_3 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 1 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 2 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 3 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 4 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 5 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 6 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 7 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 8 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 9 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 10 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 11 => match sym with | 1 | 2 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 3 => omega
    | 12 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 13 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 14 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 15 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 16 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 17 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 18 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 19 => match sym with | 0 | 2 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 3 => omega
    | 20 => match sym with | 0 | 1 | 2 => exact ⟨by decide, by decide⟩ | _ + 3 => omega
    | 21 => match sym with | 0 | 1 => exact ⟨by decide, by decide⟩ | 2 => trivial | _ + 3 => omega
    | _ + 22 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 1 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 2 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 3 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 4 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 5 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 6 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 7 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 8 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 9 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 10 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 11 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 12 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 13 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 14 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 15 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 16 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 17 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 18 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 19 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 20 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | 21 => match sym with | 0 | 1 | 2 => omega | _ + 3 => rfl
    | _ + 22 => rfl

def landmark_22_3 : Config := { st := some 15, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }
theorem reaches_landmark_22_3 : steps tm_22_3 150 initConfig = some landmark_22_3 := by
  have h0 : steps tm_22_3 35 initConfig = some ({ st := some 20, left := [2, 2, 2, 2, 2, 2, 1, 1], cur := 2, right := [1, 1] }) := rfl
  have hstep1 : steps tm_22_3 35 ({ st := some 20, left := [2, 2, 2, 2, 2, 2, 1, 1], cur := 2, right := [1, 1] }) = some ({ st := some 20, left := [2, 2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h1 : steps tm_22_3 70 initConfig = some ({ st := some 20, left := [2, 2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_22_3 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_22_3 35 ({ st := some 20, left := [2, 2, 2, 2, 2], cur := 1, right := [1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 14, left := [], cur := 0, right := [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h2 : steps tm_22_3 105 initConfig = some ({ st := some 14, left := [], cur := 0, right := [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_22_3 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_22_3 35 ({ st := some 14, left := [], cur := 0, right := [2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 16, left := [], cur := 0, right := [1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h3 : steps tm_22_3 140 initConfig = some ({ st := some 16, left := [], cur := 0, right := [1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_22_3 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_22_3 10 ({ st := some 16, left := [], cur := 0, right := [1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) = some ({ st := some 15, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := rfl
  have h4 : steps tm_22_3 150 initConfig = some ({ st := some 15, left := [1, 1, 1, 1, 1], cur := 1, right := [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }) := steps_add tm_22_3 140 10 initConfig _ _ h3 hstep4
  exact h4

end BB.Champions2026_11_21.S3
