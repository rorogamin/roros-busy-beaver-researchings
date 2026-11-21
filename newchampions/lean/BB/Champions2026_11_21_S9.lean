/-
  BB/Champions2026_11_21_S9.lean
  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for 7 9-symbol champions.
-/
import BB.TM

namespace BB.Champions2026_11_21.S9
open BB

/-! ### BB(4,9) — > f_{ω+4}(12) (`fw4_8` @ step 304) -/
def tm_4_9 : TM
  | 0, 0 => some ⟨5, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨7, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨8, Dir.L, some 1⟩
  | 0, 6 => some ⟨4, Dir.L, some 1⟩
  | 0, 7 => some ⟨6, Dir.L, some 0⟩
  | 0, 8 => some ⟨7, Dir.R, some 0⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 3⟩
  | 1, 5 => some ⟨3, Dir.R, some 0⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 1, 7 => some ⟨0, Dir.L, some 2⟩
  | 1, 8 => some ⟨2, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨5, Dir.L, some 2⟩
  | 2, 6 => some ⟨5, Dir.L, some 3⟩
  | 2, 7 => some ⟨8, Dir.L, some 2⟩
  | 2, 8 => some ⟨3, Dir.R, some 0⟩
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 2 => some ⟨6, Dir.L, some 2⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 5 => some ⟨4, Dir.L, some 3⟩
  | 3, 6 => some ⟨6, Dir.L, some 2⟩
  | 3, 7 => some ⟨7, Dir.L, some 0⟩
  | _, _ => none

theorem valid_4_9 : ValidTM 4 9 tm_4_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 8 => trivial | _ + 9 => omega
    | _ + 4 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 4 => rfl

def landmark_4_9 : Config := { st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem reaches_landmark_4_9 : steps tm_4_9 304 initConfig = some landmark_4_9 := by
  have h0 : steps tm_4_9 35 initConfig = some ({ st := some 1, left := [3, 3, 3], cur := 2, right := [3, 8] }) := rfl
  have hstep1 : steps tm_4_9 35 ({ st := some 1, left := [3, 3, 3], cur := 2, right := [3, 8] }) = some ({ st := some 2, left := [2, 2, 2, 2, 3, 3, 3], cur := 8, right := [5] }) := rfl
  have h1 : steps tm_4_9 70 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 3, 3, 3], cur := 8, right := [5] }) := steps_add tm_4_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_4_9 35 ({ st := some 2, left := [2, 2, 2, 2, 3, 3, 3], cur := 8, right := [5] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 8, 5] }) := rfl
  have h2 : steps tm_4_9 105 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 8, 5] }) := steps_add tm_4_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_4_9 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 3], cur := 3, right := [3, 3, 8, 5] }) = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 8, 5] }) := rfl
  have h3 : steps tm_4_9 140 initConfig = some ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 8, 5] }) := steps_add tm_4_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_4_9 35 ({ st := some 2, left := [2, 2, 2, 2, 2, 2, 2, 2, 2], cur := 2, right := [3, 8, 5] }) = some ({ st := some 2, left := [3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 8] }) := rfl
  have h4 : steps tm_4_9 175 initConfig = some ({ st := some 2, left := [3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 8] }) := steps_add tm_4_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_4_9 35 ({ st := some 2, left := [3], cur := 2, right := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 8] }) = some ({ st := some 0, left := [2, 3], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h5 : steps tm_4_9 210 initConfig = some ({ st := some 0, left := [2, 3], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_4_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_4_9 35 ({ st := some 0, left := [2, 3], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 1, left := [3, 3, 3], cur := 4, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h6 : steps tm_4_9 245 initConfig = some ({ st := some 1, left := [3, 3, 3], cur := 4, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_4_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_4_9 35 ({ st := some 1, left := [3, 3, 3], cur := 4, right := [6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h7 : steps tm_4_9 280 initConfig = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_4_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_4_9 24 ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h8 : steps tm_4_9 304 initConfig = some ({ st := some 0, left := [2, 3], cur := 1, right := [1, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_4_9 280 24 initConfig _ _ h7 hstep8
  exact h8

/-! ### BB(5,9) — > f_{ω×2+1}(80) (`fwm21_8_blank` @ step 8294) -/
def tm_5_9 : TM
  | 0, 0 => some ⟨8, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 3⟩
  | 0, 3 => some ⟨2, Dir.R, some 1⟩
  | 0, 5 => some ⟨7, Dir.L, some 4⟩
  | 0, 6 => some ⟨4, Dir.L, some 3⟩
  | 0, 7 => some ⟨3, Dir.L, some 2⟩
  | 0, 8 => some ⟨0, Dir.R, some 2⟩
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.L, some 0⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 1⟩
  | 1, 4 => some ⟨6, Dir.L, some 4⟩
  | 1, 5 => some ⟨3, Dir.L, some 2⟩
  | 1, 6 => some ⟨5, Dir.R, some 1⟩
  | 1, 7 => some ⟨7, Dir.L, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 0⟩
  | 2, 1 => some ⟨1, Dir.L, some 0⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨1, Dir.L, some 2⟩
  | 2, 7 => some ⟨7, Dir.L, some 2⟩
  | 2, 8 => some ⟨7, Dir.R, some 3⟩
  | 3, 0 => some ⟨6, Dir.R, some 4⟩
  | 3, 1 => some ⟨2, Dir.R, some 0⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 4⟩
  | 3, 5 => some ⟨6, Dir.L, some 3⟩
  | 3, 6 => some ⟨5, Dir.R, some 3⟩
  | 3, 7 => some ⟨6, Dir.L, some 1⟩
  | 3, 8 => some ⟨7, Dir.L, some 3⟩
  | 4, 0 => some ⟨8, Dir.R, some 0⟩
  | 4, 1 => some ⟨5, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 4⟩
  | 4, 3 => some ⟨5, Dir.L, some 4⟩
  | 4, 4 => some ⟨6, Dir.R, some 4⟩
  | 4, 5 => some ⟨4, Dir.L, some 3⟩
  | 4, 6 => some ⟨5, Dir.R, some 1⟩
  | 4, 7 => some ⟨5, Dir.L, some 4⟩
  | 4, 8 => some ⟨1, Dir.L, some 3⟩
  | _, _ => none

theorem valid_5_9 : ValidTM 5 9 tm_5_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 9 => omega
    | 1 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 8 => trivial | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 4 => trivial | _ + 9 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | _ + 5 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 5 => rfl

def landmark_5_9 : Config := { st := some 1, left := [2, 2, 3], cur := 1, right := [1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
set_option maxHeartbeats 800000 in
theorem reaches_landmark_5_9 : steps tm_5_9 8294 initConfig = some landmark_5_9 := by
  have h0 : steps tm_5_9 35 initConfig = some ({ st := some 0, left := [3], cur := 3, right := [1, 4, 4, 6, 7, 7] }) := rfl
  have hstep1 : steps tm_5_9 35 ({ st := some 0, left := [3], cur := 3, right := [1, 4, 4, 6, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 6, 5, 4, 4, 6, 7, 7] }) := rfl
  have h1 : steps tm_5_9 70 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 6, 5, 4, 4, 6, 7, 7] }) := steps_add tm_5_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 6, 5, 4, 4, 6, 7, 7] }) = some ({ st := some 0, left := [8], cur := 5, right := [5, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h2 : steps tm_5_9 105 initConfig = some ({ st := some 0, left := [8], cur := 5, right := [5, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_5_9 35 ({ st := some 0, left := [8], cur := 5, right := [5, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6], cur := 4, right := [4, 4, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h3 : steps tm_5_9 140 initConfig = some ({ st := some 3, left := [5, 6, 6], cur := 4, right := [4, 4, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6], cur := 4, right := [4, 4, 5, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [5], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h4 : steps tm_5_9 175 initConfig = some ({ st := some 3, left := [5], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_5_9 35 ({ st := some 3, left := [5], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h5 : steps tm_5_9 210 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h6 : steps tm_5_9 245 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 5, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h7 : steps tm_5_9 280 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 6, 4, 6, 7, 7] }) := rfl
  have h8 : steps tm_5_9 315 initConfig = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) := rfl
  have h9 : steps tm_5_9 350 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) := rfl
  have h10 : steps tm_5_9 385 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) := steps_add tm_5_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 1, 6, 4, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h11 : steps tm_5_9 420 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h12 : steps tm_5_9 455 initConfig = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h13 : steps tm_5_9 490 initConfig = some ({ st := some 4, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h14 : steps tm_5_9 525 initConfig = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_5_9 35 ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h15 : steps tm_5_9 560 initConfig = some ({ st := some 4, left := [6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h16 : steps tm_5_9 595 initConfig = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_5_9 35 ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h17 : steps tm_5_9 630 initConfig = some ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h18 : steps tm_5_9 665 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h19 : steps tm_5_9 700 initConfig = some ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h20 : steps tm_5_9 735 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h21 : steps tm_5_9 770 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h22 : steps tm_5_9 805 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h23 : steps tm_5_9 840 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h24 : steps tm_5_9 875 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h25 : steps tm_5_9 910 initConfig = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_5_9 35 ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h26 : steps tm_5_9 945 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h27 : steps tm_5_9 980 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h28 : steps tm_5_9 1015 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h29 : steps tm_5_9 1050 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h30 : steps tm_5_9 1085 initConfig = some ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_5_9 35 ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h31 : steps tm_5_9 1120 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h32 : steps tm_5_9 1155 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h33 : steps tm_5_9 1190 initConfig = some ({ st := some 3, left := [5, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_5_9 35 ({ st := some 3, left := [5, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h34 : steps tm_5_9 1225 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h35 : steps tm_5_9 1260 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h36 : steps tm_5_9 1295 initConfig = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h37 : steps tm_5_9 1330 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h38 : steps tm_5_9 1365 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h39 : steps tm_5_9 1400 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1365 35 initConfig _ _ h38 hstep39
  have hstep40 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := rfl
  have h40 : steps tm_5_9 1435 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1400 35 initConfig _ _ h39 hstep40
  have hstep41 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := rfl
  have h41 : steps tm_5_9 1470 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1435 35 initConfig _ _ h40 hstep41
  have hstep42 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := rfl
  have h42 : steps tm_5_9 1505 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1470 35 initConfig _ _ h41 hstep42
  have hstep43 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := rfl
  have h43 : steps tm_5_9 1540 initConfig = some ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1505 35 initConfig _ _ h42 hstep43
  have hstep44 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := rfl
  have h44 : steps tm_5_9 1575 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1540 35 initConfig _ _ h43 hstep44
  have hstep45 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := rfl
  have h45 : steps tm_5_9 1610 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1575 35 initConfig _ _ h44 hstep45
  have hstep46 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := rfl
  have h46 : steps tm_5_9 1645 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1610 35 initConfig _ _ h45 hstep46
  have hstep47 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := rfl
  have h47 : steps tm_5_9 1680 initConfig = some ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1645 35 initConfig _ _ h46 hstep47
  have hstep48 : steps tm_5_9 35 ({ st := some 4, left := [6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := rfl
  have h48 : steps tm_5_9 1715 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) := steps_add tm_5_9 1680 35 initConfig _ _ h47 hstep48
  have hstep49 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 6, 4, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := rfl
  have h49 : steps tm_5_9 1750 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := steps_add tm_5_9 1715 35 initConfig _ _ h48 hstep49
  have hstep50 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := rfl
  have h50 : steps tm_5_9 1785 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := steps_add tm_5_9 1750 35 initConfig _ _ h49 hstep50
  have hstep51 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := rfl
  have h51 : steps tm_5_9 1820 initConfig = some ({ st := some 4, left := [6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := steps_add tm_5_9 1785 35 initConfig _ _ h50 hstep51
  have hstep52 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := rfl
  have h52 : steps tm_5_9 1855 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) := steps_add tm_5_9 1820 35 initConfig _ _ h51 hstep52
  have hstep53 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h53 : steps tm_5_9 1890 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 1855 35 initConfig _ _ h52 hstep53
  have hstep54 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h54 : steps tm_5_9 1925 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 1890 35 initConfig _ _ h53 hstep54
  have hstep55 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h55 : steps tm_5_9 1960 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 1925 35 initConfig _ _ h54 hstep55
  have hstep56 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h56 : steps tm_5_9 1995 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 1960 35 initConfig _ _ h55 hstep56
  have hstep57 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h57 : steps tm_5_9 2030 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 1995 35 initConfig _ _ h56 hstep57
  have hstep58 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h58 : steps tm_5_9 2065 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2030 35 initConfig _ _ h57 hstep58
  have hstep59 : steps tm_5_9 35 ({ st := some 4, left := [], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h59 : steps tm_5_9 2100 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2065 35 initConfig _ _ h58 hstep59
  have hstep60 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h60 : steps tm_5_9 2135 initConfig = some ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2100 35 initConfig _ _ h59 hstep60
  have hstep61 : steps tm_5_9 35 ({ st := some 3, left := [], cur := 0, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h61 : steps tm_5_9 2170 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2135 35 initConfig _ _ h60 hstep61
  have hstep62 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h62 : steps tm_5_9 2205 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2170 35 initConfig _ _ h61 hstep62
  have hstep63 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h63 : steps tm_5_9 2240 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2205 35 initConfig _ _ h62 hstep63
  have hstep64 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h64 : steps tm_5_9 2275 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2240 35 initConfig _ _ h63 hstep64
  have hstep65 : steps tm_5_9 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h65 : steps tm_5_9 2310 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2275 35 initConfig _ _ h64 hstep65
  have hstep66 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h66 : steps tm_5_9 2345 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2310 35 initConfig _ _ h65 hstep66
  have hstep67 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h67 : steps tm_5_9 2380 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2345 35 initConfig _ _ h66 hstep67
  have hstep68 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h68 : steps tm_5_9 2415 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2380 35 initConfig _ _ h67 hstep68
  have hstep69 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h69 : steps tm_5_9 2450 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2415 35 initConfig _ _ h68 hstep69
  have hstep70 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h70 : steps tm_5_9 2485 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2450 35 initConfig _ _ h69 hstep70
  have hstep71 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h71 : steps tm_5_9 2520 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2485 35 initConfig _ _ h70 hstep71
  have hstep72 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h72 : steps tm_5_9 2555 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2520 35 initConfig _ _ h71 hstep72
  have hstep73 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h73 : steps tm_5_9 2590 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2555 35 initConfig _ _ h72 hstep73
  have hstep74 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h74 : steps tm_5_9 2625 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2590 35 initConfig _ _ h73 hstep74
  have hstep75 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h75 : steps tm_5_9 2660 initConfig = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2625 35 initConfig _ _ h74 hstep75
  have hstep76 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h76 : steps tm_5_9 2695 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2660 35 initConfig _ _ h75 hstep76
  have hstep77 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h77 : steps tm_5_9 2730 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2695 35 initConfig _ _ h76 hstep77
  have hstep78 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h78 : steps tm_5_9 2765 initConfig = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2730 35 initConfig _ _ h77 hstep78
  have hstep79 : steps tm_5_9 35 ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h79 : steps tm_5_9 2800 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2765 35 initConfig _ _ h78 hstep79
  have hstep80 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h80 : steps tm_5_9 2835 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2800 35 initConfig _ _ h79 hstep80
  have hstep81 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h81 : steps tm_5_9 2870 initConfig = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2835 35 initConfig _ _ h80 hstep81
  have hstep82 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h82 : steps tm_5_9 2905 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2870 35 initConfig _ _ h81 hstep82
  have hstep83 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h83 : steps tm_5_9 2940 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2905 35 initConfig _ _ h82 hstep83
  have hstep84 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h84 : steps tm_5_9 2975 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2940 35 initConfig _ _ h83 hstep84
  have hstep85 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h85 : steps tm_5_9 3010 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 2975 35 initConfig _ _ h84 hstep85
  have hstep86 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h86 : steps tm_5_9 3045 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3010 35 initConfig _ _ h85 hstep86
  have hstep87 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h87 : steps tm_5_9 3080 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3045 35 initConfig _ _ h86 hstep87
  have hstep88 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h88 : steps tm_5_9 3115 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3080 35 initConfig _ _ h87 hstep88
  have hstep89 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h89 : steps tm_5_9 3150 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3115 35 initConfig _ _ h88 hstep89
  have hstep90 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h90 : steps tm_5_9 3185 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3150 35 initConfig _ _ h89 hstep90
  have hstep91 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h91 : steps tm_5_9 3220 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3185 35 initConfig _ _ h90 hstep91
  have hstep92 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h92 : steps tm_5_9 3255 initConfig = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3220 35 initConfig _ _ h91 hstep92
  have hstep93 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h93 : steps tm_5_9 3290 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3255 35 initConfig _ _ h92 hstep93
  have hstep94 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h94 : steps tm_5_9 3325 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3290 35 initConfig _ _ h93 hstep94
  have hstep95 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h95 : steps tm_5_9 3360 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3325 35 initConfig _ _ h94 hstep95
  have hstep96 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h96 : steps tm_5_9 3395 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3360 35 initConfig _ _ h95 hstep96
  have hstep97 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h97 : steps tm_5_9 3430 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3395 35 initConfig _ _ h96 hstep97
  have hstep98 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h98 : steps tm_5_9 3465 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3430 35 initConfig _ _ h97 hstep98
  have hstep99 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h99 : steps tm_5_9 3500 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3465 35 initConfig _ _ h98 hstep99
  have hstep100 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h100 : steps tm_5_9 3535 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3500 35 initConfig _ _ h99 hstep100
  have hstep101 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h101 : steps tm_5_9 3570 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3535 35 initConfig _ _ h100 hstep101
  have hstep102 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h102 : steps tm_5_9 3605 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3570 35 initConfig _ _ h101 hstep102
  have hstep103 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h103 : steps tm_5_9 3640 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3605 35 initConfig _ _ h102 hstep103
  have hstep104 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h104 : steps tm_5_9 3675 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3640 35 initConfig _ _ h103 hstep104
  have hstep105 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h105 : steps tm_5_9 3710 initConfig = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3675 35 initConfig _ _ h104 hstep105
  have hstep106 : steps tm_5_9 35 ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h106 : steps tm_5_9 3745 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3710 35 initConfig _ _ h105 hstep106
  have hstep107 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h107 : steps tm_5_9 3780 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3745 35 initConfig _ _ h106 hstep107
  have hstep108 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h108 : steps tm_5_9 3815 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3780 35 initConfig _ _ h107 hstep108
  have hstep109 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h109 : steps tm_5_9 3850 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3815 35 initConfig _ _ h108 hstep109
  have hstep110 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h110 : steps tm_5_9 3885 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3850 35 initConfig _ _ h109 hstep110
  have hstep111 : steps tm_5_9 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h111 : steps tm_5_9 3920 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3885 35 initConfig _ _ h110 hstep111
  have hstep112 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h112 : steps tm_5_9 3955 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3920 35 initConfig _ _ h111 hstep112
  have hstep113 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h113 : steps tm_5_9 3990 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3955 35 initConfig _ _ h112 hstep113
  have hstep114 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h114 : steps tm_5_9 4025 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 3990 35 initConfig _ _ h113 hstep114
  have hstep115 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h115 : steps tm_5_9 4060 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4025 35 initConfig _ _ h114 hstep115
  have hstep116 : steps tm_5_9 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h116 : steps tm_5_9 4095 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4060 35 initConfig _ _ h115 hstep116
  have hstep117 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h117 : steps tm_5_9 4130 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4095 35 initConfig _ _ h116 hstep117
  have hstep118 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h118 : steps tm_5_9 4165 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4130 35 initConfig _ _ h117 hstep118
  have hstep119 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h119 : steps tm_5_9 4200 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4165 35 initConfig _ _ h118 hstep119
  have hstep120 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h120 : steps tm_5_9 4235 initConfig = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4200 35 initConfig _ _ h119 hstep120
  have hstep121 : steps tm_5_9 35 ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h121 : steps tm_5_9 4270 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4235 35 initConfig _ _ h120 hstep121
  have hstep122 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h122 : steps tm_5_9 4305 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4270 35 initConfig _ _ h121 hstep122
  have hstep123 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h123 : steps tm_5_9 4340 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4305 35 initConfig _ _ h122 hstep123
  have hstep124 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h124 : steps tm_5_9 4375 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4340 35 initConfig _ _ h123 hstep124
  have hstep125 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h125 : steps tm_5_9 4410 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4375 35 initConfig _ _ h124 hstep125
  have hstep126 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h126 : steps tm_5_9 4445 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4410 35 initConfig _ _ h125 hstep126
  have hstep127 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h127 : steps tm_5_9 4480 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4445 35 initConfig _ _ h126 hstep127
  have hstep128 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h128 : steps tm_5_9 4515 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4480 35 initConfig _ _ h127 hstep128
  have hstep129 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h129 : steps tm_5_9 4550 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4515 35 initConfig _ _ h128 hstep129
  have hstep130 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h130 : steps tm_5_9 4585 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4550 35 initConfig _ _ h129 hstep130
  have hstep131 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h131 : steps tm_5_9 4620 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4585 35 initConfig _ _ h130 hstep131
  have hstep132 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h132 : steps tm_5_9 4655 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4620 35 initConfig _ _ h131 hstep132
  have hstep133 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h133 : steps tm_5_9 4690 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4655 35 initConfig _ _ h132 hstep133
  have hstep134 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h134 : steps tm_5_9 4725 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4690 35 initConfig _ _ h133 hstep134
  have hstep135 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h135 : steps tm_5_9 4760 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4725 35 initConfig _ _ h134 hstep135
  have hstep136 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h136 : steps tm_5_9 4795 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4760 35 initConfig _ _ h135 hstep136
  have hstep137 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h137 : steps tm_5_9 4830 initConfig = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4795 35 initConfig _ _ h136 hstep137
  have hstep138 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h138 : steps tm_5_9 4865 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4830 35 initConfig _ _ h137 hstep138
  have hstep139 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h139 : steps tm_5_9 4900 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4865 35 initConfig _ _ h138 hstep139
  have hstep140 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h140 : steps tm_5_9 4935 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4900 35 initConfig _ _ h139 hstep140
  have hstep141 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h141 : steps tm_5_9 4970 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4935 35 initConfig _ _ h140 hstep141
  have hstep142 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h142 : steps tm_5_9 5005 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 4970 35 initConfig _ _ h141 hstep142
  have hstep143 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h143 : steps tm_5_9 5040 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5005 35 initConfig _ _ h142 hstep143
  have hstep144 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h144 : steps tm_5_9 5075 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5040 35 initConfig _ _ h143 hstep144
  have hstep145 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h145 : steps tm_5_9 5110 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5075 35 initConfig _ _ h144 hstep145
  have hstep146 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h146 : steps tm_5_9 5145 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5110 35 initConfig _ _ h145 hstep146
  have hstep147 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h147 : steps tm_5_9 5180 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5145 35 initConfig _ _ h146 hstep147
  have hstep148 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h148 : steps tm_5_9 5215 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5180 35 initConfig _ _ h147 hstep148
  have hstep149 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h149 : steps tm_5_9 5250 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5215 35 initConfig _ _ h148 hstep149
  have hstep150 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h150 : steps tm_5_9 5285 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5250 35 initConfig _ _ h149 hstep150
  have hstep151 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h151 : steps tm_5_9 5320 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5285 35 initConfig _ _ h150 hstep151
  have hstep152 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h152 : steps tm_5_9 5355 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5320 35 initConfig _ _ h151 hstep152
  have hstep153 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h153 : steps tm_5_9 5390 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5355 35 initConfig _ _ h152 hstep153
  have hstep154 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h154 : steps tm_5_9 5425 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5390 35 initConfig _ _ h153 hstep154
  have hstep155 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h155 : steps tm_5_9 5460 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5425 35 initConfig _ _ h154 hstep155
  have hstep156 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h156 : steps tm_5_9 5495 initConfig = some ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5460 35 initConfig _ _ h155 hstep156
  have hstep157 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h157 : steps tm_5_9 5530 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5495 35 initConfig _ _ h156 hstep157
  have hstep158 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h158 : steps tm_5_9 5565 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5530 35 initConfig _ _ h157 hstep158
  have hstep159 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h159 : steps tm_5_9 5600 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5565 35 initConfig _ _ h158 hstep159
  have hstep160 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h160 : steps tm_5_9 5635 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5600 35 initConfig _ _ h159 hstep160
  have hstep161 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h161 : steps tm_5_9 5670 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5635 35 initConfig _ _ h160 hstep161
  have hstep162 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h162 : steps tm_5_9 5705 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5670 35 initConfig _ _ h161 hstep162
  have hstep163 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h163 : steps tm_5_9 5740 initConfig = some ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5705 35 initConfig _ _ h162 hstep163
  have hstep164 : steps tm_5_9 35 ({ st := some 3, left := [6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h164 : steps tm_5_9 5775 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5740 35 initConfig _ _ h163 hstep164
  have hstep165 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h165 : steps tm_5_9 5810 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5775 35 initConfig _ _ h164 hstep165
  have hstep166 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h166 : steps tm_5_9 5845 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5810 35 initConfig _ _ h165 hstep166
  have hstep167 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h167 : steps tm_5_9 5880 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5845 35 initConfig _ _ h166 hstep167
  have hstep168 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h168 : steps tm_5_9 5915 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5880 35 initConfig _ _ h167 hstep168
  have hstep169 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h169 : steps tm_5_9 5950 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5915 35 initConfig _ _ h168 hstep169
  have hstep170 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h170 : steps tm_5_9 5985 initConfig = some ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5950 35 initConfig _ _ h169 hstep170
  have hstep171 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h171 : steps tm_5_9 6020 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 5985 35 initConfig _ _ h170 hstep171
  have hstep172 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h172 : steps tm_5_9 6055 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6020 35 initConfig _ _ h171 hstep172
  have hstep173 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h173 : steps tm_5_9 6090 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6055 35 initConfig _ _ h172 hstep173
  have hstep174 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h174 : steps tm_5_9 6125 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6090 35 initConfig _ _ h173 hstep174
  have hstep175 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h175 : steps tm_5_9 6160 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6125 35 initConfig _ _ h174 hstep175
  have hstep176 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h176 : steps tm_5_9 6195 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6160 35 initConfig _ _ h175 hstep176
  have hstep177 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h177 : steps tm_5_9 6230 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6195 35 initConfig _ _ h176 hstep177
  have hstep178 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h178 : steps tm_5_9 6265 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6230 35 initConfig _ _ h177 hstep178
  have hstep179 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h179 : steps tm_5_9 6300 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6265 35 initConfig _ _ h178 hstep179
  have hstep180 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h180 : steps tm_5_9 6335 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6300 35 initConfig _ _ h179 hstep180
  have hstep181 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h181 : steps tm_5_9 6370 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6335 35 initConfig _ _ h180 hstep181
  have hstep182 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h182 : steps tm_5_9 6405 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6370 35 initConfig _ _ h181 hstep182
  have hstep183 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h183 : steps tm_5_9 6440 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6405 35 initConfig _ _ h182 hstep183
  have hstep184 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h184 : steps tm_5_9 6475 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6440 35 initConfig _ _ h183 hstep184
  have hstep185 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h185 : steps tm_5_9 6510 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6475 35 initConfig _ _ h184 hstep185
  have hstep186 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h186 : steps tm_5_9 6545 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6510 35 initConfig _ _ h185 hstep186
  have hstep187 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h187 : steps tm_5_9 6580 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6545 35 initConfig _ _ h186 hstep187
  have hstep188 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [6, 4, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h188 : steps tm_5_9 6615 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6580 35 initConfig _ _ h187 hstep188
  have hstep189 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h189 : steps tm_5_9 6650 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6615 35 initConfig _ _ h188 hstep189
  have hstep190 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h190 : steps tm_5_9 6685 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6650 35 initConfig _ _ h189 hstep190
  have hstep191 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h191 : steps tm_5_9 6720 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6685 35 initConfig _ _ h190 hstep191
  have hstep192 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h192 : steps tm_5_9 6755 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6720 35 initConfig _ _ h191 hstep192
  have hstep193 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h193 : steps tm_5_9 6790 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6755 35 initConfig _ _ h192 hstep193
  have hstep194 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := rfl
  have h194 : steps tm_5_9 6825 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6790 35 initConfig _ _ h193 hstep194
  have hstep195 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h195 : steps tm_5_9 6860 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6825 35 initConfig _ _ h194 hstep195
  have hstep196 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h196 : steps tm_5_9 6895 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6860 35 initConfig _ _ h195 hstep196
  have hstep197 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h197 : steps tm_5_9 6930 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6895 35 initConfig _ _ h196 hstep197
  have hstep198 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h198 : steps tm_5_9 6965 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6930 35 initConfig _ _ h197 hstep198
  have hstep199 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h199 : steps tm_5_9 7000 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 6965 35 initConfig _ _ h198 hstep199
  have hstep200 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h200 : steps tm_5_9 7035 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7000 35 initConfig _ _ h199 hstep200
  have hstep201 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h201 : steps tm_5_9 7070 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7035 35 initConfig _ _ h200 hstep201
  have hstep202 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := rfl
  have h202 : steps tm_5_9 7105 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7070 35 initConfig _ _ h201 hstep202
  have hstep203 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h203 : steps tm_5_9 7140 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7105 35 initConfig _ _ h202 hstep203
  have hstep204 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h204 : steps tm_5_9 7175 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7140 35 initConfig _ _ h203 hstep204
  have hstep205 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h205 : steps tm_5_9 7210 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7175 35 initConfig _ _ h204 hstep205
  have hstep206 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h206 : steps tm_5_9 7245 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7210 35 initConfig _ _ h205 hstep206
  have hstep207 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h207 : steps tm_5_9 7280 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7245 35 initConfig _ _ h206 hstep207
  have hstep208 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h208 : steps tm_5_9 7315 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7280 35 initConfig _ _ h207 hstep208
  have hstep209 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h209 : steps tm_5_9 7350 initConfig = some ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7315 35 initConfig _ _ h208 hstep209
  have hstep210 : steps tm_5_9 35 ({ st := some 4, left := [], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h210 : steps tm_5_9 7385 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7350 35 initConfig _ _ h209 hstep210
  have hstep211 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 7, 7, 7] }) := rfl
  have h211 : steps tm_5_9 7420 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 7, 7, 7] }) := steps_add tm_5_9 7385 35 initConfig _ _ h210 hstep211
  have hstep212 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 6, 4, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h212 : steps tm_5_9 7455 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7420 35 initConfig _ _ h211 hstep212
  have hstep213 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h213 : steps tm_5_9 7490 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7455 35 initConfig _ _ h212 hstep213
  have hstep214 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h214 : steps tm_5_9 7525 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7490 35 initConfig _ _ h213 hstep214
  have hstep215 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h215 : steps tm_5_9 7560 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7525 35 initConfig _ _ h214 hstep215
  have hstep216 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h216 : steps tm_5_9 7595 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7560 35 initConfig _ _ h215 hstep216
  have hstep217 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h217 : steps tm_5_9 7630 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7595 35 initConfig _ _ h216 hstep217
  have hstep218 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h218 : steps tm_5_9 7665 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7630 35 initConfig _ _ h217 hstep218
  have hstep219 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := rfl
  have h219 : steps tm_5_9 7700 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) := steps_add tm_5_9 7665 35 initConfig _ _ h218 hstep219
  have hstep220 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 4, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h220 : steps tm_5_9 7735 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7700 35 initConfig _ _ h219 hstep220
  have hstep221 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h221 : steps tm_5_9 7770 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7735 35 initConfig _ _ h220 hstep221
  have hstep222 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h222 : steps tm_5_9 7805 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7770 35 initConfig _ _ h221 hstep222
  have hstep223 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h223 : steps tm_5_9 7840 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7805 35 initConfig _ _ h222 hstep223
  have hstep224 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h224 : steps tm_5_9 7875 initConfig = some ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7840 35 initConfig _ _ h223 hstep224
  have hstep225 : steps tm_5_9 35 ({ st := some 3, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h225 : steps tm_5_9 7910 initConfig = some ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7875 35 initConfig _ _ h224 hstep225
  have hstep226 : steps tm_5_9 35 ({ st := some 3, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h226 : steps tm_5_9 7945 initConfig = some ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7910 35 initConfig _ _ h225 hstep226
  have hstep227 : steps tm_5_9 35 ({ st := some 4, left := [6], cur := 5, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h227 : steps tm_5_9 7980 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7945 35 initConfig _ _ h226 hstep227
  have hstep228 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := rfl
  have h228 : steps tm_5_9 8015 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) := steps_add tm_5_9 7980 35 initConfig _ _ h227 hstep228
  have hstep229 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h229 : steps tm_5_9 8050 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8015 35 initConfig _ _ h228 hstep229
  have hstep230 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h230 : steps tm_5_9 8085 initConfig = some ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8050 35 initConfig _ _ h229 hstep230
  have hstep231 : steps tm_5_9 35 ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h231 : steps tm_5_9 8120 initConfig = some ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8085 35 initConfig _ _ h230 hstep231
  have hstep232 : steps tm_5_9 35 ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h232 : steps tm_5_9 8155 initConfig = some ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8120 35 initConfig _ _ h231 hstep232
  have hstep233 : steps tm_5_9 35 ({ st := some 4, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 6, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h233 : steps tm_5_9 8190 initConfig = some ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8155 35 initConfig _ _ h232 hstep233
  have hstep234 : steps tm_5_9 35 ({ st := some 0, left := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 5, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h234 : steps tm_5_9 8225 initConfig = some ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8190 35 initConfig _ _ h233 hstep234
  have hstep235 : steps tm_5_9 35 ({ st := some 1, left := [5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], cur := 7, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 4, left := [], cur := 0, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h235 : steps tm_5_9 8260 initConfig = some ({ st := some 4, left := [], cur := 0, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8225 35 initConfig _ _ h234 hstep235
  have hstep236 : steps tm_5_9 34 ({ st := some 4, left := [], cur := 0, right := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h236 : steps tm_5_9 8294 initConfig = some ({ st := some 1, left := [2, 2, 3], cur := 1, right := [1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_5_9 8260 34 initConfig _ _ h235 hstep236
  exact h236

/-! ### BB(11,9) — > f_{ω^ω+3}(35) (`fwpw3_8_blank` @ step 1390) -/
def tm_11_9 : TM
  | 0, 0 => some ⟨8, Dir.L, some 10⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨7, Dir.R, some 6⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => some ⟨2, Dir.R, some 9⟩
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
  | 5, 8 => some ⟨6, Dir.L, some 10⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 6 => some ⟨3, Dir.L, some 6⟩
  | 6, 7 => some ⟨2, Dir.L, some 3⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨2, Dir.L, some 3⟩
  | 7, 8 => some ⟨1, Dir.R, some 6⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 1 => some ⟨1, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨8, Dir.L, some 5⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 7 => some ⟨0, Dir.L, some 6⟩
  | 10, 8 => some ⟨8, Dir.R, some 5⟩
  | _, _ => none

theorem valid_11_9 : ValidTM 11 9 tm_11_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 3 | 4 | 7 | 8 => exact ⟨by decide, by decide⟩ | 2 | 5 | 6 => trivial | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 8 => trivial | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 8 => trivial | _ + 9 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 9 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 10 => match sym with | 0 | 2 | 3 | 4 | 5 | 7 | 8 => exact ⟨by decide, by decide⟩ | 1 | 6 => trivial | _ + 9 => omega
    | _ + 11 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 11 => rfl

def landmark_11_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }
theorem reaches_landmark_11_9 : steps tm_11_9 1390 initConfig = some landmark_11_9 := by
  have h0 : steps tm_11_9 35 initConfig = some ({ st := some 3, left := [3, 3, 3], cur := 3, right := [1, 3, 4, 1, 0, 8] }) := rfl
  have hstep1 : steps tm_11_9 35 ({ st := some 3, left := [3, 3, 3], cur := 3, right := [1, 3, 4, 1, 0, 8] }) = some ({ st := some 1, left := [7, 7, 7], cur := 4, right := [4, 4, 4, 4, 1, 0, 8] }) := rfl
  have h1 : steps tm_11_9 70 initConfig = some ({ st := some 1, left := [7, 7, 7], cur := 4, right := [4, 4, 4, 4, 1, 0, 8] }) := steps_add tm_11_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_11_9 35 ({ st := some 1, left := [7, 7, 7], cur := 4, right := [4, 4, 4, 4, 1, 0, 8] }) = some ({ st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 1, 0, 8] }) := rfl
  have h2 : steps tm_11_9 105 initConfig = some ({ st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 1, 0, 8] }) := steps_add tm_11_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3], cur := 3, right := [1, 1, 3, 4, 4, 4, 4, 1, 0, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 1, 0, 8] }) := rfl
  have h3 : steps tm_11_9 140 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 1, 0, 8] }) := steps_add tm_11_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 3, 4, 4, 1, 0, 8] }) = some ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 0, 8] }) := rfl
  have h4 : steps tm_11_9 175 initConfig = some ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 0, 8] }) := steps_add tm_11_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 0, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 0, 8] }) := rfl
  have h5 : steps tm_11_9 210 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 0, 8] }) := steps_add tm_11_9 175 35 initConfig _ _ h4 hstep5
  have hstep6 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 3, 1, 0, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 0, 8] }) := rfl
  have h6 : steps tm_11_9 245 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 0, 8] }) := steps_add tm_11_9 210 35 initConfig _ _ h5 hstep6
  have hstep7 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 0, 8] }) = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [3, 0, 8] }) := rfl
  have h7 : steps tm_11_9 280 initConfig = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [3, 0, 8] }) := steps_add tm_11_9 245 35 initConfig _ _ h6 hstep7
  have hstep8 : steps tm_11_9 35 ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [3, 0, 8] }) = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h8 : steps tm_11_9 315 initConfig = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 280 35 initConfig _ _ h7 hstep8
  have hstep9 : steps tm_11_9 35 ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 4, left := [7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h9 : steps tm_11_9 350 initConfig = some ({ st := some 4, left := [7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 315 35 initConfig _ _ h8 hstep9
  have hstep10 : steps tm_11_9 35 ({ st := some 4, left := [7, 7], cur := 7, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 7, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h10 : steps tm_11_9 385 initConfig = some ({ st := some 7, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 350 35 initConfig _ _ h9 hstep10
  have hstep11 : steps tm_11_9 35 ({ st := some 7, left := [2, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h11 : steps tm_11_9 420 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 385 35 initConfig _ _ h10 hstep11
  have hstep12 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h12 : steps tm_11_9 455 initConfig = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 420 35 initConfig _ _ h11 hstep12
  have hstep13 : steps tm_11_9 35 ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h13 : steps tm_11_9 490 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 455 35 initConfig _ _ h12 hstep13
  have hstep14 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h14 : steps tm_11_9 525 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 490 35 initConfig _ _ h13 hstep14
  have hstep15 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h15 : steps tm_11_9 560 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 525 35 initConfig _ _ h14 hstep15
  have hstep16 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h16 : steps tm_11_9 595 initConfig = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 560 35 initConfig _ _ h15 hstep16
  have hstep17 : steps tm_11_9 35 ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h17 : steps tm_11_9 630 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 595 35 initConfig _ _ h16 hstep17
  have hstep18 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h18 : steps tm_11_9 665 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 630 35 initConfig _ _ h17 hstep18
  have hstep19 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [3, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 8] }) := rfl
  have h19 : steps tm_11_9 700 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 665 35 initConfig _ _ h18 hstep19
  have hstep20 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 8] }) := rfl
  have h20 : steps tm_11_9 735 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 700 35 initConfig _ _ h19 hstep20
  have hstep21 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 4, 1, 8] }) = some ({ st := some 7, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 1, 8] }) := rfl
  have h21 : steps tm_11_9 770 initConfig = some ({ st := some 7, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 1, 8] }) := steps_add tm_11_9 735 35 initConfig _ _ h20 hstep21
  have hstep22 : steps tm_11_9 35 ({ st := some 7, left := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 4, right := [4, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 8] }) := rfl
  have h22 : steps tm_11_9 805 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 8] }) := steps_add tm_11_9 770 35 initConfig _ _ h21 hstep22
  have hstep23 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) := rfl
  have h23 : steps tm_11_9 840 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) := steps_add tm_11_9 805 35 initConfig _ _ h22 hstep23
  have hstep24 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) := rfl
  have h24 : steps tm_11_9 875 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) := steps_add tm_11_9 840 35 initConfig _ _ h23 hstep24
  have hstep25 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) := rfl
  have h25 : steps tm_11_9 910 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) := steps_add tm_11_9 875 35 initConfig _ _ h24 hstep25
  have hstep26 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) := rfl
  have h26 : steps tm_11_9 945 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) := steps_add tm_11_9 910 35 initConfig _ _ h25 hstep26
  have hstep27 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8] }) = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) := rfl
  have h27 : steps tm_11_9 980 initConfig = some ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) := steps_add tm_11_9 945 35 initConfig _ _ h26 hstep27
  have hstep28 : steps tm_11_9 35 ({ st := some 6, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) := rfl
  have h28 : steps tm_11_9 1015 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) := steps_add tm_11_9 980 35 initConfig _ _ h27 hstep28
  have hstep29 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] }) = some ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 8] }) := rfl
  have h29 : steps tm_11_9 1050 initConfig = some ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 8] }) := steps_add tm_11_9 1015 35 initConfig _ _ h28 hstep29
  have hstep30 : steps tm_11_9 35 ({ st := some 3, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 3, right := [1, 1, 1, 1, 1, 1, 1, 3, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := rfl
  have h30 : steps tm_11_9 1085 initConfig = some ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := steps_add tm_11_9 1050 35 initConfig _ _ h29 hstep30
  have hstep31 : steps tm_11_9 35 ({ st := some 1, left := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3], cur := 2, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) = some ({ st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := rfl
  have h31 : steps tm_11_9 1120 initConfig = some ({ st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := steps_add tm_11_9 1085 35 initConfig _ _ h30 hstep31
  have hstep32 : steps tm_11_9 35 ({ st := some 2, left := [2, 3, 3, 3, 3, 3], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := rfl
  have h32 : steps tm_11_9 1155 initConfig = some ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) := steps_add tm_11_9 1120 35 initConfig _ _ h31 hstep32
  have hstep33 : steps tm_11_9 35 ({ st := some 4, left := [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 1, right := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8] }) = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6] }) := rfl
  have h33 : steps tm_11_9 1190 initConfig = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6] }) := steps_add tm_11_9 1155 35 initConfig _ _ h32 hstep33
  have hstep34 : steps tm_11_9 35 ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6] }) = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h34 : steps tm_11_9 1225 initConfig = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1190 35 initConfig _ _ h33 hstep34
  have hstep35 : steps tm_11_9 35 ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h35 : steps tm_11_9 1260 initConfig = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1225 35 initConfig _ _ h34 hstep35
  have hstep36 : steps tm_11_9 35 ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h36 : steps tm_11_9 1295 initConfig = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1260 35 initConfig _ _ h35 hstep36
  have hstep37 : steps tm_11_9 35 ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h37 : steps tm_11_9 1330 initConfig = some ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1295 35 initConfig _ _ h36 hstep37
  have hstep38 : steps tm_11_9 35 ({ st := some 5, left := [4, 7, 7, 7, 7, 7, 7], cur := 8, right := [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h38 : steps tm_11_9 1365 initConfig = some ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1330 35 initConfig _ _ h37 hstep38
  have hstep39 : steps tm_11_9 25 ({ st := some 6, left := [], cur := 0, right := [1, 1, 1, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := rfl
  have h39 : steps tm_11_9 1390 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] }) := steps_add tm_11_9 1365 25 initConfig _ _ h38 hstep39
  exact h39

/-! ### BB(12,9) — > f_{ω^ω+4}(12) (`fwpw4_8_blank` @ step 194) -/
def tm_12_9 : TM
  | 0, 0 => some ⟨5, Dir.L, some 5⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨1, Dir.L, some 8⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨8, Dir.L, some 3⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨5, Dir.L, some 7⟩
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
  | 3, 8 => some ⟨1, Dir.L, some 4⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 4 => some ⟨8, Dir.R, some 6⟩
  | 4, 5 => some ⟨8, Dir.L, some 1⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 4, 8 => some ⟨7, Dir.L, some 11⟩
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
  | 7, 8 => some ⟨0, Dir.R, some 2⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 5 => some ⟨5, Dir.L, some 5⟩
  | 8, 6 => some ⟨7, Dir.L, some 8⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 6 => some ⟨7, Dir.R, some 2⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨7, Dir.L, some 11⟩
  | _, _ => none

theorem valid_12_9 : ValidTM 12 9 tm_12_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 => exact ⟨by decide, by decide⟩ | 6 => trivial | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 => exact ⟨by decide, by decide⟩ | 4 | 7 | 8 => trivial | _ + 9 => omega
    | 9 => match sym with | 0 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 7 | 8 => trivial | _ + 9 => omega
    | 10 => match sym with | 0 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 1 | 4 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 11 => match sym with | 0 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 8 => trivial | _ + 9 => omega
    | _ + 12 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 12 => rfl

def landmark_12_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem reaches_landmark_12_9 : steps tm_12_9 194 initConfig = some landmark_12_9 := by
  have h0 : steps tm_12_9 35 initConfig = some ({ st := some 9, left := [7, 7], cur := 6, right := [2, 2, 5] }) := rfl
  have hstep1 : steps tm_12_9 35 ({ st := some 9, left := [7, 7], cur := 6, right := [2, 2, 5] }) = some ({ st := some 4, left := [7], cur := 3, right := [4, 4, 8, 3, 1, 5] }) := rfl
  have h1 : steps tm_12_9 70 initConfig = some ({ st := some 4, left := [7], cur := 3, right := [4, 4, 8, 3, 1, 5] }) := steps_add tm_12_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_12_9 35 ({ st := some 4, left := [7], cur := 3, right := [4, 4, 8, 3, 1, 5] }) = some ({ st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 8, 3, 1, 5] }) := rfl
  have h2 : steps tm_12_9 105 initConfig = some ({ st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 8, 3, 1, 5] }) := steps_add tm_12_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_12_9 35 ({ st := some 1, left := [3, 3, 3, 3], cur := 1, right := [1, 1, 3, 8, 3, 1, 5] }) = some ({ st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 7, 7, 7, 8] }) := rfl
  have h3 : steps tm_12_9 140 initConfig = some ({ st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 7, 7, 7, 8] }) := steps_add tm_12_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_12_9 35 ({ st := some 2, left := [2], cur := 1, right := [1, 1, 1, 1, 1, 1, 7, 7, 7, 8] }) = some ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h4 : steps tm_12_9 175 initConfig = some ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_12_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_12_9 19 ({ st := some 11, left := [], cur := 0, right := [6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := rfl
  have h5 : steps tm_12_9 194 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }) := steps_add tm_12_9 175 19 initConfig _ _ h4 hstep5
  exact h5

/-! ### BB(13,9) — > f_{ω^ω+5}(5) (`fwpw5_13_9_blank` @ step 130) -/
def tm_13_9 : TM
  | 0, 0 => some ⟨7, Dir.L, some 10⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨4, Dir.R, some 4⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨2, Dir.R, some 0⟩
  | 0, 6 => some ⟨5, Dir.L, some 11⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨4, Dir.L, some 6⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => some ⟨4, Dir.R, some 0⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 2, 8 => some ⟨6, Dir.L, some 0⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 1 => some ⟨8, Dir.R, some 12⟩
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
  | 4, 4 => some ⟨8, Dir.L, some 12⟩
  | 4, 5 => some ⟨1, Dir.R, some 10⟩
  | 4, 6 => some ⟨8, Dir.L, some 4⟩
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
  | 6, 4 => some ⟨5, Dir.R, some 8⟩
  | 6, 5 => some ⟨8, Dir.L, some 3⟩
  | 6, 7 => some ⟨0, Dir.R, some 8⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨6, Dir.L, some 11⟩
  | 7, 8 => some ⟨7, Dir.L, some 12⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 4 => some ⟨8, Dir.L, some 6⟩
  | 8, 5 => some ⟨4, Dir.L, some 9⟩
  | 8, 8 => some ⟨1, Dir.L, some 6⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 4 => some ⟨5, Dir.L, some 1⟩
  | 9, 5 => some ⟨1, Dir.L, some 0⟩
  | 9, 8 => some ⟨5, Dir.L, some 0⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨3, Dir.R, some 6⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 4 => some ⟨4, Dir.R, some 7⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨1, Dir.R, some 5⟩
  | 10, 7 => some ⟨0, Dir.R, some 5⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 4 => some ⟨4, Dir.R, some 7⟩
  | 11, 5 => some ⟨0, Dir.L, some 6⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨1, Dir.R, some 3⟩
  | 12, 0 => some ⟨3, Dir.R, some 12⟩
  | 12, 1 => some ⟨8, Dir.R, some 5⟩
  | 12, 2 => some ⟨7, Dir.L, some 12⟩
  | 12, 3 => some ⟨7, Dir.L, some 12⟩
  | 12, 4 => some ⟨4, Dir.L, some 8⟩
  | 12, 7 => some ⟨2, Dir.R, some 7⟩
  | 12, 8 => some ⟨3, Dir.R, some 0⟩
  | _, _ => none

theorem valid_13_9 : ValidTM 13 9 tm_13_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 7 => exact ⟨by decide, by decide⟩ | 6 | 8 => trivial | _ + 9 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 8 => exact ⟨by decide, by decide⟩ | 6 | 7 => trivial | _ + 9 => omega
    | 9 => match sym with | 0 | 2 | 3 | 4 | 5 | 8 => exact ⟨by decide, by decide⟩ | 1 | 6 | 7 => trivial | _ + 9 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 11 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 8 => trivial | _ + 9 => omega
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 7 | 8 => exact ⟨by decide, by decide⟩ | 5 | 6 => trivial | _ + 9 => omega
    | _ + 13 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 13 => rfl

def landmark_13_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 8, 8, 8, 8, 8] }
theorem reaches_landmark_13_9 : steps tm_13_9 130 initConfig = some landmark_13_9 := by
  have h0 : steps tm_13_9 35 initConfig = some ({ st := some 0, left := [2, 4, 3, 3], cur := 2, right := [6] }) := rfl
  have hstep1 : steps tm_13_9 35 ({ st := some 0, left := [2, 4, 3, 3], cur := 2, right := [6] }) = some ({ st := some 8, left := [3, 3, 3], cur := 3, right := [4, 8, 8, 8] }) := rfl
  have h1 : steps tm_13_9 70 initConfig = some ({ st := some 8, left := [3, 3, 3], cur := 3, right := [4, 8, 8, 8] }) := steps_add tm_13_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_13_9 35 ({ st := some 8, left := [3, 3, 3], cur := 3, right := [4, 8, 8, 8] }) = some ({ st := some 12, left := [], cur := 3, right := [7, 7, 7, 7, 8, 8, 8, 8, 8] }) := rfl
  have h2 : steps tm_13_9 105 initConfig = some ({ st := some 12, left := [], cur := 3, right := [7, 7, 7, 7, 8, 8, 8, 8, 8] }) := steps_add tm_13_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_13_9 25 ({ st := some 12, left := [], cur := 3, right := [7, 7, 7, 7, 8, 8, 8, 8, 8] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 8, 8, 8, 8, 8] }) := rfl
  have h3 : steps tm_13_9 130 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 7, 7, 8, 8, 8, 8, 8] }) := steps_add tm_13_9 105 25 initConfig _ _ h2 hstep3
  exact h3

/-! ### BB(14,9) — > f_{ω^ω+5}(9) (`fwpw5_13_9_blank` @ step 165) -/
def tm_14_9 : TM
  | 0, 0 => some ⟨8, Dir.L, some 6⟩
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
  | 1, 8 => some ⟨0, Dir.R, some 6⟩
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
  | 5, 8 => some ⟨8, Dir.L, some 6⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨8, Dir.L, some 5⟩
  | 6, 7 => some ⟨0, Dir.L, some 4⟩
  | 7, 0 => some ⟨1, Dir.R, none⟩
  | 7, 1 => some ⟨3, Dir.L, some 1⟩
  | 7, 2 => some ⟨4, Dir.L, some 4⟩
  | 7, 3 => some ⟨2, Dir.R, some 7⟩
  | 7, 4 => some ⟨3, Dir.L, some 6⟩
  | 7, 5 => some ⟨2, Dir.L, some 9⟩
  | 7, 6 => some ⟨5, Dir.L, some 10⟩
  | 7, 7 => some ⟨6, Dir.L, some 11⟩
  | 7, 8 => some ⟨7, Dir.L, some 12⟩
  | 8, 0 => some ⟨3, Dir.R, some 8⟩
  | 8, 1 => some ⟨3, Dir.L, some 1⟩
  | 8, 2 => some ⟨2, Dir.R, some 8⟩
  | 8, 3 => some ⟨2, Dir.L, some 8⟩
  | 8, 8 => some ⟨7, Dir.L, some 10⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨2, Dir.R, some 13⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 12, 0 => some ⟨3, Dir.R, some 12⟩
  | 12, 2 => some ⟨7, Dir.L, some 12⟩
  | 12, 3 => some ⟨7, Dir.L, some 12⟩
  | 12, 7 => some ⟨2, Dir.R, some 7⟩
  | 13, 7 => some ⟨8, Dir.L, some 4⟩
  | _, _ => none

theorem valid_14_9 : ValidTM 14 9 tm_14_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 2 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 8 => trivial | _ + 9 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 1 | 8 => trivial | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | _ + 9 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 8 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 7 => trivial | _ + 9 => omega
    | 9 => match sym with | 0 | 2 | 3 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 5 => exact ⟨by decide, by decide⟩ | 4 | 6 | 7 | 8 => trivial | _ + 9 => omega
    | 11 => match sym with | 0 | 2 | 3 | 6 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 7 | 8 => trivial | _ + 9 => omega
    | 12 => match sym with | 0 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 13 => match sym with | 7 => exact ⟨by decide, by decide⟩ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | _ + 14 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 14 => rfl

def landmark_14_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }
theorem reaches_landmark_14_9 : steps tm_14_9 165 initConfig = some landmark_14_9 := by
  have h0 : steps tm_14_9 35 initConfig = some ({ st := some 6, left := [3, 3, 3], cur := 2, right := [3, 4, 1, 8] }) := rfl
  have hstep1 : steps tm_14_9 35 ({ st := some 6, left := [3, 3, 3], cur := 2, right := [3, 4, 1, 8] }) = some ({ st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 3, 8] }) := rfl
  have h1 : steps tm_14_9 70 initConfig = some ({ st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 3, 8] }) := steps_add tm_14_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_14_9 35 ({ st := some 1, left := [3, 3, 3, 3], cur := 2, right := [1, 1, 1, 3, 8] }) = some ({ st := some 5, left := [7, 7, 7, 7, 7, 7], cur := 7, right := [8, 8, 8, 8] }) := rfl
  have h2 : steps tm_14_9 105 initConfig = some ({ st := some 5, left := [7, 7, 7, 7, 7, 7], cur := 7, right := [8, 8, 8, 8] }) := steps_add tm_14_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_14_9 35 ({ st := some 5, left := [7, 7, 7, 7, 7, 7], cur := 7, right := [8, 8, 8, 8] }) = some ({ st := some 12, left := [], cur := 3, right := [7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }) := rfl
  have h3 : steps tm_14_9 140 initConfig = some ({ st := some 12, left := [], cur := 3, right := [7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }) := steps_add tm_14_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_14_9 25 ({ st := some 12, left := [], cur := 3, right := [7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }) := rfl
  have h4 : steps tm_14_9 165 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 2, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8] }) := steps_add tm_14_9 140 25 initConfig _ _ h3 hstep4
  exact h4

/-! ### BB(16,9) — > f_{ω^ω+7}(11) (`fwpw7_8` @ step 195) -/
def tm_16_9 : TM
  | 0, 0 => some ⟨4, Dir.L, some 6⟩
  | 0, 1 => some ⟨5, Dir.R, some 0⟩
  | 0, 2 => some ⟨3, Dir.L, some 12⟩
  | 0, 3 => some ⟨6, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.R, some 5⟩
  | 0, 5 => some ⟨7, Dir.R, some 2⟩
  | 0, 6 => some ⟨0, Dir.R, some 15⟩
  | 0, 7 => some ⟨7, Dir.R, some 0⟩
  | 0, 8 => some ⟨8, Dir.R, some 5⟩
  | 1, 0 => some ⟨7, Dir.R, some 0⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 7⟩
  | 1, 4 => some ⟨4, Dir.L, some 5⟩
  | 1, 5 => some ⟨0, Dir.L, some 2⟩
  | 1, 6 => some ⟨2, Dir.L, some 3⟩
  | 1, 7 => some ⟨7, Dir.L, some 1⟩
  | 1, 8 => some ⟨0, Dir.R, some 6⟩
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 2⟩
  | 2, 6 => some ⟨3, Dir.L, some 2⟩
  | 2, 7 => some ⟨1, Dir.L, some 1⟩
  | 2, 8 => some ⟨5, Dir.R, some 12⟩
  | 3, 0 => some ⟨7, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨4, Dir.L, some 3⟩
  | 3, 5 => some ⟨1, Dir.L, some 3⟩
  | 3, 6 => some ⟨3, Dir.L, some 3⟩
  | 3, 7 => some ⟨3, Dir.L, some 1⟩
  | 3, 8 => some ⟨8, Dir.R, some 1⟩
  | 4, 0 => some ⟨3, Dir.R, some 1⟩
  | 4, 1 => some ⟨7, Dir.R, some 4⟩
  | 4, 2 => some ⟨1, Dir.L, some 8⟩
  | 4, 3 => some ⟨4, Dir.R, some 5⟩
  | 4, 6 => some ⟨8, Dir.R, some 0⟩
  | 4, 7 => some ⟨7, Dir.R, some 4⟩
  | 4, 8 => some ⟨1, Dir.L, some 4⟩
  | 5, 0 => some ⟨1, Dir.L, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 5⟩
  | 5, 2 => some ⟨3, Dir.L, some 1⟩
  | 5, 3 => some ⟨6, Dir.R, some 5⟩
  | 5, 4 => some ⟨4, Dir.L, some 1⟩
  | 5, 5 => some ⟨1, Dir.L, some 5⟩
  | 5, 6 => some ⟨3, Dir.L, some 5⟩
  | 5, 7 => some ⟨3, Dir.L, some 4⟩
  | 5, 8 => some ⟨0, Dir.L, some 10⟩
  | 6, 0 => some ⟨3, Dir.R, some 1⟩
  | 6, 1 => some ⟨1, Dir.L, some 6⟩
  | 6, 2 => some ⟨1, Dir.L, some 6⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨5, Dir.L, some 0⟩
  | 6, 7 => some ⟨2, Dir.R, some 6⟩
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
  | 8, 7 => some ⟨2, Dir.R, some 11⟩
  | 9, 0 => some ⟨0, Dir.R, some 2⟩
  | 9, 2 => some ⟨2, Dir.L, some 9⟩
  | 9, 3 => some ⟨2, Dir.L, some 9⟩
  | 9, 7 => some ⟨7, Dir.L, some 9⟩
  | 9, 8 => some ⟨7, Dir.L, some 12⟩
  | 10, 0 => some ⟨3, Dir.R, some 10⟩
  | 10, 1 => some ⟨4, Dir.R, some 13⟩
  | 10, 2 => some ⟨5, Dir.L, some 10⟩
  | 10, 3 => some ⟨5, Dir.L, some 10⟩
  | 10, 5 => some ⟨2, Dir.R, some 7⟩
  | 10, 6 => some ⟨8, Dir.R, some 14⟩
  | 10, 7 => some ⟨6, Dir.L, some 4⟩
  | 11, 0 => some ⟨3, Dir.R, some 11⟩
  | 11, 1 => some ⟨0, Dir.L, some 12⟩
  | 11, 2 => some ⟨6, Dir.L, some 11⟩
  | 11, 3 => some ⟨6, Dir.L, some 11⟩
  | 11, 6 => some ⟨2, Dir.R, some 7⟩
  | 11, 7 => some ⟨3, Dir.L, some 3⟩
  | 12, 0 => some ⟨1, Dir.R, none⟩
  | 12, 1 => some ⟨3, Dir.R, some 0⟩
  | 12, 2 => some ⟨5, Dir.L, some 15⟩
  | 12, 3 => some ⟨1, Dir.R, some 10⟩
  | 12, 5 => some ⟨6, Dir.L, some 14⟩
  | 12, 6 => some ⟨7, Dir.L, some 13⟩
  | 12, 7 => some ⟨6, Dir.L, some 11⟩
  | 12, 8 => some ⟨5, Dir.R, some 14⟩
  | 13, 0 => some ⟨3, Dir.R, some 13⟩
  | 13, 1 => some ⟨6, Dir.R, some 1⟩
  | 13, 2 => some ⟨7, Dir.L, some 13⟩
  | 13, 3 => some ⟨7, Dir.L, some 13⟩
  | 13, 4 => some ⟨6, Dir.R, some 0⟩
  | 13, 5 => some ⟨8, Dir.L, some 13⟩
  | 13, 6 => some ⟨2, Dir.R, some 14⟩
  | 13, 7 => some ⟨2, Dir.R, some 7⟩
  | 13, 8 => some ⟨2, Dir.L, some 12⟩
  | 14, 0 => some ⟨3, Dir.R, some 13⟩
  | 14, 2 => some ⟨6, Dir.L, some 14⟩
  | 14, 3 => some ⟨6, Dir.L, some 14⟩
  | 14, 4 => some ⟨8, Dir.R, some 5⟩
  | 14, 5 => some ⟨2, Dir.R, some 15⟩
  | 14, 6 => some ⟨2, Dir.R, some 12⟩
  | 15, 0 => some ⟨3, Dir.R, some 14⟩
  | 15, 2 => some ⟨5, Dir.L, some 15⟩
  | 15, 3 => some ⟨5, Dir.L, some 15⟩
  | 15, 5 => some ⟨2, Dir.R, some 12⟩
  | 15, 6 => some ⟨0, Dir.R, some 8⟩
  | 15, 8 => some ⟨8, Dir.R, some 2⟩
  | _, _ => none

theorem valid_16_9 : ValidTM 16 9 tm_16_9 := by
  constructor
  · intro s sym hs hsym
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 3 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 1 => trivial | _ + 9 => omega
    | 4 => match sym with | 0 | 1 | 2 | 3 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 4 | 5 => trivial | _ + 9 => omega
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 7 => exact ⟨by decide, by decide⟩ | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 7 => match sym with | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 8 => trivial | _ + 9 => omega
    | 8 => match sym with | 0 | 1 | 2 | 3 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 6 | 8 => trivial | _ + 9 => omega
    | 9 => match sym with | 0 | 2 | 3 | 7 | 8 => exact ⟨by decide, by decide⟩ | 1 | 4 | 5 | 6 => trivial | _ + 9 => omega
    | 10 => match sym with | 0 | 1 | 2 | 3 | 5 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 | 8 => trivial | _ + 9 => omega
    | 11 => match sym with | 0 | 1 | 2 | 3 | 6 | 7 => exact ⟨by decide, by decide⟩ | 4 | 5 | 8 => trivial | _ + 9 => omega
    | 12 => match sym with | 1 | 2 | 3 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | 0 => exact ⟨by decide, trivial⟩ | 4 => trivial | _ + 9 => omega
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact ⟨by decide, by decide⟩ | _ + 9 => omega
    | 14 => match sym with | 0 | 2 | 3 | 4 | 5 | 6 => exact ⟨by decide, by decide⟩ | 1 | 7 | 8 => trivial | _ + 9 => omega
    | 15 => match sym with | 0 | 2 | 3 | 5 | 6 | 8 => exact ⟨by decide, by decide⟩ | 1 | 4 | 7 => trivial | _ + 9 => omega
    | _ + 16 => omega
  · intro s sym h
    match s with
    | 0 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 1 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 2 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 3 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 4 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 5 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 6 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 7 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 8 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 9 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 10 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 11 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 12 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 13 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 14 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | 15 => match sym with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega | _ + 9 => rfl
    | _ + 16 => rfl

def landmark_16_9 : Config := { st := some 8, left := [2, 3], cur := 1, right := [4, 7, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem reaches_landmark_16_9 : steps tm_16_9 195 initConfig = some landmark_16_9 := by
  have h0 : steps tm_16_9 35 initConfig = some ({ st := some 13, left := [3, 8, 3, 3, 2, 3], cur := 1, right := [] }) := rfl
  have hstep1 : steps tm_16_9 35 ({ st := some 13, left := [3, 8, 3, 3, 2, 3], cur := 1, right := [] }) = some ({ st := some 5, left := [8, 6, 7, 6, 7, 6, 5, 8, 3, 2, 3], cur := 5, right := [] }) := rfl
  have h1 : steps tm_16_9 70 initConfig = some ({ st := some 5, left := [8, 6, 7, 6, 7, 6, 5, 8, 3, 2, 3], cur := 5, right := [] }) := steps_add tm_16_9 35 35 initConfig _ _ h0 hstep1
  have hstep2 : steps tm_16_9 35 ({ st := some 5, left := [8, 6, 7, 6, 7, 6, 5, 8, 3, 2, 3], cur := 5, right := [] }) = some ({ st := some 2, left := [7, 3, 5, 5, 8, 3, 2, 3], cur := 5, right := [5, 7, 7, 3, 5] }) := rfl
  have h2 : steps tm_16_9 105 initConfig = some ({ st := some 2, left := [7, 3, 5, 5, 8, 3, 2, 3], cur := 5, right := [5, 7, 7, 3, 5] }) := steps_add tm_16_9 70 35 initConfig _ _ h1 hstep2
  have hstep3 : steps tm_16_9 35 ({ st := some 2, left := [7, 3, 5, 5, 8, 3, 2, 3], cur := 5, right := [5, 7, 7, 3, 5] }) = some ({ st := some 9, left := [3, 2, 3], cur := 8, right := [2, 2, 2, 2, 2, 2, 7, 7, 3, 5] }) := rfl
  have h3 : steps tm_16_9 140 initConfig = some ({ st := some 9, left := [3, 2, 3], cur := 8, right := [2, 2, 2, 2, 2, 2, 7, 7, 3, 5] }) := steps_add tm_16_9 105 35 initConfig _ _ h2 hstep3
  have hstep4 : steps tm_16_9 35 ({ st := some 9, left := [3, 2, 3], cur := 8, right := [2, 2, 2, 2, 2, 2, 7, 7, 3, 5] }) = some ({ st := some 9, left := [2, 2, 2, 2, 2, 3, 2, 7, 2, 3], cur := 2, right := [2, 2, 2] }) := rfl
  have h4 : steps tm_16_9 175 initConfig = some ({ st := some 9, left := [2, 2, 2, 2, 2, 3, 2, 7, 2, 3], cur := 2, right := [2, 2, 2] }) := steps_add tm_16_9 140 35 initConfig _ _ h3 hstep4
  have hstep5 : steps tm_16_9 20 ({ st := some 9, left := [2, 2, 2, 2, 2, 3, 2, 7, 2, 3], cur := 2, right := [2, 2, 2] }) = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 7, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := rfl
  have h5 : steps tm_16_9 195 initConfig = some ({ st := some 8, left := [2, 3], cur := 1, right := [4, 7, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) := steps_add tm_16_9 175 20 initConfig _ _ h4 hstep5
  exact h5

end BB.Champions2026_11_21.S9
