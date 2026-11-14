import RequestProject.Machine

/-!
# The token machine

The used tape is read as `0^ω 1 2  W  s`: the left end `1 2`, a word `W` of
two-cell tokens

* `F = 0 2` (fresh marker), `C = 1 2` (charged marker), `P = 0 4` (block),

and a list `s` of loose cells to the right.  `estep` is one macro step on this
picture, with its exact cost in machine steps (`estep_sound`), and `Reaches`
is reachability *in the real machine* between token configurations.
-/

namespace BB25

/-- A token of the counter word. -/
inductive Tok where
  | F : Tok
  | C : Tok
  | P : Tok

/-- The two cells of a token, in reverse tape order. -/
def Tok.cellsRev : Tok → List Sym
  | .F => [2, 0]
  | .C => [2, 1]
  | .P => [4, 0]

/-- The cells of a token word given in reverse tape order (the head of the
list is the rightmost token), in reverse tape order. -/
def tcellsRev : List Tok → List Sym
  | [] => []
  | x :: xs => x.cellsRev ++ tcellsRev xs

/-- `L`: the head has just arrived, moving left, on the last cell of the word;
`R`: the head moves right, on the first cell of `s`. -/
inductive MDir where
  | L : MDir
  | R : MDir

/-- A token configuration: a direction, the token word in reverse tape order,
and the cells to the right of the word. -/
structure MCfg where
  dir : MDir
  w : List Tok
  s : List Sym

/-- The real configuration a token configuration denotes; the cells to the left
of the word are the left end `1 2` of the used tape. -/
def ecfg (c : MCfg) : Cfg :=
  match c.dir with
  | .L => ⟨(tcellsRev c.w ++ [2, 1]).tail, .A, (tcellsRev c.w ++ [2, 1]).headD 0 :: c.s⟩
  | .R => ⟨tcellsRev c.w ++ [2, 1], .A, c.s⟩

/-- **One step of the token machine**, with its cost in machine steps.  The
remaining `none` cases are the halting patterns (and cells `0`, `1` in `s`,
which never occur). -/
def estep : MCfg → Option (ℕ × MCfg)
  -- the head has arrived at the right end of the word and moves left
  | ⟨.L, .P :: x :: w, s⟩ => some (2, ⟨.L, x :: w, 2 :: 2 :: s⟩)
  | ⟨.L, [.P], s⟩ => some (2, ⟨.L, [], 2 :: 2 :: s⟩)
  | ⟨.L, .F :: w, s⟩ => some (3, ⟨.R, .C :: w, s⟩)
  | ⟨.L, .C :: .C :: x :: w, s⟩ => some (4, ⟨.L, x :: w, 3 :: 3 :: 3 :: 3 :: s⟩)
  | ⟨.L, [.C, .C], s⟩ => some (4, ⟨.L, [], 3 :: 3 :: 3 :: 3 :: s⟩)
  | ⟨.L, .C :: .P :: x :: w, s⟩ => some (4, ⟨.L, x :: w, 2 :: 2 :: 3 :: 3 :: s⟩)
  | ⟨.L, [.C, .P], s⟩ => some (4, ⟨.L, [], 2 :: 2 :: 3 :: 3 :: s⟩)
  | ⟨.L, .C :: .F :: w, s⟩ => some (5, ⟨.R, .C :: w, 3 :: 3 :: s⟩)
  | ⟨.L, [.C], s⟩ => some (6, ⟨.R, [], 3 :: 3 :: 3 :: s⟩)
  | ⟨.L, [], s⟩ => some (4, ⟨.R, [], 3 :: s⟩)
  -- the head moves right
  | ⟨.R, w, 3 :: 3 :: s⟩ => some (2, ⟨.R, .F :: w, s⟩)
  | ⟨.R, w, 3 :: 2 :: s⟩ => some (2, ⟨.R, .P :: w, s⟩)
  | ⟨.R, x :: w, 2 :: s⟩ => some (1, ⟨.L, x :: w, 3 :: s⟩)
  | ⟨.R, [], 2 :: s⟩ => some (1, ⟨.L, [], 3 :: s⟩)
  | ⟨.R, x :: w, []⟩ => some (3, ⟨.L, x :: w, [3, 2]⟩)
  | ⟨.R, [], []⟩ => some (3, ⟨.L, [], [3, 2]⟩)
  | ⟨.R, x :: w, [3]⟩ => some (9, ⟨.L, x :: w, [4, 2, 3, 2]⟩)
  | ⟨.R, [], [3]⟩ => some (9, ⟨.L, [], [4, 2, 3, 2]⟩)
  | ⟨.R, .F :: w, 4 :: s⟩ => some (5, ⟨.L, w, 2 :: 2 :: 3 :: s⟩)
  | ⟨.R, .C :: w, 4 :: s⟩ => some (5, ⟨.L, w, 4 :: 2 :: 3 :: s⟩)
  | _ => none

/-- **Exactness of one token step.** -/
theorem estep_sound (c : MCfg) (t : ℕ) (c' : MCfg) (h : estep c = some (t, c')) :
    steps t (ecfg c) = some (ecfg c') := by
  unfold estep at h
  split at h
  all_goals cases h
  all_goals rfl

/-- Every token step costs at least one machine step. -/
theorem estep_cost_pos {c : MCfg} {t : ℕ} {c' : MCfg} (h : estep c = some (t, c')) : 0 < t := by
  unfold estep at h
  split at h
  all_goals cases h
  all_goals norm_num

/-! ## Reachability in the real machine -/

/-- The real machine gets from one token configuration to another. -/
def Reaches (c c' : MCfg) : Prop := ∃ t, steps t (ecfg c) = some (ecfg c')

/-- The real machine gets from one token configuration to another in a positive
number of steps. -/
def RunPos (c c' : MCfg) : Prop := ∃ t, 0 < t ∧ steps t (ecfg c) = some (ecfg c')

theorem Reaches.refl (c : MCfg) : Reaches c c := ⟨0, rfl⟩

theorem Reaches.trans {a b c : MCfg} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c :=
  let ⟨t₁, h1⟩ := h₁
  let ⟨t₂, h2⟩ := h₂
  ⟨t₁ + t₂, steps_trans h1 h2⟩

theorem Reaches.step {c c' : MCfg} {t : ℕ} (h : estep c = some (t, c')) : Reaches c c' :=
  ⟨t, estep_sound c t c' h⟩

theorem RunPos.step {c c' : MCfg} {t : ℕ} (h : estep c = some (t, c')) : RunPos c c' :=
  ⟨t, estep_cost_pos h, estep_sound c t c' h⟩

theorem RunPos.trans_reaches {a b c : MCfg} (h₁ : RunPos a b) (h₂ : Reaches b c) : RunPos a c :=
  let ⟨t₁, hp, h1⟩ := h₁
  let ⟨t₂, h2⟩ := h₂
  ⟨t₁ + t₂, by omega, steps_trans h1 h2⟩

theorem Reaches.trans_pos {a b c : MCfg} (h₁ : Reaches a b) (h₂ : RunPos b c) : RunPos a c :=
  let ⟨t₁, h1⟩ := h₁
  let ⟨t₂, hp, h2⟩ := h₂
  ⟨t₁ + t₂, by omega, steps_trans h1 h2⟩

end BB25
