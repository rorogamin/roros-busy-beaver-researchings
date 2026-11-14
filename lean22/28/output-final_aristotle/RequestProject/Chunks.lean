import RequestProject.Overflow

/-!
# Chunks

The cells an overflow leaves behind come in chunks `M = 33`, `S = 32`,
`B = 22`; `ck W` reads them off the word (`spill_ck`).  `ckFold` is the
capacity scan of the rebuild over a chunk word.
-/

namespace BB25

/-- A chunk of a spill: the two cells one clause of `spill` appends. -/
inductive Ck where
  /-- `3 3`: the rebuild appends a marker and does not carry. -/
  | M : Ck
  /-- `3 2`: the rebuild appends a marker and carries. -/
  | S : Ck
  /-- `2 2`: the rebuild appends a block and carries. -/
  | B : Ck
deriving DecidableEq

/-- The two cells of a chunk. -/
def Ck.syms : Ck → List Sym
  | .M => [3, 3]
  | .S => [3, 2]
  | .B => [2, 2]

/-- Does the chunk make the rebuild carry?  Every chunk but `M` does. -/
def Ck.pays : Ck → Bool
  | .M => false
  | .S => true
  | .B => true

/-- What the chunk does to the balance of the rebuilt word: `M` and `S` append
a marker, `B` appends a block. -/
def Ck.wt : Ck → ℤ
  | .M => 1
  | .S => 1
  | .B => -1

/-- The cells of a list of chunks. -/
def csyms : List Ck → List Sym
  | [] => []
  | c :: cs => c.syms ++ csyms cs

@[simp] theorem csyms_nil : csyms [] = [] := rfl

@[simp] theorem csyms_cons (c : Ck) (cs : List Ck) : csyms (c :: cs) = c.syms ++ csyms cs := rfl

theorem csyms_append : ∀ (cs ds : List Ck), csyms (cs ++ ds) = csyms cs ++ csyms ds
  | [], ds => by simp
  | c :: cs, ds => by simp [csyms_append cs ds, List.append_assoc]

/-- **The chunks of `spill 0 W`**, read off the word. -/
def ck : List Tok → List Ck
  | [] => []
  | .F :: _ => []
  | .C :: w => ck w ++ [.M]
  | .P :: w =>
      match h : carry 0 w with
      | some w' => ck w' ++ [.S]
      | none => ck w ++ [.B]
  termination_by w => w.length
  decreasing_by
    · simp
    · rw [carry_length 0 w w' h]; simp
    · simp

@[simp] theorem ck_nil : ck [] = [] := by rw [ck]

@[simp] theorem ck_F (w : List Tok) : ck (.F :: w) = [] := by rw [ck]

@[simp] theorem ck_C (w : List Tok) : ck (.C :: w) = ck w ++ [.M] := by rw [ck]

theorem ck_P_some {w w' : List Tok} (h : carry 0 w = some w') :
    ck (.P :: w) = ck w' ++ [.S] := by
  rw [ck]; split <;> simp_all

theorem ck_P_none {w : List Tok} (h : carry 0 w = none) :
    ck (.P :: w) = ck w ++ [.B] := by
  rw [ck]; split <;> simp_all

/-- **A spill is the concatenation of its chunks.** -/
theorem spill_ck : ∀ (n : ℕ) (W : List Tok), W.length ≤ n → spill 0 W = csyms (ck W) := by
  intro n
  induction n with
  | zero =>
      intro W hW
      have : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hW)
      subst this; simp [mat]
  | succ n ih =>
      intro W hW
      match W with
      | [] => simp [mat]
      | .F :: w => rw [spill]; simp
      | .C :: w =>
          have hw : w.length ≤ n := by simpa using hW
          rw [spill_C_zero, ck_C, csyms_append, ih w hw]
          simp [Ck.syms]
      | .P :: w =>
          have hw : w.length ≤ n := by simpa using hW
          rw [spill_P_zero]
          match hcw : w with
          | [] => rw [ck_P_none (by simp), spill_nil]; simp [mat, Ck.syms]
          | x :: v =>
              match hc : carry 0 (x :: v) with
              | some w' =>
                  have hlen : w'.length ≤ n := by
                    rw [carry_length 0 (x :: v) w' hc]; exact hw
                  rw [spill_succ_some 0 (x :: v) w' (by simp) hc, ck_P_some hc,
                    csyms_append, ih w' hlen]
                  simp [Ck.syms]
              | none =>
                  rw [spill_succ_none 0 (x :: v) (by simp) hc, ck_P_none hc,
                    csyms_append, ih (x :: v) hw]
                  simp [Ck.syms]

/-- **One chunk of the capacity recursion.**  The chunk appends its token and
then carries, unless it is an `M`; the carry can only fail after a block. -/
def ckStep : Ck → ℕ → Option ℕ
  | .M, R => some (2 * R + 1)
  | .S, R => some (2 * R)
  | .B, R => if R / 2 = 0 then none else some (R / 2 - 1)

/-- **The capacity recursion over a chunk word.** -/
def ckFold : ℕ → List Ck → Option ℕ
  | R, [] => some R
  | R, c :: cs => match ckStep c R with
      | none => none
      | some R' => ckFold R' cs

@[simp] theorem ckFold_nil (R : ℕ) : ckFold R [] = some R := rfl

theorem ckFold_cons (R : ℕ) (c : Ck) (cs : List Ck) :
    ckFold R (c :: cs) = match ckStep c R with
      | none => none
      | some R' => ckFold R' cs := rfl

/-- The total rise of the chunk walk. -/
def ctot : List Ck → ℤ
  | [] => 0
  | c :: cs => c.wt + ctot cs

@[simp] theorem ctot_nil : ctot [] = 0 := rfl

@[simp] theorem ctot_cons (c : Ck) (cs : List Ck) : ctot (c :: cs) = c.wt + ctot cs := rfl

theorem ctot_append : ∀ (cs ds : List Ck), ctot (cs ++ ds) = ctot cs + ctot ds
  | [], ds => by simp
  | c :: cs, ds => by simp [ctot_append cs ds]; ring

end BB25
