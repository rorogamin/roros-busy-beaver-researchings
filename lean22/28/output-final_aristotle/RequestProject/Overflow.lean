import RequestProject.Carry

/-!
# Overflow, rebuild and the tail

* `spill d W` / `spillLaw`: when a carry runs off the left end of the word,
  the head eats the whole word, is reflected at the left end, and leaves the
  cells `3 (spill d W)` behind it.
* `rebG` / `rebG_reaches`: the right-moving head then re-parses those cells two
  at a time into a new word, carrying at every pair that begins with a `2`.
* `tail_pass`: after the tail `4 2 3 2` has been created in front of a word
  `C :: X`, the next pass eats it.
-/

namespace BB25

/-- **The overflow law in closed form.**  `spill d W` is the word of cells the
head leaves behind when the carry entering `W` with `d` blocks' worth of
material runs off the left end of `W`. -/
def spill : ℕ → List Tok → List Sym
  | d, [] => mat d
  | 0, .F :: _ => []
  | 0, .C :: w => spill 0 w ++ [3, 3]
  | 0, .P :: w => spill 1 w
  | d + 1, x :: w =>
      match h : carry d (x :: w) with
      | none => spill d (x :: w) ++ [2, 2]
      | some W₁ => spill d W₁ ++ [3, 2]
  termination_by d w => (w.length, d)
  decreasing_by
    · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
    · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
    · exact Prod.Lex.right _ (Nat.lt_succ_self d)
    · rw [carry_length d (x :: w) W₁ h]
      exact Prod.Lex.right _ (Nat.lt_succ_self d)

@[simp] theorem spill_nil (d : ℕ) : spill d [] = mat d := by
  rw [spill]

@[simp] theorem spill_C_zero (w : List Tok) : spill 0 (.C :: w) = spill 0 w ++ [3, 3] := by
  rw [spill]

@[simp] theorem spill_P_zero (w : List Tok) : spill 0 (.P :: w) = spill 1 w := by
  rw [spill]

theorem spill_succ_none (d : ℕ) (W : List Tok) (hW : W ≠ []) (h : carry d W = none) :
    spill (d + 1) W = spill d W ++ [2, 2] := by
  obtain ⟨x, w, rfl⟩ : ∃ x w, W = x :: w := by
    cases W with
    | nil => exact absurd rfl hW
    | cons x w => exact ⟨x, w, rfl⟩
  rw [spill]
  split <;> simp_all

theorem spill_succ_some (d : ℕ) (W W₁ : List Tok) (hW : W ≠ []) (h : carry d W = some W₁) :
    spill (d + 1) W = spill d W₁ ++ [3, 2] := by
  obtain ⟨x, w, rfl⟩ : ∃ x w, W = x :: w := by
    cases W with
    | nil => exact absurd rfl hW
    | cons x w => exact ⟨x, w, rfl⟩
  rw [spill]
  split <;> simp_all

/-- **The overflow law.**  If the carry entering the word `W` with `d` blocks'
worth of material runs off the left end of `W`, then the head eats the whole
word, arrives at the left end of the used tape and is reflected there; what it
has written is exactly `spill d W`, and the reflection adds the extra `3`. -/
theorem spillLaw : ∀ (n d : ℕ) (W : List Tok), W.length ≤ n → carry d W = none →
    ∀ r : List Sym, Reaches ⟨.L, W, mat d ++ r⟩ ⟨.R, [], 3 :: (spill d W ++ r)⟩ := by
  have hnil : ∀ (d : ℕ) (r : List Sym),
      Reaches ⟨.L, [], mat d ++ r⟩ ⟨.R, [], 3 :: (spill d [] ++ r)⟩ := by
    intro d r
    simpa using Reaches.step (c := ⟨.L, [], mat d ++ r⟩) rfl
  intro n
  induction n with
  | zero =>
      intro d W hW _ r
      have : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hW)
      subst this
      exact hnil d r
  | succ n ih =>
      intro d
      induction d with
      | zero =>
          intro W hW hc r
          match W with
          | [] => exact hnil 0 r
          | .F :: w => simp at hc
          | .P :: w =>
              have h1 : Reaches ⟨.L, (.P :: w : List Tok), mat 0 ++ r⟩ ⟨.L, w, 2 :: 2 :: r⟩ := by
                match w with
                | [] => simpa using Reaches.step (c := ⟨.L, [(.P : Tok)], r⟩) rfl
                | x :: v => simpa using Reaches.step (c := ⟨.L, (.P :: x :: v : List Tok), r⟩) rfl
              have hcw : carry 1 w = none := by
                simp only [carry_P, Option.map_eq_none_iff] at hc
                exact hc
              have h2 := ih 1 w (by simp at hW ⊢; omega) hcw r
              rw [show mat 1 ++ r = 2 :: 2 :: r by simp [mat]] at h2
              simpa using h1.trans h2
          | .C :: w =>
              have hcw : carry 0 w = none := by
                simp only [carry_C_zero, Option.map_eq_none_iff] at hc
                exact hc
              match w with
              | [] => simpa using Reaches.step (c := ⟨.L, [(.C : Tok)], r⟩) rfl
              | .F :: y => simp at hcw
              | .C :: v =>
                  have h1 : Reaches ⟨.L, (.C :: .C :: v : List Tok), mat 0 ++ r⟩
                      ⟨.L, v, 3 :: 3 :: 3 :: 3 :: r⟩ := by
                    match v with
                    | [] => simpa using Reaches.step (c := ⟨.L, [(.C : Tok), .C], r⟩) rfl
                    | x :: v' =>
                        simpa using
                          Reaches.step (c := ⟨.L, (.C :: .C :: x :: v' : List Tok), r⟩) rfl
                  have hcv : carry 0 v = none := by
                    simp only [carry_C_zero, Option.map_eq_none_iff] at hcw
                    exact hcw
                  have h2 := ih 0 v (by simp at hW ⊢; omega) hcv (3 :: 3 :: 3 :: 3 :: r)
                  simp only [mat_zero, List.nil_append] at h2
                  simpa using h1.trans h2
              | .P :: v =>
                  have h1 : Reaches ⟨.L, (.C :: .P :: v : List Tok), mat 0 ++ r⟩
                      ⟨.L, v, 2 :: 2 :: 3 :: 3 :: r⟩ := by
                    match v with
                    | [] => simpa using Reaches.step (c := ⟨.L, [(.C : Tok), .P], r⟩) rfl
                    | x :: v' =>
                        simpa using
                          Reaches.step (c := ⟨.L, (.C :: .P :: x :: v' : List Tok), r⟩) rfl
                  have hcv : carry 1 v = none := by
                    simp only [carry_P, Option.map_eq_none_iff] at hcw
                    exact hcw
                  have h2 := ih 1 v (by simp at hW ⊢; omega) hcv (3 :: 3 :: r)
                  rw [show mat 1 ++ (3 :: 3 :: r) = 2 :: 2 :: 3 :: 3 :: r by simp [mat]] at h2
                  simpa using h1.trans h2
      | succ e ihd =>
          intro W hW hc r
          match hWe : W with
          | [] => exact hnil (e + 1) r
          | x :: w =>
            have hWne : (x :: w : List Tok) ≠ [] := by simp
            rw [carry_double] at hc
            cases hce : carry e (x :: w) with
            | none =>
                have h1 := ihd (x :: w) hW hce (2 :: 2 :: r)
                rw [← mat_succ] at h1
                rw [spill_succ_none e (x :: w) hWne hce]
                simpa using h1
            | some W₁ =>
                have hc₁ : carry e W₁ = none := by
                  rw [hce] at hc
                  simpa using hc
                have hW₁ : W₁ ≠ [] := carry_ne_nil hce
                have hlen₁ : W₁.length ≤ n + 1 := by
                  rw [carry_length e (x :: w) W₁ hce]; exact hW
                -- the first half of the doubling succeeds
                have h1 : Reaches ⟨.L, (x :: w : List Tok), mat (e + 1) ++ r⟩
                    ⟨.R, blocks e ++ W₁, 2 :: 2 :: r⟩ := by
                  have := crossCarry (x :: w).length e (x :: w) W₁ (le_refl _) hce (2 :: 2 :: r)
                  rw [← mat_succ] at this
                  exact this
                -- the head turns around on the first `2`
                obtain ⟨y, v, hyv⟩ : ∃ y v, blocks e ++ W₁ = y :: v := by
                  cases hbw : blocks e ++ W₁ with
                  | nil => exact absurd hbw (by simp [hW₁])
                  | cons y v => exact ⟨y, v, rfl⟩
                have h2 : Reaches ⟨.R, blocks e ++ W₁, 2 :: 2 :: r⟩
                    ⟨.L, blocks e ++ W₁, 3 :: 2 :: r⟩ := by
                  rw [hyv]
                  exact Reaches.step (c := ⟨.R, y :: v, 2 :: 2 :: r⟩) rfl
                -- and dissolves the blocks it has just made
                have h3 : Reaches ⟨.L, blocks e ++ W₁, 3 :: 2 :: r⟩ ⟨.L, W₁, mat e ++ 3 :: 2 :: r⟩ :=
                  (pop_blocks e W₁ hW₁ (3 :: 2 :: r))
                -- the second half fails
                have h4 := ihd W₁ hlen₁ hc₁ (3 :: 2 :: r)
                rw [spill_succ_some e (x :: w) W₁ hWne hce]
                simpa using ((h1.trans h2).trans h3).trans h4

/-- **The overflow law at a pass boundary.**  If the carry of a pass over the
word `X` runs off the left end, the head arrives at the left end of the used
tape, is reflected there, and starts re-reading the cells `3 (spill 0 X) 3 2`
it has left behind. -/
theorem overflow_pass (X : List Tok) (h : carry 0 X = none) :
    Reaches ⟨.L, X, [3, 2]⟩ ⟨.R, [], 3 :: (spill 0 X ++ [3, 2])⟩ := by
  simpa using spillLaw X.length 0 X (le_refl _) h [3, 2]

/-! ## The rebuild -/

/-- How a rebuild ends: tail creation, back at a pass boundary, a new
overflow, or a cell that never occurs. -/
inductive GEnd where
  | tail : List Tok → GEnd
  | boundary : List Tok → GEnd
  | ovf : List Tok → List Sym → GEnd
  | stuck : List Tok → List Sym → GEnd

/-- The configuration a rebuild ends in. -/
def gCfg : GEnd → MCfg
  | .tail w => ⟨.R, w, [3]⟩
  | .boundary w => ⟨.R, w, []⟩
  | .ovf w t => ⟨.L, w, 3 :: t⟩
  | .stuck w s => ⟨.R, w, s⟩

/-- **The rebuild.**  The head, moving right over the cells `s`, re-parses them
two at a time onto the word `w`, performing one carry whenever a pair begins
with a `2`; a carry which runs off the left end of the word stops it. -/
def rebG : List Tok → List Sym → GEnd
  | w, [] => .boundary w
  | w, [3] => .tail w
  | w, [2] =>
      match carry 0 w with
      | some w' => .tail w'
      | none => .ovf w []
  | w, 3 :: 3 :: s => rebG (.F :: w) s
  | w, 3 :: 2 :: s => rebG (.P :: w) s
  | w, 2 :: 3 :: s =>
      match carry 0 w with
      | some w' => rebG (.F :: w') s
      | none => .ovf w (3 :: s)
  | w, 2 :: 2 :: s =>
      match carry 0 w with
      | some w' => rebG (.P :: w') s
      | none => .ovf w (2 :: s)
  | w, s => .stuck w s
  termination_by _ s => s.length

/-- The head turns around on a `2`. -/
theorem gTurn (w : List Tok) (t : List Sym) :
    Reaches ⟨.R, w, 2 :: t⟩ ⟨.L, w, 3 :: t⟩ := by
  cases w with
  | nil => exact Reaches.step (c := ⟨.R, ([] : List Tok), 2 :: t⟩) rfl
  | cons a b => exact Reaches.step (c := ⟨.R, a :: b, 2 :: t⟩) rfl

/-- One carry of the rebuild, as a run of the machine. -/
theorem gCarry {w w' : List Tok} (h : carry 0 w = some w') (t : List Sym) :
    Reaches ⟨.R, w, 2 :: t⟩ ⟨.R, w', 3 :: t⟩ := by
  refine (gTurn w t).trans (?_)
  have := crossCarry w.length 0 w w' (le_refl _) h (3 :: t)
  simpa using this

/-- **The rebuild is exact**: the machine really does get from
the head's arrival at the cells to the configuration `rebG` names. -/
theorem rebG_reaches : ∀ (n : ℕ) (w : List Tok) (s : List Sym), s.length ≤ n →
    Reaches ⟨.R, w, s⟩ (gCfg (rebG w s)) := by
  intro n
  induction n with
  | zero =>
      intro w s hs
      have : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hs)
      subst this
      rw [rebG, gCfg]
      exact Reaches.refl _
  | succ n ih =>
      intro w s hs
      match s with
      | [] => rw [rebG, gCfg]; exact Reaches.refl _
      | [3] => rw [rebG, gCfg]; exact Reaches.refl _
      | [2] =>
          rw [rebG]
          cases hcv : carry 0 w with
          | none => exact gTurn w []
          | some w' => exact gCarry hcv []
      | 3 :: 3 :: s' =>
          have hs' : s'.length ≤ n := by simp only [List.length_cons] at hs; omega
          have h1 : Reaches ⟨.R, w, (3 : Sym) :: 3 :: s'⟩ ⟨.R, Tok.F :: w, s'⟩ :=
            Reaches.step (c := ⟨.R, w, (3 : Sym) :: 3 :: s'⟩) rfl
          rw [rebG]
          exact h1.trans (ih (Tok.F :: w) s' hs')
      | 3 :: 2 :: s' =>
          have hs' : s'.length ≤ n := by simp only [List.length_cons] at hs; omega
          have h1 : Reaches ⟨.R, w, (3 : Sym) :: 2 :: s'⟩ ⟨.R, Tok.P :: w, s'⟩ :=
            Reaches.step (c := ⟨.R, w, (3 : Sym) :: 2 :: s'⟩) rfl
          rw [rebG]
          exact h1.trans (ih (Tok.P :: w) s' hs')
      | 2 :: 3 :: s' =>
          have hs' : s'.length ≤ n := by simp only [List.length_cons] at hs; omega
          rw [rebG]
          cases hcv : carry 0 w with
          | none => exact gTurn w (3 :: s')
          | some w' =>
              have h1 := gCarry hcv (3 :: s')
              have h2 : Reaches ⟨.R, w', (3 : Sym) :: 3 :: s'⟩ ⟨.R, Tok.F :: w', s'⟩ :=
                Reaches.step (c := ⟨.R, w', (3 : Sym) :: 3 :: s'⟩) rfl
              exact (h1.trans h2).trans (ih (Tok.F :: w') s' hs')
      | 2 :: 2 :: s' =>
          have hs' : s'.length ≤ n := by simp only [List.length_cons] at hs; omega
          rw [rebG]
          cases hcv : carry 0 w with
          | none => exact gTurn w (2 :: s')
          | some w' =>
              have h1 := gCarry hcv (2 :: s')
              have h2 : Reaches ⟨.R, w', (3 : Sym) :: 2 :: s'⟩ ⟨.R, Tok.P :: w', s'⟩ :=
                Reaches.step (c := ⟨.R, w', (3 : Sym) :: 2 :: s'⟩) rfl
              exact (h1.trans h2).trans (ih (Tok.P :: w') s' hs')
      | 0 :: s' =>
          have h : rebG w (0 :: s') = .stuck w (0 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 1 :: s' =>
          have h : rebG w (1 :: s') = .stuck w (1 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 4 :: s' =>
          have h : rebG w (4 :: s') = .stuck w (4 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 3 :: 0 :: s' =>
          have h : rebG w (3 :: 0 :: s') = .stuck w (3 :: 0 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 3 :: 1 :: s' =>
          have h : rebG w (3 :: 1 :: s') = .stuck w (3 :: 1 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 3 :: 4 :: s' =>
          have h : rebG w (3 :: 4 :: s') = .stuck w (3 :: 4 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 2 :: 0 :: s' =>
          have h : rebG w (2 :: 0 :: s') = .stuck w (2 :: 0 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 2 :: 1 :: s' =>
          have h : rebG w (2 :: 1 :: s') = .stuck w (2 :: 1 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _
      | 2 :: 4 :: s' =>
          have h : rebG w (2 :: 4 :: s') = .stuck w (2 :: 4 :: s') := by rw [rebG] <;> simp
          rw [h]; exact Reaches.refl _

/-- **The rebuild after an overflow.**  The head is reflected at the left end
and re-parses the cells `3 (spill 0 X) 3 2` from nothing. -/
theorem overflow_rebuild_cap (X : List Tok) (hc : carry 0 X = none) :
    Reaches ⟨.L, X, [3, 2]⟩ (gCfg (rebG [] (3 :: (spill 0 X ++ [3, 2])))) := by
  refine (overflow_pass X hc).trans ?_
  exact rebG_reaches (3 :: (spill 0 X ++ [3, 2])).length [] _ (le_refl _)

/-! ## The tail-eating pass -/

/-- **The tail-eating pass.**  A tail has just been created in front of a word
ending (in tape order) with a charged marker.  If the carry of the next pass
does not overflow, the head comes back over a word starting with a fresh
marker, and that marker eats the `4`. -/
theorem tail_pass (X v : List Tok) (h : carry 0 X = some v) :
    Reaches ⟨.L, .C :: X, [4, 2, 3, 2]⟩ ⟨.L, v, [2, 2, 3, 2, 3, 2]⟩ := by
  have hc : carry 0 (.C :: X) = some (.F :: v) := by simp [h]
  have h1 : Reaches ⟨.L, (.C :: X : List Tok), ([4, 2, 3, 2] : List Sym)⟩
      ⟨.R, (.F :: v : List Tok), ([4, 2, 3, 2] : List Sym)⟩ := by
    have := crossCarry (.C :: X).length 0 (.C :: X) (.F :: v) (le_refl _) hc [4, 2, 3, 2]
    simpa using this
  exact h1.trans (Reaches.step (c := ⟨.R, (.F :: v : List Tok), ([4, 2, 3, 2] : List Sym)⟩) rfl)

end BB25
