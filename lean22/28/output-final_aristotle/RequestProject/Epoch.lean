import RequestProject.Price

/-!
# The two-epoch argument: the exact overflow-to-overflow law

This file connects the chunk map `epochMap` of `RequestProject/Price.lean`
with the machine.  The key new ingredient is the *decoration* `decor` of a
token word: the pattern of blocks, refined by the parity bit that the capacity
discards at each block.  Carries preserve it (`carry_decor`), and at capacity
zero it is exactly the chunk word of the overflow (`ck_eq_decor`).

The main result is `epoch_step`: if the machine is at a normal overflow
configuration `⟨L, X, [3,2]⟩` (with `cap X = 0`) and the capacity scan of
`ck X` succeeds with value at least `3`, then after a positive number of real
machine steps it is at the next normal overflow configuration `⟨L, X', [3,2]⟩`,
with `cap X' = 0` and `ck X' = epochMap (ck X)`.
-/

namespace BB25


/-! ## The decoration -/

/-- **The decoration of a token word**, in tape order (deepest token first):
a marker gives `M`; a block gives `S` or `B` according to the parity of the
capacity of the word below it. -/
def decor : List Tok → List Ck
  | [] => []
  | .F :: w => decor w ++ [.M]
  | .C :: w => decor w ++ [.M]
  | .P :: w => decor w ++ [if cap w % 2 = 1 then .S else .B]

@[simp] theorem decor_nil : decor [] = [] := rfl
@[simp] theorem decor_F (w : List Tok) : decor (.F :: w) = decor w ++ [.M] := rfl
@[simp] theorem decor_C (w : List Tok) : decor (.C :: w) = decor w ++ [.M] := rfl
@[simp] theorem decor_P (w : List Tok) :
    decor (.P :: w) = decor w ++ [if cap w % 2 = 1 then .S else .B] := rfl

/-- **Lemma 2.1: a successful carry preserves the decoration.** -/
theorem carry_decor : ∀ (d : ℕ) (w w' : List Tok), carry d w = some w' → decor w' = decor w := by
  intro d w
  induction w generalizing d with
  | nil => simp
  | cons x w ih =>
      intro w' h
      match x, d with
      | .P, d =>
          simp only [carry_P, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          have hge : ¬ cap w < 2 ^ (d + 1) := by
            intro hlt
            rw [← cap_carry_iff] at hlt
            rw [hlt] at hv
            exact Option.some_ne_none v hv.symm
          have hcap : cap v = cap w - 2 ^ (d + 1) := cap_carry w (d + 1) v hv
          have hpar : cap v % 2 = cap w % 2 := by
            rw [hcap, pow_succ]
            rw [pow_succ] at hge
            omega
          simp [ih (d + 1) v hv, hpar]
      | .C, d + 1 =>
          simp only [carry_C_succ, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih d v hv]
      | .F, d + 1 =>
          simp only [carry_F_succ, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih d v hv]
      | .C, 0 =>
          simp only [carry_C_zero, Option.map_eq_some_iff] at h
          obtain ⟨v, hv, rfl⟩ := h
          simp [ih 0 v hv]
      | .F, 0 =>
          rw [carry_F_zero, Option.some.injEq] at h
          subst h
          simp

/-- **Lemma 2.2: at capacity zero the decoration is the chunk word.** -/
theorem ck_eq_decor : ∀ (n : ℕ) (W : List Tok), W.length ≤ n → cap W = 0 → ck W = decor W := by
  intro n
  induction n with
  | zero =>
      intro W hW _
      have : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hW)
      subst this; simp
  | succ n ih =>
      intro W hW hcap
      match W with
      | [] => simp
      | .F :: w => simp [cap_F] at hcap
      | .C :: w =>
          have hw : w.length ≤ n := by simpa using hW
          have : cap w = 0 := by rw [cap_C] at hcap; omega
          simp [ih w hw this]
      | .P :: w =>
          have hw : w.length ≤ n := by simpa using hW
          have hcw : cap w ≤ 1 := cap_P_tail hcap
          match hc : carry 0 w with
          | some w' =>
              have hlen : w'.length = w.length := carry_length 0 w w' hc
              have h1 : cap w' = cap w - 2 ^ 0 := cap_carry w 0 w' hc
              have hpos : ¬ (cap w < 2 ^ 0) := by
                intro hlt
                rw [← cap_carry_iff] at hlt
                rw [hlt] at hc
                exact Option.some_ne_none w' hc.symm
              have h1' : cap w = 1 := by simp at hpos; omega
              have : cap w' = 0 := by simp at h1; omega
              rw [ck_P_some hc, ih w' (by omega) this, carry_decor 0 w w' hc, decor_P, h1']
              rfl
          | none =>
              have hcw0 : cap w = 0 := by
                have := (cap_carry_iff w 0).1 hc
                simpa using this
              rw [ck_P_none hc, ih w hw hcw0, decor_P, hcw0]
              rfl

theorem bitsLSB_succ (N t : ℕ) : bitsLSB N (t + 1) = bitsLSB N t ++ [bitCk N t] := by
  simp [bitsLSB, List.range_succ]

/-- The decoration of the blocks the passes stack on top of a word: the binary
digits of the capacity below them, least significant first. -/
theorem decor_replicate_P : ∀ (t : ℕ) (V : List Tok),
    decor (List.replicate t .P ++ V) = decor V ++ bitsLSB (cap V) t
  | 0, V => by simp [bitsLSB]
  | t + 1, V => by
      rw [List.replicate_succ, List.cons_append, decor_P, decor_replicate_P t V,
        cap_replicate_P, bitsLSB_succ, List.append_assoc]
      rfl

/-! ## The rebuild tracks the decoration -/

/-- A carry at the start of a pair is the same as a `3` there, on the carried
word. -/
theorem rebG_two {w w' : List Tok} (h : carry 0 w = some w') (x : Sym) (s : List Sym)
    (hx : x = 2 ∨ x = 3) : rebG w (2 :: x :: s) = rebG w' (3 :: x :: s) := by
  rcases hx with rfl | rfl
  · rw [rebG, rebG]; simp only [h]
  · rw [rebG, rebG]; simp only [h]

theorem csyms_head (cs : List Ck) : ∃ x s, csyms cs ++ [3, 2] = x :: s ∧ (x = 2 ∨ x = 3) := by
  cases cs with
  | nil => exact ⟨3, [2], rfl, Or.inr rfl⟩
  | cons c cs =>
      cases c
      · exact ⟨3, 3 :: (csyms cs ++ [3, 2]), by simp [Ck.syms], Or.inr rfl⟩
      · exact ⟨3, 2 :: (csyms cs ++ [3, 2]), by simp [Ck.syms], Or.inr rfl⟩
      · exact ⟨2, 2 :: (csyms cs ++ [3, 2]), by simp [Ck.syms], Or.inl rfl⟩

/-- **Lemma 3.1: the rebuilt core has decoration `A(c)`.**  Over the cells of a
chunk word whose scan succeeds with value `v`, the rebuild creates the tail in
front of a word `C :: U` with `cap U = v`, and the decoration of `U` is that of
the starting word followed by the emission of the scan. -/
theorem rebG_decor : ∀ (cs : List Ck) (w : List Tok) (R v : ℕ), cap w = R →
    ckFold R cs = some v →
    ∃ U, rebG w ((3 : Sym) :: (csyms cs ++ [3, 2])) = .tail (.C :: U) ∧ cap U = v ∧
      decor U = decor w ++ emitW R cs := by
  intro cs
  induction cs with
  | nil =>
      intro w R v hR hv
      simp only [ckFold_nil, Option.some.injEq] at hv
      subst hv
      refine ⟨w, ?_, hR, by simp [emitW]⟩
      rw [csyms_nil, List.nil_append]
      rw [rebG, rebG]
      simp
  | cons c cs ih =>
      intro w R v hR hv
      rw [ckFold_cons] at hv
      cases c with
      | M =>
          simp only [ckStep] at hv
          have hc : csyms (.M :: cs) ++ [3, 2] = (3 : Sym) :: 3 :: (csyms cs ++ [3, 2]) := by
            simp [Ck.syms]
          obtain ⟨U, h1, h2, h3⟩ := ih (.F :: w) (2 * R + 1) v (by simp [hR]) hv
          refine ⟨U, ?_, h2, ?_⟩
          · rw [hc, rebG]; exact h1
          · rw [h3]; simp [emitW, emitLabel, stepT]
      | S =>
          simp only [ckStep] at hv
          have hc : csyms (.S :: cs) ++ [3, 2] = (3 : Sym) :: 2 :: (csyms cs ++ [3, 2]) := by
            simp [Ck.syms]
          obtain ⟨U, h1, h2, h3⟩ := ih (.C :: w) (2 * R) v (by simp [hR]) hv
          refine ⟨U, ?_, h2, ?_⟩
          · rw [hc, rebG]
            obtain ⟨x, s, hs, hx⟩ := csyms_head cs
            rw [hs] at h1 ⊢
            rw [rebG_two (carry_F_zero w) x s hx]
            exact h1
          · rw [h3]; simp [emitW, emitLabel, stepT]
      | B =>
          by_cases hne : R / 2 = 0
          · simp [ckStep, hne] at hv
          · simp only [ckStep, hne, ↓reduceIte] at hv
            have hc : csyms (.B :: cs) ++ [3, 2] = (2 : Sym) :: 2 :: (csyms cs ++ [3, 2]) := by
              simp [Ck.syms]
            have hcapP : cap (.P :: w) = R / 2 := by simp [hR]
            have hnn : carry 0 (.P :: w) ≠ none := by
              intro hn
              rw [cap_carry_iff, hcapP] at hn
              simp at hn; omega
            obtain ⟨w'', hw''⟩ := Option.ne_none_iff_exists'.1 hnn
            have hcap'' : cap w'' = R / 2 - 1 := by
              rw [cap_carry _ 0 w'' hw'', hcapP]; simp
            obtain ⟨U, h1, h2, h3⟩ := ih w'' (R / 2 - 1) v hcap'' hv
            refine ⟨U, ?_, h2, ?_⟩
            · rw [hc, rebG]
              obtain ⟨x, s, hs, hx⟩ := csyms_head cs
              rw [hs] at h1 ⊢
              rw [rebG_two hw'' x s hx]
              exact h1
            · rw [h3, carry_decor 0 _ _ hw'', decor_P, hR]
              simp [emitW, emitLabel, stepT]

/-! ## The passes -/

/-- **The ordinary passes.**  Starting with `j` blocks on top of `V`, the passes
each subtract `2^j` from the capacity of the core and stack one more block,
until the core can no longer pay: the machine arrives at `P^(j+m) ++ V'` with
`cap V' < 2^(j+m)`, `cap V' + 2^(j+m) = cap V + 2^j`, and the decoration of the
core unchanged. -/
theorem passes : ∀ (n j : ℕ) (V : List Tok), cap V ≤ n →
    ∃ m V', Reaches ⟨.L, List.replicate j .P ++ V, [3, 2]⟩ ⟨.L, List.replicate (j + m) .P ++ V', [3, 2]⟩ ∧
      cap V' < 2 ^ (j + m) ∧ cap V' + 2 ^ (j + m) = cap V + 2 ^ j ∧ decor V' = decor V := by
  intro n
  induction n with
  | zero =>
      intro j V hV
      refine ⟨0, V, Reaches.refl _, ?_, rfl, rfl⟩
      have : 0 < 2 ^ j := pow_pos (by norm_num) j
      simp; omega
  | succ n ih =>
      intro j V hV
      by_cases hlt : cap V < 2 ^ j
      · exact ⟨0, V, Reaches.refl _, by simpa using hlt, rfl, rfl⟩
      · have hnn : carry j V ≠ none := fun h => hlt ((cap_carry_iff V j).1 h)
        obtain ⟨V1, hV1⟩ := Option.ne_none_iff_exists'.1 hnn
        have hcap1 : cap V1 = cap V - 2 ^ j := cap_carry V j V1 hV1
        have hpos : 0 < 2 ^ j := pow_pos (by norm_num) j
        have hcarry : carry 0 (List.replicate j .P ++ V) = some (List.replicate j .P ++ V1) := by
          rw [carry_replicate_P j V, hV1]; rfl
        have hpass := cascade_pass_tok _ _ hcarry
        obtain ⟨m, V', hrun, h1, h2, h3⟩ := ih (j + 1) V1 (by omega)
        refine ⟨m + 1, V', ?_, ?_, ?_, ?_⟩
        · refine hpass.trans ?_
          have e1 : Tok.P :: (List.replicate j Tok.P ++ V1) = List.replicate (j + 1) .P ++ V1 := by
            rw [List.replicate_succ]; rfl
          have e2 : j + (m + 1) = j + 1 + m := by omega
          show Reaches ⟨.L, Tok.P :: (List.replicate j Tok.P ++ V1), [3, 2]⟩ _
          rw [e1, e2]; exact hrun
        · rw [show j + (m + 1) = j + 1 + m by omega]; exact h1
        · rw [show j + (m + 1) = j + 1 + m by omega, h2, hcap1, pow_succ]; omega
        · rw [h3, carry_decor j V V1 hV1]

/-! ## The epoch law -/

/-- **The exact overflow-to-overflow law (Lemma 3.2 / Corollary 3.3).**  From a
normal overflow configuration whose chunk scan succeeds with value at least
`3`, the machine reaches, in a positive number of steps, the next normal
overflow configuration, and its chunk word is `epochMap` of the old one. -/
theorem epoch_step (X : List Tok) (hX : cap X = 0) (v : ℕ) (hv : ckFold 0 (ck X) = some v)
    (h3 : 3 ≤ v) :
    ∃ X', cap X' = 0 ∧ ck X' = epochMap (ck X) ∧ RunPos ⟨.L, X, [3, 2]⟩ ⟨.L, X', [3, 2]⟩ := by
  have hc : carry 0 X = none := (cap_carry_iff X 0).2 (by simp [hX])
  have h1 := overflow_rebuild_cap X hc
  rw [spill_ck X.length X (le_refl _)] at h1
  obtain ⟨U, hU, hcapU, hdecU⟩ := rebG_decor (ck X) [] 0 v rfl hv
  rw [hU] at h1
  -- the tail creation
  have h2 : estep (gCfg (.tail (.C :: U))) = some (9, ⟨.L, .C :: U, [4, 2, 3, 2]⟩) := rfl
  -- the tail-eating pass
  have hnn1 : carry 0 U ≠ none := by
    intro hn; rw [cap_carry_iff, hcapU] at hn; simp at hn; omega
  obtain ⟨U1, hU1⟩ := Option.ne_none_iff_exists'.1 hnn1
  have hcap1 : cap U1 = v - 1 := by rw [cap_carry U 0 U1 hU1, hcapU]; simp
  have h3' := tail_pass U U1 hU1
  -- the carry through the initial `2 2`
  have hnn2 : carry 1 U1 ≠ none := by
    intro hn; rw [cap_carry_iff, hcap1] at hn; simp at hn; omega
  obtain ⟨U2, hU2⟩ := Option.ne_none_iff_exists'.1 hnn2
  have hcap2 : cap U2 = v - 3 := by rw [cap_carry U1 1 U2 hU2, hcap1]; simp; omega
  have h4 := crossCarry U1.length 1 U1 U2 (le_refl _) hU2 [3, 2, 3, 2]
  have h5 : estep ⟨.R, .P :: U2, [3, 2, 3, 2]⟩ = some (2, ⟨.R, .P :: .P :: U2, [3, 2]⟩) := rfl
  have h6 : estep ⟨.R, .P :: .P :: U2, [3, 2]⟩ = some (2, ⟨.R, .P :: .P :: .P :: U2, []⟩) := rfl
  have h7 : estep ⟨.R, .P :: .P :: .P :: U2, []⟩ = some (3, ⟨.L, .P :: .P :: .P :: U2, [3, 2]⟩) :=
    rfl
  -- the ordinary passes
  obtain ⟨m, V', hrun, hlt, hsum, hdec⟩ := passes (cap U2) 3 U2 (le_refl _)
  have hlog : Nat.log 2 (v + 5) = 3 + m := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]; omega
  have hcapV' : cap V' = v + 5 - 2 ^ (3 + m) := by omega
  refine ⟨List.replicate (3 + m) .P ++ V', ?_, ?_, ?_⟩
  · rw [cap_replicate_P]; exact Nat.div_eq_of_lt hlt
  · rw [ck_eq_decor _ _ (le_refl _) (by rw [cap_replicate_P]; exact Nat.div_eq_of_lt hlt),
      decor_replicate_P, hdec, carry_decor 1 U1 U2 hU2, carry_decor 0 U U1 hU1, hdecU, epochMap, ckFold_foldT _ _ _ hv, hlog, hcapV']
    simp
  · refine h1.trans_pos ?_
    refine (RunPos.step h2).trans_reaches ?_
    refine h3'.trans ?_
    refine (show Reaches ⟨.L, U1, [2, 2, 3, 2, 3, 2]⟩ ⟨.R, .P :: U2, [3, 2, 3, 2]⟩ by
      simpa using h4).trans ?_
    refine (Reaches.step h5).trans ?_
    refine (Reaches.step h6).trans ?_
    refine (Reaches.step h7).trans ?_
    exact hrun

end BB25
