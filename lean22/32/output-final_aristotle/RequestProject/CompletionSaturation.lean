import RequestProject.CompletionArithmetic

/-!
# Completion of the non-halting proof — semantic bridge

The central new invariant is `sat_preserved`: the saturation labels of a counter
are unchanged by a successful increment.  Hence the word released by a normal
phase is an explicit function of the counter (`normal_exact`), and the junction
has an equally explicit effect (`junction_exact`).

The argument formalised here was supplied with the task as an uncompiled
candidate (see `nonhalting_completion/NONHALTING_PROOF.md`); the proofs below
have been repaired where needed and are machine-checked.
-/

namespace SOC.Completion

theorem mod_three_cases (h : Nat) : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega

@[simp] theorem beta_succ_alpha (h : Nat) : beta (h + 1) = alpha h := by
  rcases mod_three_cases h with h3 | h3 | h3
  · have e : (h + 1) % 3 = 1 := by omega
    simp [beta, alpha, h3, e]
  · have e : (h + 1) % 3 = 2 := by omega
    simp [beta, alpha, h3, e]
  · have e : (h + 1) % 3 = 0 := by omega
    simp [beta, alpha, h3, e]

@[simp] theorem alpha_add_two_beta (h : Nat) : alpha (h + 2) = beta h := by
  rcases mod_three_cases h with h3 | h3 | h3
  · have e : (h + 2) % 3 = 2 := by omega
    simp [beta, alpha, h3, e]
  · have e : (h + 2) % 3 = 0 := by omega
    simp [beta, alpha, h3, e]
  · have e : (h + 2) % 3 = 1 := by omega
    simp [beta, alpha, h3, e]

@[simp] theorem is4_beta (h : Nat) : is4 (beta h) = false := by
  rcases mod_three_cases h with h3 | h3 | h3 <;> simp [beta, is4, h3]

@[simp] theorem is4_alpha (h : Nat) : is4 (alpha h) = false := by
  rcases mod_three_cases h with h3 | h3 | h3 <;> simp [alpha, is4, h3]

/-- Tape-order block labels after completely spending this counter. -/
def sat : List LD → List Sym
  | [] => []
  | .d0 :: w => sat w ++ [4]
  | .d1 :: w => sat w ++ [4]
  | .dB :: w => sat w ++ [beta (gap w)]
  | .dA :: w => sat w ++ [alpha (gap w)]

@[simp] theorem sat_length (w : List LD) : (sat w).length = w.length := by
  induction w with
  | nil => rfl
  | cons d w ih => cases d <;> simp [sat, ih]

theorem sat_pattern (w : List LD) : (sat w).map is4 = (w.map rad2).reverse := by
  induction w with
  | nil => rfl
  | cons d w ih => cases d <;> simp [sat, ih, rad2]

/-- Saturation erases the timing of all successful increments. -/
theorem sat_preserved {w w' : List LD} (h : Inc w w') : sat w' = sat w := by
  induction h with
  | d0 w => rfl
  | @d1 w w' hi ih => simp only [sat, ih]
  | @dB w w' hi ih =>
      simp only [sat, ih]
      rw [hi.gap_eq, beta_succ_alpha]
  | @dA w w' w'' h1 h2 ih1 ih2 =>
      have hg : gap w = gap w'' + 2 := by
        have e1 := h1.gap_eq
        have e2 := h2.gap_eq
        omega
      simp only [sat, ih2, ih1, hg, alpha_add_two_beta]

theorem addT_four_facts {w w' : List LD} (h : addT w 4 = some w') :
    sat w' = sat w ∧ gap w' + 4 = gap w := by
  obtain ⟨u1, u2, u3, e1, e2, e3, e4⟩ := addT_four h
  have s1 := sat_preserved e1
  have s2 := sat_preserved e2
  have s3 := sat_preserved e3
  have s4 := sat_preserved e4
  have g1 := e1.gap_eq
  have g2 := e2.gap_eq
  have g3 := e3.gap_eq
  have g4 := e4.gap_eq
  exact ⟨by rw [s4, s3, s2, s1], by omega⟩

/-- At zero gap, the executable overflow emits exactly the saturation labels. -/
theorem ovf_sat : ∀ {w : List LD}, gap w = 0 → ∀ acc : List Sym,
    ovfF w acc = some (sat w ++ acc)
  | [], _, acc => by simp [ovfF, sat]
  | .d0 :: w, hz, acc => by simp at hz
  | .d1 :: w, hz, acc => by
      have hw : gap w = 0 := by simp only [gap_d1] at hz; omega
      rw [ovfF, ovf_sat hw]
      simp [sat, List.append_assoc]
  | .dB :: w, hz, acc => by
      have hw : gap w = 0 := by simp only [gap_dB] at hz; omega
      rw [ovfF, ovf_sat hw]
      simp [sat, hw, beta, List.append_assoc]
  | .dA :: w, hz, acc => by
      have hwle : gap w ≤ 1 := by simp only [gap_dA] at hz; omega
      rw [ovfF]
      cases hone : addT w 1 with
      | none =>
          have hw : gap w = 0 := gap_eq_zero_of_addT_none hone
          show ovfF w (2 :: acc) = some (sat (LD.dA :: w) ++ acc)
          rw [ovf_sat hw]
          simp [sat, hw, alpha, List.append_assoc]
      | some w' =>
          have hi : Inc w w' := addT_one_inc hone
          have hg := hi.gap_eq
          have hw' : gap w' = 0 := by omega
          have hw : gap w = 1 := by omega
          have hlen : w'.length = w.length := addT_length hone
          show ovfF w' (1 :: acc) = some (sat (LD.dA :: w) ++ acc)
          rw [ovf_sat hw', sat_preserved hi]
          simp [sat, hw, alpha, List.append_assoc]
  termination_by w => w.length
  decreasing_by all_goals simp_all [List.length_cons]

/-- The normal phase has an exact, scalar fresh suffix. -/
theorem normal_exact (w : List LD) (acc : List Sym) :
    normalF w acc = some (sat w ++ fresh (gap w) ++ acc) := by
  rw [normalF]
  cases hone : addT w 1 with
  | none =>
      have hz : gap w = 0 := gap_eq_zero_of_addT_none hone
      show ovfF w acc = some (sat w ++ fresh (gap w) ++ acc)
      simpa [hz] using ovf_sat hz acc
  | some w' =>
      have hi : Inc w w' := addT_one_inc hone
      have hlt : gap (.dB :: w') < gap w := gap_normal_cycle_lt hi hi.gap_pos
      have hgap := hi.gap_eq
      have hd : gap (.dB :: w') = descend (gap w) := by
        simp only [gap_dB, descend]
        omega
      have hb : beta (gap w') = freshDigit (gap w) := by
        rw [hgap, freshDigit_succ]
      show normalF (LD.dB :: w') acc = some (sat w ++ fresh (gap w) ++ acc)
      rw [normal_exact (.dB :: w') acc]
      simp only [sat, sat_preserved hi, hd, hb]
      rw [fresh_pos hi.gap_pos]
      simp [List.append_assoc]
termination_by gap w
decreasing_by exact hlt

/-- Exact gap and saturation labels at the junction. -/
theorem junction_exact {w wj : List LD} (h : junctionF w = some wj) :
    gap wj = junctionGap (gap w) ∧
      sat wj = sat w.tail ++ [junctionFirst (gap w), alpha (junctionTop (gap w))] := by
  match w with
  | [] => simp at h
  | .dA :: v => simp at h
  | .dB :: v => simp at h
  | .d0 :: v =>
      rw [junctionF] at h
      cases hfour : addT v 4 with
      | none => rw [hfour] at h; simp at h
      | some v' =>
          rw [hfour] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst wj
          obtain ⟨hs, hg⟩ := addT_four_facts hfour
          have ht : gap (.dB :: v') = junctionTop (gap (.d0 :: v)) := by
            simp only [gap_dB, gap_d0, junctionTop]
            omega
          have hb : beta (gap v') = junctionFirst (gap (.d0 :: v)) := by
            have hgv : gap (LD.d0 :: v) = 2 * gap v' + 9 := by
              simp only [gap_d0]; omega
            rw [hgv]
            rcases mod_three_cases (gap v') with h3 | h3 | h3
            · have e : (2 * gap v' + 9) % 3 = 0 := by omega
              simp [beta, junctionFirst, h3, e]
            · have e : (2 * gap v' + 9) % 3 = 2 := by omega
              simp [beta, junctionFirst, h3, e]
            · have e : (2 * gap v' + 9) % 3 = 1 := by omega
              simp [beta, junctionFirst, h3, e]
          refine ⟨?_, ?_⟩
          · change (2 * gap (.dB :: v')) / 3 = junctionGap (gap (.d0 :: v))
            rw [ht]
            rfl
          · simp only [sat, List.tail_cons, hs, ht, hb]
            simp [List.append_assoc]
  | .d1 :: v =>
      rw [junctionF] at h
      cases hfour : addT v 4 with
      | none => rw [hfour] at h; simp at h
      | some v' =>
          rw [hfour] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst wj
          obtain ⟨hs, hg⟩ := addT_four_facts hfour
          have ht : gap (.dA :: v') = junctionTop (gap (.d1 :: v)) := by
            simp only [gap_dA, gap_d1, junctionTop]
            omega
          have hb : alpha (gap v') = junctionFirst (gap (.d1 :: v)) := by
            have hgv : gap (LD.d1 :: v) = 2 * gap v' + 8 := by
              simp only [gap_d1]; omega
            rw [hgv]
            rcases mod_three_cases (gap v') with h3 | h3 | h3
            · have e : (2 * gap v' + 8) % 3 = 2 := by omega
              simp [alpha, junctionFirst, h3, e]
            · have e : (2 * gap v' + 8) % 3 = 1 := by omega
              simp [alpha, junctionFirst, h3, e]
            · have e : (2 * gap v' + 8) % 3 = 0 := by omega
              simp [alpha, junctionFirst, h3, e]
          refine ⟨?_, ?_⟩
          · change (2 * gap (.dA :: v')) / 3 = junctionGap (gap (.d1 :: v))
            rw [ht]
            rfl
          · simp only [sat, List.tail_cons, hs, ht, hb]
            simp [List.append_assoc]

/-- Exact replacement for the old, conditional fresh-material estimate. -/
theorem revolution_suffix {L L' : List Sym} {w : List LD}
    (hreset : resetF [.d0] L = some w) (hrev : revolutionF L = some L') :
    ∃ S : List Sym,
      L' = S ++ suffix (gap w) ∧ S.map is4 = L.map notOne := by
  have hw : w.map rad2 = true :: (L.map notOne).reverse := by
    rw [resetF_pat hreset, show ([LD.d0] : List LD).map rad2 = true :: [] from rfl,
      patF_true]
    simp
  have hwtail : w.tail.map rad2 = (L.map notOne).reverse := by
    have ht := congrArg List.tail hw
    simpa using ht
  have hshape : (sat w.tail).map is4 = L.map notOne := by
    rw [sat_pattern, hwtail, List.reverse_reverse]
  rw [revolutionF, hreset, Option.bind_some] at hrev
  cases hj : junctionF w with
  | none => rw [hj] at hrev; simp at hrev
  | some wj =>
      rw [hj, Option.bind_some, normal_exact] at hrev
      simp only [List.append_nil, Option.some.injEq] at hrev
      obtain ⟨hg, hs⟩ := junction_exact hj
      refine ⟨sat w.tail, ?_, hshape⟩
      rw [← hrev, hs, hg]
      simp [suffix, List.append_assoc]

end SOC.Completion
