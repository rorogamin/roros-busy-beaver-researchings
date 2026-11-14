/-
# Lemma A: every generated word is a safe local reset

Putting the three previous files together:

* `Classify.lean` sorts a generated word into the leading-run criterion or one
  of the four exceptional shapes;
* `Credit.lean` settles the criterion;
* `Families.lean` settles the four shapes by hand.

The two conclusions are

* `gen_scan_stops`: the reverse two-decrement scan of a generated word stops
  inside the word, over any nonnegative base counter — so the paid stack of the
  reset is ready without help from the stack below it;
* `gen_rrun_pos`: the value of a generated word is positive, with the single
  exception of the unextended base word `w0 2 = Y X Y Y V` over an exhausted
  counter, which is the exceptional branch of the argument.
-/
import RequestProject.BB25.Prefix.RB.Families

namespace BB25.Prefix

open BB25

variable {a : ℤ} {Q : ℕ → Prop}

/-! ## Splitting off the leading run -/

theorem lead_split : ∀ (w : List RB), w = List.replicate (lead w) .Y ++ w.drop (lead w) := by
  intro w
  induction w with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | Y =>
          show RB.Y :: t = List.replicate (lead t + 1) RB.Y ++ List.drop (lead t + 1) (RB.Y :: t)
          rw [List.replicate_succ, List.cons_append, List.drop_succ_cons]
          exact congrArg _ ih
      | _ => rfl

theorem Digs.drop {w : List RB} (hw : Digs w) (n : ℕ) : Digs (w.drop n) :=
  fun b hb => hw b (List.drop_subset _ _ hb)

theorem eight_le_two_pow {i : ℕ} (h : 3 ≤ i) : (8 : ℤ) ≤ 2 ^ i := by
  have hp := two_pow_le_int (i := 3) (j := i) h
  norm_num at hp
  exact hp

theorem one_le_two_pow {i : ℕ} : (1 : ℤ) ≤ 2 ^ i := by
  have hp := two_pow_le_int (i := 0) (j := i) (Nat.zero_le i)
  norm_num at hp
  exact hp

/-! ## The scan of a generated word -/

/-- A word that satisfies the leading-run criterion stops its own scan. -/
theorem scan_of_criterion {w : List RB} (hw : Digs w) (ha : 0 ≤ a)
    (hcrit : nxw w + 2 ≤ lead w) : Scan w 0 a Q := by
  obtain ⟨s, hds, hnx, hsp⟩ :
      ∃ s, Digs s ∧ nxw s = nxw w ∧ w = List.replicate (lead w) .Y ++ s := by
    refine ⟨w.drop (lead w), hw.drop _, ?_, lead_split w⟩
    conv_rhs => rw [lead_split w]
    rw [nxw_Yrun_append]
  rw [hsp]
  exact (scan_leading_run hds ha (by omega)).of_stops

/-- **Lemma A, first half.**  The reverse two-decrement scan of a generated
word always stops inside the word. -/
theorem gen_scan_stops {w : List RB} {h : ℕ} (hg : Gen w h) (ha : 0 ≤ a) :
    Scan w 0 a Q := by
  rcases gen_lead_or_exc hg with hcrit | hexc
  · exact scan_of_criterion hg.digs ha hcrit
  · rcases hexc with ⟨k, -, rfl⟩ | ⟨j, k, -, rfl⟩ | ⟨k, rfl⟩ | ⟨j, k, rfl⟩
    · exact scan_fam12 k
    · exact scan_fam34 j k ha
    · exact scan_fam5 k ha
    · exact scan_fam6 j k ha

/-! ## The value of a generated word -/

/-- The credit estimate in the form used for positivity. -/
theorem rrun_pos_of_credit {pre p : List RB} (hp : Digs p)
    (h : 3 * 2 ^ (nxw p) ≤ rrun pre a + 2) : 1 ≤ rrun (pre ++ p) a := by
  have hcond : (2 : ℤ) ^ (nxw p + 1) ≤ rrun pre a + 2 := by
    have : (2 : ℤ) ^ (nxw p + 1) = 2 * 2 ^ (nxw p) := by ring
    have hpos : (0 : ℤ) < 2 ^ (nxw p) := by positivity
    linarith
  have hcr := rrun_credit p hp (rrun pre a) hcond
  have hdiv : (3 : ℤ) ≤ (rrun pre a + 2) / 2 ^ (nxw p) := by
    rw [Int.le_ediv_iff_mul_le (by positivity)]
    linarith
  rw [rrun_append]
  linarith

theorem digs_Xrun_V (c : ℕ) : Digs (List.replicate c .X ++ [.V]) :=
  (digs_Xrun c).append (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)

/-- **Lemma A, second half.**  A generated word has positive value over any
nonnegative counter, except for the unextended `w0 2` over an exhausted
counter. -/
theorem gen_rrun_pos {w : List RB} {h : ℕ} (hg : Gen w h) (ha : 0 ≤ a)
    (hexc : w ≠ w0 2 ∨ 1 ≤ a) : 1 ≤ rrun w a := by
  have ha1 : (1 : ℤ) ≤ a + 1 := by omega
  rcases gen_lead_or_exc hg with hcrit | hexcw
  · obtain ⟨s, hds, hnx, hsp⟩ :
        ∃ s, Digs s ∧ nxw s = nxw w ∧ w = List.replicate (lead w) .Y ++ s := by
      refine ⟨w.drop (lead w), hg.digs.drop _, ?_, lead_split w⟩
      conv_rhs => rw [lead_split w]
      rw [nxw_Yrun_append]
    rw [hsp]
    have := rrun_pos_leading_run hds ha (show nxw s + 2 ≤ lead w by omega)
    omega
  · rcases hexcw with ⟨k, -, rfl⟩ | ⟨j, k, -, rfl⟩ | ⟨k, rfl⟩ | ⟨j, k, rfl⟩
    · -- the unextended `w0 2` with `k` extra one bits in front
      rw [rrun_YcX]
      have hk : 1 ≤ k ∨ 1 ≤ a := by
        rcases hexc with hne | h1
        · refine Or.inl ?_
          by_contra hc
          exact hne (by rw [show k = 0 by omega]; rfl)
        · exact Or.inr h1
      have h8 : (8 : ℤ) ≤ 2 ^ 3 := by norm_num
      rcases hk with hk | hk
      · have h16 : (2 : ℤ) ^ 4 ≤ 2 ^ (k + 3) := two_pow_le_int (by omega)
        have hm : (2 : ℤ) ^ (k + 3) ≤ 2 ^ (k + 3) * (a + 1) :=
          le_mul_of_one_le_right (by positivity) ha1
        norm_num at h16
        linarith
      · have hm : (2 : ℤ) ^ (k + 3) * 2 ≤ 2 ^ (k + 3) * (a + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        have h8' : (8 : ℤ) ≤ 2 ^ (k + 3) := eight_le_two_pow (by omega)
        linarith
    · -- one marker step on it
      rw [show List.replicate (j + k + 2) RB.Y ++ (cX ++ List.replicate (k + 1) RB.X ++ [RB.V])
        = (List.replicate ((j + k + 1) + 1) RB.Y ++ cX)
            ++ (List.replicate (k + 1) RB.X ++ [RB.V]) by
          rw [show (j + k + 1) + 1 = j + k + 2 from rfl]; simp]
      refine rrun_pos_of_credit (digs_Xrun_V (k + 1)) ?_
      rw [show nxw (List.replicate (k + 1) RB.X ++ [RB.V]) = k + 1 by
        rw [nxw_append, nxw_Xrun]; rfl, rrun_YcX, show j + k + 1 + 3 = j + k + 4 by omega]
      have hm : (2 : ℤ) ^ (j + k + 4) ≤ 2 ^ (j + k + 4) * (a + 1) :=
        le_mul_of_one_le_right (by positivity) ha1
      have h1 : (2 : ℤ) ^ (k + 4) ≤ 2 ^ (j + k + 4) := two_pow_le_int (by omega)
      have h2 : (3 : ℤ) * 2 ^ (k + 1) = 6 * 2 ^ k := by ring
      have h3 : (2 : ℤ) ^ (k + 4) = 16 * 2 ^ k := by ring
      have h4 : (1 : ℤ) ≤ 2 ^ k := one_le_two_pow
      linarith
    · -- one marker step on the unextended `w0 3`
      rw [show List.replicate (k + 3) RB.Y ++ (cV ++ List.replicate (k + 2) RB.X ++ [RB.V])
        = (List.replicate ((k + 2) + 1) RB.Y ++ cV)
            ++ (List.replicate (k + 2) RB.X ++ [RB.V]) by
          rw [show (k + 2) + 1 = k + 3 from rfl]; simp]
      refine rrun_pos_of_credit (digs_Xrun_V (k + 2)) ?_
      rw [show nxw (List.replicate (k + 2) RB.X ++ [RB.V]) = k + 2 by
        rw [nxw_append, nxw_Xrun]; rfl, rrun_YcV, show k + 2 + 5 = k + 7 by omega]
      have hm : (2 : ℤ) ^ (k + 7) ≤ 2 ^ (k + 7) * (a + 1) :=
        le_mul_of_one_le_right (by positivity) ha1
      have h3 : (2 : ℤ) ^ (k + 7) = 32 * 2 ^ (k + 2) := by ring
      have h4 : (1 : ℤ) ≤ 2 ^ (k + 2) := one_le_two_pow
      linarith
    · -- two marker steps on the unextended `w0 2`
      rw [show List.replicate (j + k + 3) RB.Y ++ (cX ++ List.replicate (k + 1) RB.X ++ [RB.V]
            ++ List.replicate j RB.X ++ [RB.V])
        = (List.replicate ((j + k + 2) + 1) RB.Y ++ cX)
            ++ (List.replicate (k + 1) RB.X ++ [RB.V] ++ List.replicate j RB.X ++ [RB.V]) by
          rw [show (j + k + 2) + 1 = j + k + 3 from rfl]; simp]
      refine rrun_pos_of_credit
        (((digs_Xrun_V (k + 1)).append (digs_Xrun j)).append
          (Digs.cons (Or.inr (Or.inl rfl)) Digs.nil)) ?_
      rw [show nxw (List.replicate (k + 1) RB.X ++ [RB.V] ++ List.replicate j RB.X ++ [RB.V])
          = k + 1 + j by
        rw [nxw_append, nxw_append, nxw_append, nxw_Xrun, nxw_Xrun]; rfl,
        rrun_YcX, show j + k + 2 + 3 = j + k + 5 by omega]
      have hm : (2 : ℤ) ^ (j + k + 5) ≤ 2 ^ (j + k + 5) * (a + 1) :=
        le_mul_of_one_le_right (by positivity) ha1
      have h2 : (3 : ℤ) * 2 ^ (k + 1 + j) = 6 * 2 ^ (j + k) := by ring
      have h3 : (2 : ℤ) ^ (j + k + 5) = 32 * 2 ^ (j + k) := by ring
      have h4 : (1 : ℤ) ≤ 2 ^ (j + k) := one_le_two_pow
      linarith

end BB25.Prefix
