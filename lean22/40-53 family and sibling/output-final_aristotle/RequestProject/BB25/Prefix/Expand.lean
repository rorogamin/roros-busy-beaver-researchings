/-
# Height-sensitive bounds for the reset transducer

`Word.lean` proves that a matched group multiplies the second counter by four.
For the remaining members of the family that is not enough: one needs to know
how the bound grows with the *height* of the Dyck prefix, and one needs to
distinguish the closing letters whose transduced image doubles the second
counter (`V`, and `X` read at an odd first counter) from those that halve it.

`qcnt w a` counts the **expanding closes** of `w`, read from the first counter
`a`.  With `h = bal w` the height of the Dyck prefix, the three bounds are

```
              2 ^ h * (c + 1)      - 1 ≤ trun w a c
  1 ≤ q  →    2 ^ h * (4 c + 3)    - 1 ≤ trun w a c
  2 ≤ q  →    2 ^ h * (16 c + 11)  - 1 ≤ trun w a c
```

The constants `1, 3, 11` are `(2 * 4 ^ q + 1) / 3`, and they are sharp: the
words `Y`, `YYVX` and `YYVXYX` attain them.

The last result of the file is the arithmetic shape of a word with at most one
expanding close: its value is never divisible by four at height at least two.
-/
import RequestProject.BB25.Prefix.Word

namespace BB25.Prefix

open BB25

/-! ## Expanding closes -/

/-- Whether the digit `b`, read at the first counter `a`, is an *expanding*
close: its transduced letter doubles the second counter. -/
def qstep (b : RB) (a : ℤ) : ℕ :=
  match b with
  | .V => 1
  | .X => if a % 2 = 1 then 1 else 0
  | _ => 0

@[simp] theorem qstep_Y (a : ℤ) : qstep .Y a = 0 := rfl
@[simp] theorem qstep_V (a : ℤ) : qstep .V a = 1 := rfl
theorem qstep_X (a : ℤ) : qstep .X a = if a % 2 = 1 then 1 else 0 := rfl

/-- The number of expanding closes of a word, read from the first counter. -/
def qcnt : List RB → ℤ → ℕ
  | [], _ => 0
  | b :: w, a => qstep b a + qcnt w (rstep b a)

@[simp] theorem qcnt_nil (a : ℤ) : qcnt [] a = 0 := rfl
@[simp] theorem qcnt_cons (b : RB) (w : List RB) (a : ℤ) :
    qcnt (b :: w) a = qstep b a + qcnt w (rstep b a) := rfl

theorem qcnt_append (w v : List RB) (a : ℤ) :
    qcnt (w ++ v) a = qcnt w a + qcnt v (rrun w a) := by
  induction w generalizing a with
  | nil => simp
  | cons b w ih => simp [ih, Nat.add_assoc]

/-! ## The first close of a Dyck prefix is expanding -/

/-- A word of digits with a close splits at its first close. -/
theorem digs_split_first_close : ∀ (w : List RB), Digs w → HasCl w →
    ∃ (k : ℕ) (cl : RB) (rest : List RB),
      (cl = RB.V ∨ cl = RB.X) ∧ w = List.replicate k RB.Y ++ cl :: rest := by
  intro w
  induction w with
  | nil => intro _ h; obtain ⟨b, hb, _⟩ := h; simp at hb
  | cons b w ih =>
      intro hdigs hcl
      obtain ⟨hb, hw⟩ := hdigs.of_cons
      rcases hb with rfl | rfl | rfl
      · -- an opening letter: the first close is inside `w`
        have hcl' : HasCl w := by
          obtain ⟨x, hx, hxc⟩ := hcl
          rcases List.mem_cons.mp hx with rfl | hx'
          · rcases hxc with h | h <;> simp at h
          · exact ⟨x, hx', hxc⟩
        obtain ⟨k, cl, rest, hcl0, rfl⟩ := ih hw hcl'
        exact ⟨k + 1, cl, rest, hcl0, by rw [List.replicate_succ, List.cons_append]⟩
      · exact ⟨0, RB.V, w, Or.inl rfl, by simp⟩
      · exact ⟨0, RB.X, w, Or.inr rfl, by simp⟩

/-- **The first close of a Dyck prefix is expanding**: it is preceded by at
least one opening letter and by no other close, so the first counter is odd. -/
theorem qcnt_pos_of_hasCl {w : List RB} (hw : Digs w) (hd : DyckPre w) (h : HasCl w) (a : ℤ) :
    1 ≤ qcnt w a := by
  obtain ⟨k, cl, rest, hcl, rfl⟩ := digs_split_first_close w hw h
  -- the run of opening letters is nonempty
  have hk : 1 ≤ k := by
    by_contra hc
    obtain rfl : k = 0 := by omega
    have := hd [cl] (by simp)
    rcases hcl with rfl | rfl <;> simp [bal] at this
  -- the first counter at the close is odd
  have hval : rrun (List.replicate k RB.Y) a = 2 ^ k * (a + 1) - 1 := rrun_replicate_Y k a
  have hdvd : (2 : ℤ) ∣ 2 ^ k * (a + 1) :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hodd : (rrun (List.replicate k RB.Y) a) % 2 = 1 := by
    rw [hval]; omega
  rw [qcnt_append, qcnt_cons]
  have : qstep cl (rrun (List.replicate k RB.Y) a) = 1 := by
    rcases hcl with rfl | rfl
    · rfl
    · rw [qstep_X, if_pos hodd]
  omega

/-! ## The three bounds -/

/-- The two elementary facts about the scale `2 ^ h` used throughout. -/
private theorem two_pow_facts (h : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    (1 : ℤ) ≤ 2 ^ h ∧ (2 : ℤ) ^ h ≤ 2 ^ h * (c + 1) := by
  have h1 : (0 : ℤ) < 2 ^ h := by positivity
  refine ⟨by omega, ?_⟩
  nlinarith

private theorem trun_pow_bounds : ∀ (n : ℕ) (w : List RB), w.length ≤ n → Digs w → DyckPre w →
    ∀ (h : ℕ), bal w = (h : ℤ) → ∀ a c : ℤ, 0 ≤ c →
      (2 ^ h * (c + 1) - 1 ≤ trun w a c) ∧
      (1 ≤ qcnt w a → 4 * (2 ^ h * (c + 1)) - 2 ^ h - 1 ≤ trun w a c) ∧
      (2 ≤ qcnt w a → 16 * (2 ^ h * (c + 1)) - 5 * 2 ^ h - 1 ≤ trun w a c) := by
  intro n
  induction n with
  | zero =>
      intro w hlen _ _ h hbal a c hc
      obtain rfl : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simp only [bal_nil] at hbal
      obtain rfl : h = 0 := by exact_mod_cast hbal.symm
      simp only [trun_nil, pow_zero, one_mul, qcnt_nil]
      exact ⟨by omega, fun hq => by omega, fun hq => by omega⟩
  | succ n ih =>
      intro w hlen hdigs hd h hbal a c hc
      rcases List.eq_nil_or_concat w with rfl | ⟨p, b, hcat⟩
      · simp only [bal_nil] at hbal
        obtain rfl : h = 0 := by exact_mod_cast hbal.symm
        simp only [trun_nil, pow_zero, one_mul, qcnt_nil]
        exact ⟨by omega, fun hq => by omega, fun hq => by omega⟩
      rw [List.concat_eq_append] at hcat
      subst hcat
      have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
      have hdigsp : Digs p := (hdigs.of_append).1
      have hlenp : p.length ≤ n := by
        have : (p ++ [b]).length = p.length + 1 := by simp
        omega
      have hbb : Dig b := (hdigs.of_append).2 b (by simp)
      have hbalsum : bal (p ++ [b]) = bal p + bal [b] := bal_append p [b]
      have htsplit : trun (p ++ [b]) a c = rstep (qout b (rrun p a)) (trun p a c) := by
        rw [trun_append]; simp
      have hqsplit : qcnt (p ++ [b]) a = qcnt p a + qstep b (rrun p a) := by
        rw [qcnt_append]; simp
      obtain ⟨hpT, hpD⟩ := two_pow_facts h hc
      rcases hbb with rfl | rfl | rfl
      · -- an opening `Y`
        have hbp : bal p = (h : ℤ) - 1 := by simp [bal] at hbalsum; omega
        have hh : 1 ≤ h := by
          have := hdp.bal_nonneg
          omega
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        have hbp' : bal p = (h' : ℤ) := by push_cast at hbp ⊢; omega
        obtain ⟨A1, A2, A3⟩ := ih p hlenp hdigsp hdp h' hbp' a c hc
        have e1 : (2 : ℤ) ^ (h' + 1) * (c + 1) = 2 * (2 ^ h' * (c + 1)) := by ring
        have e2 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
        have hq : qcnt (p ++ [RB.Y]) a = qcnt p a := by rw [hqsplit]; simp
        obtain ⟨hT', hD'⟩ := two_pow_facts h' hc
        rw [htsplit]
        simp only [qout, rstep_Y]
        refine ⟨by omega, fun hq1 => ?_, fun hq2 => ?_⟩
        · have := A2 (by omega)
          omega
        · have := A3 (by omega)
          omega
      · -- a closing `V`: always expanding
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        obtain ⟨A1, A2, A3⟩ := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc
        have e1 : (2 : ℤ) ^ (h + 1) * (c + 1) = 2 * (2 ^ h * (c + 1)) := by ring
        have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        have hq : qcnt (p ++ [RB.V]) a = qcnt p a + 1 := by rw [hqsplit]; simp
        rw [htsplit]
        simp only [qout, rstep_Y]
        refine ⟨by omega, fun _ => by omega, fun hq2 => ?_⟩
        have := A2 (by omega)
        omega
      · -- a closing `X`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        by_cases hodd : (rrun p a) % 2 = 1
        · -- expanding
          obtain ⟨A1, A2, A3⟩ := ih p hlenp hdigsp hdp (h + 1) hbp' a c hc
          have e1 : (2 : ℤ) ^ (h + 1) * (c + 1) = 2 * (2 ^ h * (c + 1)) := by ring
          have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
          have hq : qcnt (p ++ [RB.X]) a = qcnt p a + 1 := by
            rw [hqsplit, qstep_X, if_pos hodd]
          rw [htsplit]
          simp only [qout, hodd, if_pos, rstep_V]
          refine ⟨by omega, fun _ => by omega, fun hq2 => ?_⟩
          have := A2 (by omega)
          omega
        · -- contracting: split the last matched group off
          have hbalp : 1 ≤ bal p := by omega
          obtain ⟨q, e, rfl, hdq, hbe⟩ := dyck_split hdigsp hdp hbalp
          have hdigsq : Digs q := (hdigsp.of_append).1
          have hdigse : Digs e := ((hdigsp.of_append).2.of_cons).2
          have hlenq : q.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          have hlene : e.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          have hbq : bal q = (h : ℤ) := by
            rw [bal_append, bal_Y, hbe.2] at hbp
            omega
          obtain ⟨Q1, Q2, Q3⟩ := ih q hlenq hdigsq hdq h hbq a c hc
          set cq : ℤ := trun q a c with hcq
          set aq : ℤ := rrun q a with haq
          have hcq0 : 0 ≤ cq := by omega
          have hc1 : (0 : ℤ) ≤ 2 * cq + 1 := by omega
          obtain ⟨E1, E2, E3⟩ := ih e hlene hdigse hbe.1 0 (by simpa using hbe.2)
            (2 * aq + 1) (2 * cq + 1) hc1
          simp only [pow_zero, one_mul] at E1 E2 E3
          set c₂ : ℤ := trun e (2 * aq + 1) (2 * cq + 1) with hc₂
          set a₂ : ℤ := rrun e (2 * aq + 1) with ha₂
          -- the interior is nonempty, so it contains an expanding close
          have hne : e ≠ [] := by
            rintro rfl
            simp only [ha₂, rrun_nil] at *
            have : rrun (q ++ RB.Y :: []) a = 2 * aq + 1 := by
              rw [rrun_append, rrun_cons, rrun_nil, rstep_Y, ← haq]
            rw [this] at hodd
            omega
          have hqe : 1 ≤ qcnt e (2 * aq + 1) :=
            qcnt_pos_of_hasCl hdigse hbe.1 (HasCl.of_bal hdigse hbe hne) _
          have hE2 := E2 hqe
          -- the run of the whole word
          have hrunw : rrun (q ++ RB.Y :: e) a = a₂ := by
            rw [rrun_append, rrun_cons, rstep_Y, ← haq, ← ha₂]
          have htrunw : trun (q ++ RB.Y :: e) a c = c₂ := by
            rw [trun_append, trun_cons, rstep_Y, ← haq, ← hcq]
            simp only [qout, rstep_Y, ← hc₂]
          have hqw : qcnt ((q ++ RB.Y :: e) ++ [RB.X]) a = qcnt q a + qcnt e (2 * aq + 1) := by
            rw [hqsplit, qcnt_append, qcnt_cons, qstep_X, if_neg hodd, ← haq]
            simp
          have htw : trun ((q ++ RB.Y :: e) ++ [RB.X]) a c = c₂ / 2 - 1 := by
            rw [htsplit, htrunw, hrunw]
            have : qout RB.X a₂ = RB.X := by
              simp only [qout]
              rw [if_neg]
              rw [hrunw] at hodd
              exact hodd
            rw [this, rstep_X]
          rw [htw]
          refine ⟨by omega, fun _ => by omega, fun hq2 => ?_⟩
          rcases Nat.lt_or_ge (qcnt q a) 1 with hq0 | hq1
          · -- no expanding close before the group: the group has two
            have hqe2 : 2 ≤ qcnt e (2 * aq + 1) := by omega
            have := E3 hqe2
            omega
          · have := Q2 hq1
            omega

/-- **One expanding close gains a factor four.** -/
theorem trun_ge_pow_q1 {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) {a c : ℤ} (hc : 0 ≤ c) (hq : 1 ≤ qcnt w a) :
    2 ^ h * (4 * c + 3) - 1 ≤ trun w a c := by
  have := (trun_pow_bounds w.length w (le_refl _) hw hd h hb a c hc).2.1 hq
  have e : (2 : ℤ) ^ h * (4 * c + 3) = 4 * (2 ^ h * (c + 1)) - 2 ^ h := by ring
  omega

/-- **Two expanding closes gain a factor sixteen.** -/
theorem trun_ge_pow_q2 {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) {a c : ℤ} (hc : 0 ≤ c) (hq : 2 ≤ qcnt w a) :
    2 ^ h * (16 * c + 11) - 1 ≤ trun w a c := by
  have := (trun_pow_bounds w.length w (le_refl _) hw hd h hb a c hc).2.2 hq
  have e : (2 : ℤ) ^ h * (16 * c + 11) = 16 * (2 ^ h * (c + 1)) - 5 * 2 ^ h := by ring
  omega

/-! ## Words with at most one expanding close -/

/-- The arithmetic shape of the value of a clean Dyck prefix with at most one
expanding close: `2 ^ h - 1` when there is none, and `2 ^ h - 2 ^ k - 1` or
`2 ^ (h + 2) - 2 ^ k - 1` when there is exactly one. -/
def Shape (a : ℤ) (h q : ℕ) : Prop :=
  (q = 0 ∧ a + 1 = 2 ^ h) ∨
  (q = 1 ∧ ∃ k, k ≤ h ∧ (a + 1 = 2 ^ h - 2 ^ k ∨ a + 1 = 2 ^ (h + 2) - 2 ^ k)) ∨
  2 ≤ q

/-- One digit preserves the shape. -/
theorem shape_step {b : RB} (hb : Dig b) {a : ℤ} {h q : ℕ} (hs : Shape a h q)
    {h' : ℕ} (hh' : (h' : ℤ) = (h : ℤ) + bal [b]) (ha' : 0 ≤ rstep b a) :
    Shape (rstep b a) h' (q + qstep b a) := by
  rcases hb with rfl | rfl | rfl
  · -- `Y`: an opening letter
    have hh : h' = h + 1 := by
      have : (h' : ℤ) = (h : ℤ) + 1 := by simpa [bal] using hh'
      exact_mod_cast this
    subst hh
    simp only [rstep_Y, qstep_Y, Nat.add_zero]
    rcases hs with ⟨hq, hval⟩ | ⟨hq, k, hk, hval⟩ | hq
    · refine Or.inl ⟨hq, ?_⟩
      rw [pow_succ]
      omega
    · refine Or.inr (Or.inl ⟨hq, k + 1, by omega, ?_⟩)
      rcases hval with hval | hval
      · left
        have e1 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        have e2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      · right
        have e1 : (2 : ℤ) ^ (h + 1 + 2) = 2 * 2 ^ (h + 2) := by ring
        have e2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
    · exact Or.inr (Or.inr hq)
  · -- `V`: an expanding close
    have hh : h = h' + 1 := by
      have : (h' : ℤ) = (h : ℤ) - 1 := by simpa [bal] using hh'
      omega
    subst hh
    simp only [rstep_V, qstep_V]
    rcases hs with ⟨hq, hval⟩ | ⟨hq, k, hk, hval⟩ | hq
    · refine Or.inr (Or.inl ⟨by omega, 0, by omega, Or.inr ?_⟩)
      have e1 : (2 : ℤ) ^ (h' + 2) = 2 * 2 ^ (h' + 1) := by ring
      simp only [pow_zero]
      omega
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
  · -- `X`: a close, expanding exactly when the counter is odd
    have hh : h = h' + 1 := by
      have : (h' : ℤ) = (h : ℤ) - 1 := by simpa [bal] using hh'
      omega
    subst hh
    simp only [rstep_X] at ha' ⊢
    rw [qstep_X]
    by_cases hodd : a % 2 = 1
    · rw [if_pos hodd]
      rcases hs with ⟨hq, hval⟩ | ⟨hq, k, hk, hval⟩ | hq
      · -- the value is `2 ^ (h' + 1) - 1`
        refine Or.inr (Or.inl ⟨by omega, 0, by omega, Or.inl ?_⟩)
        have e1 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
        simp only [pow_zero]
        omega
      · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inr (by omega))
    · rw [if_neg hodd, Nat.add_zero]
      rcases hs with ⟨hq, hval⟩ | ⟨hq, k, hk, hval⟩ | hq
      · -- impossible: an even value forces `h = 0`, and then the pop underflows
        exfalso
        have e1 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
        omega
      · refine Or.inr (Or.inl ⟨hq, 0, by omega, ?_⟩)
        have hk0 : k = 0 := by
          by_contra hc
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have e2 : (2 : ℤ) ^ (k' + 1) = 2 * 2 ^ k' := by ring
          have e1 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
          have e3 : (2 : ℤ) ^ (h' + 1 + 2) = 2 * 2 ^ (h' + 2) := by ring
          rcases hval with hval | hval <;> omega
        subst hk0
        simp only [pow_zero] at hval ⊢
        rcases hval with hval | hval
        · left
          have e1 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
          omega
        · right
          have e3 : (2 : ℤ) ^ (h' + 1 + 2) = 2 * 2 ^ (h' + 2) := by ring
          omega
      · exact Or.inr (Or.inr hq)

/-- The shape is preserved along a whole clean Dyck prefix. -/
theorem shape_run : ∀ (w : List RB), Digs w → ∀ (a : ℤ) (h q : ℕ), Shape a h q →
    (∀ p, p <+: w → 0 ≤ (h : ℤ) + bal p) → 0 ≤ rrun w a →
    ∀ (h' : ℕ), (h' : ℤ) = (h : ℤ) + bal w → Shape (rrun w a) h' (q + qcnt w a) := by
  intro w
  induction w with
  | nil =>
      intro _ a h q hs _ _ h' hh'
      obtain rfl : h' = h := by simp only [bal_nil, add_zero] at hh'; exact_mod_cast hh'
      simpa using hs
  | cons b w ih =>
      intro hdigs a h q hs hpre hcl h' hh'
      obtain ⟨hb, hw⟩ := hdigs.of_cons
      -- the value after the first digit
      have ha1 : 0 ≤ rstep b a := by
        have := rrun_nonneg_of_nonneg (w := [b]) (v := w) hw (a := a) (by simpa using hcl)
        simpa using this
      -- the height after the first digit
      have hb1 : 0 ≤ (h : ℤ) + bal [b] := hpre [b] (by simp)
      obtain ⟨h1, hh1⟩ : ∃ h1 : ℕ, (h1 : ℤ) = (h : ℤ) + bal [b] :=
        ⟨((h : ℤ) + bal [b]).toNat, Int.toNat_of_nonneg hb1⟩
      have hs1 : Shape (rstep b a) h1 (q + qstep b a) := shape_step hb hs hh1 ha1
      have hpre1 : ∀ p, p <+: w → 0 ≤ (h1 : ℤ) + bal p := by
        intro p hp
        have := hpre (b :: p) (by exact List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        have hbb : bal (b :: p) = bal [b] + bal p := by
          have : (b :: p) = [b] ++ p := rfl
          rw [this, bal_append]
        omega
      have hh2 : (h' : ℤ) = (h1 : ℤ) + bal w := by
        have hbb : bal (b :: w) = bal [b] + bal w := by
          have : (b :: w) = [b] ++ w := rfl
          rw [this, bal_append]
        omega
      have := ih hw (rstep b a) h1 (q + qstep b a) hs1 hpre1 (by simpa using hcl) h' hh2
      simpa [Nat.add_assoc] using this

/-- **The value of a clean Dyck prefix with at most one expanding close** is
odd or of the form `2 ^ e - 2`, as soon as its height is at least two. -/
theorem rrun_shape_le_one {w : List RB} (hw : Digs w) (hd : DyckPre w) (ha : 0 ≤ rrun w 0)
    (hq : qcnt w 0 ≤ 1) {h : ℕ} (hb : bal w = (h : ℤ)) (hh : 2 ≤ h) :
    rrun w 0 % 2 = 1 ∨ ∃ e, 2 ≤ e ∧ rrun w 0 = 2 ^ e - 2 := by
  have hs : Shape (rrun w 0) h (0 + qcnt w 0) := by
    refine shape_run w hw 0 0 0 (Or.inl ⟨rfl, by norm_num⟩) ?_ ha h ?_
    · intro p hp
      simpa using hd p hp
    · simpa using hb.symm
  rcases hs with ⟨-, hval⟩ | ⟨-, k, hk, hval⟩ | hq2
  · -- no close at all: the value is `2 ^ h - 1`, which is odd
    refine Or.inl ?_
    have h2 : (2 : ℤ) ∣ 2 ^ h := dvd_pow_self 2 (by omega)
    omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · -- the close is at the very bottom: the value is `2 ^ e - 2`
      refine Or.inr ?_
      simp only [pow_zero] at hval
      rcases hval with hv | hv
      · exact ⟨h, hh, by omega⟩
      · exact ⟨h + 2, by omega, by omega⟩
    · -- otherwise both `2 ^ h` and `2 ^ k` are even, so the value is odd
      refine Or.inl ?_
      have h2 : (2 : ℤ) ∣ 2 ^ h := dvd_pow_self 2 (by omega)
      have h2k : (2 : ℤ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have h2' : (2 : ℤ) ∣ 2 ^ (h + 2) := dvd_pow_self 2 (by omega)
      rcases hval with hv | hv <;> omega
  · omega

/-- **A clean Dyck prefix with at most one expanding close has a value that is
not divisible by four**, as soon as its height is at least two. -/
theorem rrun_mod_four_ne {w : List RB} (hw : Digs w) (hd : DyckPre w) (ha : 0 ≤ rrun w 0)
    (hq : qcnt w 0 ≤ 1) {h : ℕ} (hb : bal w = (h : ℤ)) (hh : 2 ≤ h) : rrun w 0 % 4 ≠ 0 := by
  have hs : Shape (rrun w 0) h (0 + qcnt w 0) := by
    refine shape_run w hw 0 0 0 (Or.inl ⟨rfl, by norm_num⟩) ?_ ha h ?_
    · intro p hp
      simpa using hd p hp
    · simpa using hb.symm
  -- `2 ^ h` is divisible by four, `2 ^ k` is `1`, `2` or divisible by four
  have h4 : (4 : ℤ) ∣ 2 ^ h := by
    obtain ⟨m, rfl⟩ : ∃ m, h = m + 2 := ⟨h - 2, by omega⟩
    exact ⟨2 ^ m, by ring⟩
  rcases hs with ⟨-, hval⟩ | ⟨-, k, hk, hval⟩ | hq2
  · omega
  · have h4' : (4 : ℤ) ∣ 2 ^ (h + 2) := ⟨2 ^ h, by ring⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> simp only [pow_zero, pow_one] at hval <;> omega
    · have h4k : (4 : ℤ) ∣ 2 ^ k := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        exact ⟨2 ^ m, by ring⟩
      omega
  · omega

end BB25.Prefix
