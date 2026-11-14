/-
# `0LB`: the energy of a reset word

The `0LB` member pays **four** decrements at every pop its `<B1` sweep
crosses (`W <B1 → D⁴ … <B1 22`).  The supply of those decrements is certified
by an integer *energy*: the reset arithmetic of `Word.lean` with the pop map
`a ↦ ⌊a/2⌋ - 1` replaced by `e ↦ ⌊e/2⌋ - 3` (`estep`, `erun`).

This file is the word level of the argument:

* `erun_le_rrun`, `erun_add_two_le_rrun`: energy is a lower bound of the reset
  value, with a margin of two as soon as the word contains a pop;
* `etrun`: the energy of the *transduced* word (the first counter still runs
  with the reset arithmetic), and `qw`, the transduced word itself;
* `etrun_ge_egain`: the energy analogue of `trun_ge_qgain` (Lemma 3.1 of the
  submitted argument): a Dyck prefix of height `h` with at least `q` expanding
  closes sends an energy `e ≥ 1` to at least `2^h (4^q (e+1) - 5 qloss q) - 1`;
* `TW_facts`, `dpow_TW_facts`: the counter, decoded value, decoded word and
  height of a (partly paid-off) paid reset stack, read off the reset word.
-/
import RequestProject.BB25.Prefix.Slack
import RequestProject.BB25.Prefix.LA.Exact

namespace BB25.Prefix

open BB25

/-! ## The energy of a word -/

/-- One digit of the energy arithmetic. -/
def estep (b : RB) (e : ℤ) : ℤ :=
  match b with
  | .Y => 2 * e + 1
  | .V => 2 * e
  | .X => e / 2 - 3
  | _ => e

@[simp] theorem estep_Y (e : ℤ) : estep .Y e = 2 * e + 1 := rfl
@[simp] theorem estep_V (e : ℤ) : estep .V e = 2 * e := rfl
@[simp] theorem estep_X (e : ℤ) : estep .X e = e / 2 - 3 := rfl

/-- The energy of a whole word, read in tape order. -/
def erun : List RB → ℤ → ℤ
  | [], e => e
  | b :: w, e => erun w (estep b e)

@[simp] theorem erun_nil (e : ℤ) : erun [] e = e := rfl
@[simp] theorem erun_cons (b : RB) (w : List RB) (e : ℤ) :
    erun (b :: w) e = erun w (estep b e) := rfl

theorem erun_append (w v : List RB) (e : ℤ) : erun (w ++ v) e = erun v (erun w e) := by
  induction w generalizing e with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem erun_singleton (b : RB) (e : ℤ) : erun [b] e = estep b e := rfl

theorem estep_le_rstep {e a : ℤ} (b : RB) (h : e ≤ a) : estep b e ≤ rstep b a := by
  cases b <;> simp [estep, rstep] <;> omega

/-- Energy never exceeds the reset value. -/
theorem erun_le_rrun (w : List RB) {e a : ℤ} (h : e ≤ a) : erun w e ≤ rrun w a := by
  induction w generalizing e a with
  | nil => exact h
  | cons b w ih => exact ih (estep_le_rstep b h)

/-- After a pop, the reset value exceeds the energy by at least two. -/
theorem erun_add_two_le_rrun {w : List RB} (hX : RB.X ∈ w) {e a : ℤ} (h : e ≤ a) :
    erun w e + 2 ≤ rrun w a := by
  induction w generalizing e a with
  | nil => simp at hX
  | cons b w ih =>
      rcases List.mem_cons.mp hX with rfl | hX'
      · simp only [erun_cons, rrun_cons, estep_X, rstep_X]
        have h2 : e / 2 - 3 + 2 ≤ a / 2 - 1 := by omega
        have key : ∀ (v : List RB) (x y : ℤ), x + 2 ≤ y → erun v x + 2 ≤ rrun v y := by
          intro v
          induction v with
          | nil => intro x y hxy; exact hxy
          | cons c v ihv =>
              intro x y hxy
              refine ihv _ _ ?_
              cases c <;> simp [estep, rstep] <;> omega
        exact key w _ _ h2
      · exact ih hX' (estep_le_rstep b h)

/-! ## The transduced word and its energy -/

/-- The transduced word: the word a later overflow deposits. -/
def qw : List RB → ℤ → List RB
  | [], _ => []
  | b :: w, a => qout b a :: qw w (rstep b a)

@[simp] theorem qw_nil (a : ℤ) : qw [] a = [] := rfl
@[simp] theorem qw_cons (b : RB) (w : List RB) (a : ℤ) :
    qw (b :: w) a = qout b a :: qw w (rstep b a) := rfl

theorem qw_append (w v : List RB) (a : ℤ) : qw (w ++ v) a = qw w a ++ qw v (rrun w a) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem qw_digs {w : List RB} (hw : Digs w) (a : ℤ) : Digs (qw w a) := by
  induction w generalizing a with
  | nil => exact Digs.nil
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      exact Digs.cons (qout_dig hb a) (ih hw' _)

theorem trun_eq_rrun_qw (w : List RB) (a c : ℤ) : trun w a c = rrun (qw w a) c := by
  induction w generalizing a c with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- The energy of the transduced word; the first counter runs with the reset
arithmetic. -/
def etrun : List RB → ℤ → ℤ → ℤ
  | [], _, e => e
  | b :: w, a, e => etrun w (rstep b a) (estep (qout b a) e)

@[simp] theorem etrun_nil (a e : ℤ) : etrun [] a e = e := rfl
@[simp] theorem etrun_cons (b : RB) (w : List RB) (a e : ℤ) :
    etrun (b :: w) a e = etrun w (rstep b a) (estep (qout b a) e) := rfl

theorem etrun_append (w v : List RB) (a e : ℤ) :
    etrun (w ++ v) a e = etrun v (rrun w a) (etrun w a e) := by
  induction w generalizing a e with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem etrun_eq_erun_qw (w : List RB) (a e : ℤ) : etrun w a e = erun (qw w a) e := by
  induction w generalizing a e with
  | nil => rfl
  | cons b w ih => simp [ih]

/-! ## Heights -/

/-- The height of the paid reset stack of a word: bits count `+1`, pops `-1`. -/
def ht : List RB → ℤ
  | [] => 0
  | .X :: w => ht w - 1
  | _ :: w => ht w + 1

@[simp] theorem ht_nil : ht [] = 0 := rfl
@[simp] theorem ht_Y (w : List RB) : ht (.Y :: w) = ht w + 1 := rfl
@[simp] theorem ht_V (w : List RB) : ht (.V :: w) = ht w + 1 := rfl
@[simp] theorem ht_X (w : List RB) : ht (.X :: w) = ht w - 1 := rfl

theorem ht_append (w v : List RB) : ht (w ++ v) = ht w + ht v := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [ht, ih] <;> ring

theorem bal_le_ht {w : List RB} (hw : Digs w) : bal w ≤ ht w := by
  induction w with
  | nil => simp
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have := ih hw'
      rcases hb with rfl | rfl | rfl <;> simp <;> omega

/-- The transduced word has the height of the original one as its balance. -/
theorem bal_qw {w : List RB} (hw : Digs w) (a : ℤ) : bal (qw w a) = ht w := by
  induction w generalizing a with
  | nil => simp
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have := ih hw' (rstep b a)
      rcases hb with rfl | rfl | rfl
      · simp only [rstep_Y] at this; simp [qout, this]
      · simp only [rstep_V] at this; simp [qout, this]
      · simp only [rstep_X] at this; by_cases h : a % 2 = 1 <;> simp [qout, h, this]

/-- The height is at most the balance plus twice the expanding closes. -/
theorem ht_le_bal_qcnt {w : List RB} (hw : Digs w) (a : ℤ) :
    ht w ≤ bal w + 2 * (qcnt w a : ℤ) := by
  induction w generalizing a with
  | nil => simp
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have := ih hw' (rstep b a)
      rcases hb with rfl | rfl | rfl
      · simp only [ht_Y, bal_Y, qcnt_cons, qstep_Y]; push_cast; omega
      · simp only [ht_V, bal_V, qcnt_cons, qstep_V]; push_cast; omega
      · simp only [ht_X, bal_X, qcnt_cons, qstep_X]
        split_ifs <;> push_cast <;> omega

theorem ht_ge_neg_length (w : List RB) : -(w.length : ℤ) ≤ ht w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [ht] <;> omega

/-! ## Dyck prefixes of transduced words -/

theorem DyckPre.snoc {w : List RB} {b : RB} (hw : DyckPre w) (hb : 0 ≤ bal (w ++ [b])) :
    DyckPre (w ++ [b]) := by
  intro p hp
  rcases prefix_append_cases hp with h | ⟨q, rfl, hq⟩
  · exact hw p h
  · rcases prefix_singleton_cases hq with rfl | rfl
    · simpa using hw.bal_nonneg
    · exact hb

theorem dyckPre_qw {v : List RB} (hv : Digs v) (hd : DyckPre v) (a : ℤ) :
    DyckPre (qw v a) := by
  induction v using List.reverseRecOn with
  | nil => exact DyckPre.nil
  | append_singleton p b ih =>
      have hp : Digs p := hv.of_append.1
      have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
      rw [qw_append]
      have hq : qw [b] (rrun p a) = [qout b (rrun p a)] := rfl
      rw [hq]
      refine DyckPre.snoc (ih hp hdp) ?_
      rw [← hq, ← qw_append, bal_qw hv]
      exact le_trans (hd (p ++ [b]) (List.prefix_refl _)) (bal_le_ht hv)

/-! ## The energy analogue of the expanding-close bound -/

/-- The energy gain of a Dyck prefix with `q` expanding closes. -/
def egain (q : ℕ) (e : ℤ) : ℤ := 4 ^ q * (e + 1) - 5 * qloss q

theorem egain_zero (e : ℤ) : egain 0 e = e + 1 := by simp [egain]

theorem egain_succ (q : ℕ) (e : ℤ) : egain (q + 1) e = 4 * egain q e - 5 := by
  simp only [egain, qloss_succ, pow_succ]
  ring

theorem egain_two_le {e : ℤ} (he : 1 ≤ e) : ∀ q : ℕ, 2 ≤ egain q e := by
  intro q
  induction q with
  | zero => rw [egain_zero]; omega
  | succ q ih => rw [egain_succ]; omega

theorem egain_mono {e : ℤ} (he : 1 ≤ e) {q Q : ℕ} (h : q ≤ Q) : egain q e ≤ egain Q e := by
  obtain ⟨d, rfl⟩ : ∃ d, Q = q + d := ⟨Q - q, by omega⟩
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
      rw [← Nat.add_assoc, egain_succ]
      have := egain_two_le he (q + d)
      have := ih (by omega)
      omega

theorem egain_add (i j : ℕ) (e : ℤ) : egain (i + j) e = 4 ^ j * egain i e - 5 * qloss j := by
  simp only [egain, qloss_add i j, pow_add]
  ring

theorem qloss_odd {q : ℕ} (hq : 1 ≤ q) : qloss q % 2 = 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [qloss_succ]
  omega

theorem four_pow_eq_qloss (q : ℕ) : (4 : ℤ) ^ q = 3 * qloss q + 1 := by
  have := three_qloss q
  omega

private theorem etrun_gain_aux : ∀ (n : ℕ) (w : List RB), w.length ≤ n → Digs w → DyckPre w →
    ∀ (h : ℕ), bal w = (h : ℤ) → ∀ a e : ℤ, 1 ≤ e → ∀ q : ℕ, q ≤ qcnt w a →
      2 ^ h * egain q e ≤ etrun w a e + 1 := by
  intro n
  induction n with
  | zero =>
      intro w hlen _ _ h hbal a e he q hq
      obtain rfl : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      simp only [bal_nil] at hbal
      obtain rfl : h = 0 := by exact_mod_cast hbal.symm
      simp only [qcnt_nil, Nat.le_zero] at hq
      subst hq
      simp only [etrun_nil, pow_zero, one_mul, egain_zero]
      omega
  | succ n ih =>
      intro w hlen hdigs hd h hbal a e he q hq
      rcases List.eq_nil_or_concat w with rfl | ⟨p, b, hcat⟩
      · simp only [bal_nil] at hbal
        obtain rfl : h = 0 := by exact_mod_cast hbal.symm
        simp only [qcnt_nil, Nat.le_zero] at hq
        subst hq
        simp only [etrun_nil, pow_zero, one_mul, egain_zero]
        omega
      rw [List.concat_eq_append] at hcat
      subst hcat
      have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
      have hdigsp : Digs p := (hdigs.of_append).1
      have hlenp : p.length ≤ n := by
        have : (p ++ [b]).length = p.length + 1 := by simp
        omega
      have hbb : Dig b := (hdigs.of_append).2 b (by simp)
      have hbalsum : bal (p ++ [b]) = bal p + bal [b] := bal_append p [b]
      have htsplit : etrun (p ++ [b]) a e = estep (qout b (rrun p a)) (etrun p a e) := by
        rw [etrun_append]; simp
      have hqsplit : qcnt (p ++ [b]) a = qcnt p a + qstep b (rrun p a) := by
        rw [qcnt_append]; simp
      have hP : (1 : ℤ) ≤ 2 ^ h := by
        have : (0 : ℤ) < 2 ^ h := by positivity
        omega
      have hgn : ∀ H Q : ℕ, (2 : ℤ) ≤ 2 ^ H * egain Q e := by
        intro H Q
        have h1 : (1 : ℤ) ≤ 2 ^ H := by
          have : (0 : ℤ) < 2 ^ H := by positivity
          omega
        have h2 := egain_two_le he Q
        nlinarith
      rcases hbb with rfl | rfl | rfl
      · -- an opening `Y`
        have hbp : bal p = (h : ℤ) - 1 := by simp [bal] at hbalsum; omega
        have hh : 1 ≤ h := by
          have := hdp.bal_nonneg
          omega
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        have hbp' : bal p = (h' : ℤ) := by push_cast at hbp ⊢; omega
        have hq' : q ≤ qcnt p a := by rw [hqsplit] at hq; simpa using hq
        have A := ih p hlenp hdigsp hdp h' hbp' a e he q hq'
        rw [htsplit]
        simp only [qout, estep_Y]
        have e2 : (2 : ℤ) ^ (h' + 1) = 2 * 2 ^ h' := by ring
        rw [e2]
        linarith
      · -- a closing `V`: always expanding, transduced to `Y`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have hqv : qcnt (p ++ [RB.V]) a = qcnt p a + 1 := by rw [hqsplit]; simp
        have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        rw [htsplit]
        simp only [qout, estep_Y]
        rcases Nat.lt_or_ge (qcnt p a) q with hlt | hge
        · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          have hq'' : q' ≤ qcnt p a := by omega
          have A := ih p hlenp hdigsp hdp (h + 1) hbp' a e he q' hq''
          rw [e2] at A
          rw [egain_succ]
          nlinarith [hP, A]
        · have A := ih p hlenp hdigsp hdp (h + 1) hbp' a e he q hge
          rw [e2] at A
          linarith [hgn h q]
      · -- a closing `X`
        have hbp : bal p = (h : ℤ) + 1 := by simp [bal] at hbalsum; omega
        have hbp' : bal p = ((h + 1 : ℕ) : ℤ) := by push_cast; omega
        have e2 : (2 : ℤ) ^ (h + 1) = 2 * 2 ^ h := by ring
        by_cases hodd : (rrun p a) % 2 = 1
        · -- expanding: transduced to `V`
          have hqv : qcnt (p ++ [RB.X]) a = qcnt p a + 1 := by
            rw [hqsplit, qstep_X, if_pos hodd]
          rw [htsplit]
          simp only [qout, hodd, if_pos, estep_V]
          rcases Nat.lt_or_ge (qcnt p a) q with hlt | hge
          · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
            have hq'' : q' ≤ qcnt p a := by rw [hqv] at hq; omega
            have A := ih p hlenp hdigsp hdp (h + 1) hbp' a e he q' hq''
            rw [e2] at A
            rw [egain_succ]
            nlinarith [hP, A]
          · have A := ih p hlenp hdigsp hdp (h + 1) hbp' a e he q hge
            rw [e2] at A
            linarith [hgn h q]
        · -- contracting: split the last matched group off
          have hbalp : 1 ≤ bal p := by omega
          obtain ⟨u, g, rfl, hdu, hbe⟩ := dyck_split hdigsp hdp hbalp
          have hdigsu : Digs u := (hdigsp.of_append).1
          have hdigse : Digs g := ((hdigsp.of_append).2.of_cons).2
          have hlenu : u.length ≤ n := by
            have h1 : (u ++ RB.Y :: g).length = u.length + g.length + 1 := by simp; omega
            omega
          have hlene : g.length ≤ n := by
            have h1 : (u ++ RB.Y :: g).length = u.length + g.length + 1 := by simp; omega
            omega
          have hbu : bal u = (h : ℤ) := by
            rw [bal_append, bal_Y, hbe.2] at hbp
            omega
          set cu : ℤ := etrun u a e with hcu
          set au : ℤ := rrun u a with hau
          set c₂ : ℤ := etrun g (2 * au + 1) (2 * cu + 1) with hc₂
          set a₂ : ℤ := rrun g (2 * au + 1) with ha₂
          have hne : g ≠ [] := by
            rintro rfl
            simp only [ha₂, rrun_nil] at *
            have hr : rrun (u ++ RB.Y :: []) a = 2 * au + 1 := by
              rw [rrun_append, rrun_cons, rrun_nil, rstep_Y, ← hau]
            rw [hr] at hodd
            omega
          have hqe : 1 ≤ qcnt g (2 * au + 1) :=
            qcnt_pos_of_hasCl hdigse hbe.1 (HasCl.of_bal hdigse hbe hne) _
          have hrunw : rrun (u ++ RB.Y :: g) a = a₂ := by
            rw [rrun_append, rrun_cons, rstep_Y, ← hau, ← ha₂]
          have htrunw : etrun (u ++ RB.Y :: g) a e = c₂ := by
            rw [etrun_append, etrun_cons, rstep_Y, ← hau, ← hcu]
            simp only [qout, estep_Y, ← hc₂]
          have hqw : qcnt ((u ++ RB.Y :: g) ++ [RB.X]) a = qcnt u a + qcnt g (2 * au + 1) := by
            rw [hqsplit, qcnt_append, qcnt_cons, qstep_X, if_neg hodd, ← hau]
            simp
          have htw : etrun ((u ++ RB.Y :: g) ++ [RB.X]) a e = c₂ / 2 - 3 := by
            rw [htsplit, htrunw, hrunw]
            have hqX : qout RB.X a₂ = RB.X := by
              simp only [qout]
              rw [if_neg]
              rw [hrunw] at hodd
              exact hodd
            rw [hqX, estep_X]
          rw [htw]
          rw [hqw] at hq
          obtain ⟨q'', q', hq''A, hq'E, hq'1, hqsum⟩ :
              ∃ q'' q' : ℕ, q'' ≤ qcnt u a ∧ q' ≤ qcnt g (2 * au + 1) ∧ 1 ≤ q' ∧
                q ≤ q'' + q' := by
            rcases Nat.lt_or_ge (qcnt u a) q with hlt | hle
            · exact ⟨qcnt u a, q - qcnt u a, le_refl _, by omega, by omega, by omega⟩
            · exact ⟨q, 1, hle, hqe, le_refl 1, by omega⟩
          have A := ih u hlenu hdigsu hdu h hbu a e he q'' hq''A
          have hcu1 : 1 ≤ cu := by
            have := hgn h q''
            omega
          have B := ih g hlene hdigse hbe.1 0 (by simpa using hbe.2) (2 * au + 1)
            (2 * cu + 1) (by omega) q' hq'E
          rw [pow_zero, one_mul] at B
          -- the interior: `c₂ ≥ 2 A cu + M + 1` with `A = 4^q' = 3M+1`
          set M : ℤ := qloss q' with hMdef
          have hM1 : 1 ≤ M := qloss_one_le hq'1
          have hModd : M % 2 = 1 := qloss_odd hq'1
          have hA : (4 : ℤ) ^ q' = 3 * M + 1 := four_pow_eq_qloss q'
          have hB : 2 * ((3 * M + 1) * cu) + M + 1 ≤ c₂ := by
            simp only [egain, hA] at B
            nlinarith [B]
          -- the contracting close
          have hC : (3 * M + 1) * cu - 2 * M ≤ c₂ / 2 - 3 := by
            have : (2 * ((3 * M + 1) * cu) + M + 1) / 2 ≤ c₂ / 2 :=
              Int.ediv_le_ediv (by norm_num) hB
            have h2 : (2 * ((3 * M + 1) * cu) + M + 1) / 2 = (3 * M + 1) * cu + (M + 1) / 2 := by
              omega
            omega
          -- the gain
          have hgain : egain q e ≤ (3 * M + 1) * egain q'' e - 5 * M := by
            calc egain q e ≤ egain (q'' + q') e := egain_mono he hqsum
              _ = 4 ^ q' * egain q'' e - 5 * qloss q' := egain_add _ _ _
              _ = (3 * M + 1) * egain q'' e - 5 * M := by rw [hA]
          obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, Z = 2 ^ h * egain q'' e := ⟨_, rfl⟩
          have hZcu : Z ≤ cu + 1 := by rw [hZ]; exact A
          have hmul : 2 ^ h * egain q e ≤ (3 * M + 1) * Z - 5 * M * 2 ^ h := by
            have := mul_le_mul_of_nonneg_left hgain (show (0 : ℤ) ≤ 2 ^ h by positivity)
            rw [hZ]
            linarith
          have h3 : (3 * M + 1) * Z ≤ (3 * M + 1) * cu + (3 * M + 1) := by
            have := mul_le_mul_of_nonneg_left hZcu (show (0 : ℤ) ≤ 3 * M + 1 by omega)
            linarith
          have h4 : 5 * M ≤ 5 * M * 2 ^ h := by
            have := mul_le_mul_of_nonneg_left hP (show (0 : ℤ) ≤ 5 * M by omega)
            linarith
          linarith

/-- **The energy analogue of the expanding-close bound.** -/
theorem etrun_ge_egain {w : List RB} (hw : Digs w) (hd : DyckPre w) {h : ℕ}
    (hb : bal w = (h : ℤ)) {a e : ℤ} (he : 1 ≤ e) {q : ℕ} (hq : q ≤ qcnt w a) :
    2 ^ h * egain q e ≤ etrun w a e + 1 :=
  etrun_gain_aux w.length w (le_refl _) hw hd h hb a e he q hq

/-! ## The paid reset stack of a word -/

/-- The decoded word of a paid reset stack is the transduced word. -/
theorem pdec_tfold : ∀ (w : List RB), Digs w → ∀ {σ : List LB}, CStack σ → Adm σ → Good σ →
    0 ≤ rrun w (cval σ) → pdec (tfold σ w) = pdec σ ++ qw w (cval σ) := by
  intro w
  induction w with
  | nil => intro _ σ _ _ _ _; simp
  | cons b w ih =>
      intro hw σ hst hadm hg hcl
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have hcl1 : 0 ≤ rstep b (cval σ) := by
        have := rrun_nonneg_of_nonneg (w := [b]) (v := w) hw' (a := (cval σ : ℤ))
          (by simpa using hcl)
        simpa using this
      obtain ⟨hst1, hadm1, hg1, hcv1, -, -⟩ := tstep_props hb hst hadm hg hcl1
      have hcl2 : 0 ≤ rrun w (cval (tstep σ b)) := by rw [hcv1]; simpa using hcl
      rw [tfold_cons, ih hw' hst1 hadm1 hg1 hcl2, hcv1, qw_cons]
      have hstep : pdec (tstep σ b) = pdec σ ++ [qout b (cval σ)] := by
        rcases hb with rfl | rfl | rfl
        · simp [qout]
        · simp [qout]
        · have ha2 : 2 ≤ cval σ := by
            simp only [rstep_X] at hcl1
            omega
          have hWv : 1 ≤ cval (.W :: σ) := by simp only [cval_W]; omega
          rw [tstep_X, pdec_cdec hst.consW hWv, pdec_W]
          by_cases hodd : cval σ % 2 = 1
          · have : (cval σ : ℤ) % 2 = 1 := by omega
            simp [qout, hodd, this]
          · have : (cval σ : ℤ) % 2 ≠ 1 := by omega
            simp [qout, hodd, this]
      rw [hstep, List.append_assoc]
      rfl

theorem nbit_nsh_tfold : ∀ (w : List RB), Digs w → ∀ (σ : List LB),
    (nbit (tfold σ w) : ℤ) - nsh (tfold σ w) = (nbit σ : ℤ) - nsh σ + ht w := by
  intro w
  induction w with
  | nil => intro _ σ; simp
  | cons b w ih =>
      intro hw σ
      obtain ⟨hb, hw'⟩ := hw.of_cons
      rw [tfold_cons, ih hw']
      rcases hb with rfl | rfl | rfl
      · simp; ring
      · simp; ring
      · simp only [tstep_X, nbit_cdec, nsh_cdec, nbit_W, nsh_W, ht_X]
        push_cast
        ring

/-- The facts about a paid reset stack over the bottom block. -/
theorem TW_facts {w : List RB} (hw : Digs w) (hcl : 0 ≤ rrun w 0) :
    CStack (TW w) ∧ Adm (TW w) ∧ Good (TW w) ∧ (cval (TW w) : ℤ) = rrun w 0 ∧
      bval (TW w) = trun w 0 0 ∧ pdec (TW w) = qw w 0 ∧
      (nbit (TW w) : ℤ) - nsh (TW w) = ht w := by
  have hL : cval ([LB.L] : List LB) = 0 := rfl
  have hcl' : 0 ≤ rrun w (cval ([LB.L] : List LB)) := by rw [hL]; simpa using hcl
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := tfold_props w hw CStack.base adm_L good_L hcl'
  have h6 := pdec_tfold w hw CStack.base adm_L good_L hcl'
  have h7 := nbit_nsh_tfold w hw [LB.L]
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · rw [TW, h4, hL]; rfl
  · rw [TW, h5, hL]; rfl
  · rw [TW, h6, hL]; rfl
  · rw [TW, h7]; simp

/-- The facts about a partly paid-off reset stack. -/
theorem dpow_TW_facts {w : List RB} (hw : Digs w) {k : ℕ} (hk : (k : ℤ) ≤ rrun w 0) :
    CStack (dpow k (TW w)) ∧ Adm (dpow k (TW w)) ∧ Good (dpow k (TW w)) ∧
      (cval (dpow k (TW w)) : ℤ) = rrun w 0 - k ∧
      bval (dpow k (TW w)) = trun w 0 0 ∧ pdec (dpow k (TW w)) = qw w 0 ∧
      (nbit (dpow k (TW w)) : ℤ) - nsh (dpow k (TW w)) = ht w := by
  have hcl : 0 ≤ rrun w 0 := le_trans (by positivity) hk
  obtain ⟨hst, hadm, hg, hcv, hbv, hpd, hnb⟩ := TW_facts hw hcl
  induction k with
  | zero => exact ⟨hst, hadm, hg, by simpa using hcv, hbv, hpd, hnb⟩
  | succ k ih =>
      obtain ⟨hst', hadm', hg', hcv', hbv', hpd', hnb'⟩ := ih (by push_cast at hk; omega)
      have h1 : 1 ≤ cval (dpow k (TW w)) := by push_cast at hk; omega
      rw [dpow_succ]
      refine ⟨cdec_CStack_all hst', Adm.cdec hst' hadm' h1, Good.cdec hst' hg' h1, ?_, ?_, ?_, ?_⟩
      · rw [cdec_cval hst' h1]; push_cast; omega
      · rw [bval_cdec hst' h1, hbv']
      · rw [pdec_cdec hst' h1, hpd']
      · rw [nbit_cdec, nsh_cdec, hnb']

end BB25.Prefix
