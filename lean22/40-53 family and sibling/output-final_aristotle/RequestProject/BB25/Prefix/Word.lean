/-
# The reset word arithmetic and the matched-group expansion lemma

This file develops the *word level* of the prefix-safety analysis of the
`3RA` and `2LA` members of the family.

A **reset word** is a word over the three digit blocks `Y = 22`, `V = 21` and
`X = 11`, read in tape order.  The machine consumes such a word in the reset
phase, building a counter.  In the *adjusted* coordinate — the physical
counter value minus one whenever the pending digit is `1>`, i.e. the pending
decrement charged immediately — the three blocks act on the counter by

```
  Y : a ↦ 2a + 1        V : a ↦ 2a        X : a ↦ ⌊a/2⌋ - 1
```

(`rstep`).  The arithmetic is done in `ℤ`: a negative value records an unpaid
borrow, i.e. the fact that the machine overflows instead of finishing the
word.  All three maps send negative values to negative values
(`rstep_neg`), so a nonnegative final value certifies that no prefix of the
word overflows (`rrun_nonneg_of_nonneg`).

The second ingredient is the **transducer** `qout`: while the machine consumes
a reset word it builds a counter stack, and the word that a later overflow
would deposit from that stack is the transduced word — `Y` and `V` both
deposit `Y`, while `X` deposits `V` or `X` according to the parity of the
counter before it (this is the matched bit).  `trun` runs a word through the
transducer and evaluates the output with `rstep` at the same time.

The main result is `trun_ge_of_hasCl`: a *Dyck prefix* containing at least one
closing letter multiplies the second counter by four (plus two).  Its
corollary `trun_ge_two` is the case needed by the main proof: a nonempty clean
Dyck prefix whose own value is `0` transduces to a word of value at least `2`.
-/
import Mathlib
import RequestProject.BB25.Blocks

namespace BB25.Prefix

open BB25

/-! ## The three digit letters -/

/-- The letters of a reset word. -/
def Dig (b : RB) : Prop := b = .Y ∨ b = .V ∨ b = .X

/-- A word over the three digit letters. -/
def Digs (w : List RB) : Prop := ∀ b ∈ w, Dig b

theorem Digs.nil : Digs [] := by intro b hb; simp at hb

theorem Digs.cons {b : RB} {w : List RB} (hb : Dig b) (hw : Digs w) : Digs (b :: w) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hb
  · exact hw c hc

theorem Digs.of_cons {b : RB} {w : List RB} (h : Digs (b :: w)) : Dig b ∧ Digs w :=
  ⟨h b (by simp), fun c hc => h c (by simp [hc])⟩

theorem Digs.append {w v : List RB} (hw : Digs w) (hv : Digs v) : Digs (w ++ v) := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact hw b h
  · exact hv b h

theorem Digs.of_append {w v : List RB} (h : Digs (w ++ v)) : Digs w ∧ Digs v :=
  ⟨fun b hb => h b (by simp [hb]), fun b hb => h b (by simp [hb])⟩

/-! ## The reset arithmetic -/

/-- One digit of the reset arithmetic, in the adjusted coordinate. -/
def rstep (b : RB) (a : ℤ) : ℤ :=
  match b with
  | .Y => 2 * a + 1
  | .V => 2 * a
  | .X => a / 2 - 1
  | _ => a

@[simp] theorem rstep_Y (a : ℤ) : rstep .Y a = 2 * a + 1 := rfl
@[simp] theorem rstep_V (a : ℤ) : rstep .V a = 2 * a := rfl
@[simp] theorem rstep_X (a : ℤ) : rstep .X a = a / 2 - 1 := rfl

/-- The reset arithmetic of a whole word, read in tape order. -/
def rrun : List RB → ℤ → ℤ
  | [], a => a
  | b :: w, a => rrun w (rstep b a)

@[simp] theorem rrun_nil (a : ℤ) : rrun [] a = a := rfl
@[simp] theorem rrun_cons (b : RB) (w : List RB) (a : ℤ) :
    rrun (b :: w) a = rrun w (rstep b a) := rfl

theorem rrun_append (w v : List RB) (a : ℤ) : rrun (w ++ v) a = rrun v (rrun w a) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem rstep_mono {a a' : ℤ} (b : RB) (h : a ≤ a') : rstep b a ≤ rstep b a' := by
  cases b <;> simp [rstep] <;> omega

theorem rrun_mono {a a' : ℤ} (w : List RB) (h : a ≤ a') : rrun w a ≤ rrun w a' := by
  induction w generalizing a a' with
  | nil => exact h
  | cons b w ih => exact ih (rstep_mono b h)

/-- All three digit maps keep a negative value negative: an unpaid borrow is
never repaid. -/
theorem rstep_neg {b : RB} (hb : Dig b) {a : ℤ} (h : a < 0) : rstep b a < 0 := by
  rcases hb with rfl | rfl | rfl <;> simp [rstep] <;> omega

theorem rrun_neg {w : List RB} (hw : Digs w) {a : ℤ} (h : a < 0) : rrun w a < 0 := by
  induction w generalizing a with
  | nil => exact h
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      exact ih hw' (rstep_neg hb h)

/-- **Cleanliness is implied by a nonnegative final value.** -/
theorem rrun_nonneg_of_nonneg {w v : List RB} (hv : Digs v) {a : ℤ}
    (h : 0 ≤ rrun (w ++ v) a) : 0 ≤ rrun w a := by
  by_contra hc
  push_neg at hc
  rw [rrun_append] at h
  exact absurd h (by simpa using (rrun_neg hv hc).not_ge)

/-! ## The transducer -/

/-- The letter the *next* overflow will deposit for the digit `b`: a bit block
always deposits `Y`, while the pop `X` deposits `V` or `X` according to the
parity of the counter it pops (the matched bit). -/
def qout (b : RB) (a : ℤ) : RB :=
  match b with
  | .Y => .Y
  | .V => .Y
  | .X => if a % 2 = 1 then .V else .X
  | _ => b

theorem qout_dig {b : RB} (hb : Dig b) (a : ℤ) : Dig (qout b a) := by
  rcases hb with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases h : a % 2 = 1 <;> simp [qout, h, Dig]

/-- The second counter after running the word `w` from first counter `a` and
second counter `c`: every letter acts on `a` by `rstep`, and its transduced
letter acts on `c`. -/
def trun : List RB → ℤ → ℤ → ℤ
  | [], _, c => c
  | b :: w, a, c => trun w (rstep b a) (rstep (qout b a) c)

@[simp] theorem trun_nil (a c : ℤ) : trun [] a c = c := rfl
@[simp] theorem trun_cons (b : RB) (w : List RB) (a c : ℤ) :
    trun (b :: w) a c = trun w (rstep b a) (rstep (qout b a) c) := rfl

theorem trun_append (w v : List RB) (a c : ℤ) :
    trun (w ++ v) a c = trun v (rrun w a) (trun w a c) := by
  induction w generalizing a c with
  | nil => rfl
  | cons b w ih => simp [ih]

/-! ## Dyck prefixes -/

/-- The balance of a word: opening letters `Y` count `+1`, the closing letters
`V` and `X` count `-1`. -/
def bal : List RB → ℤ
  | [] => 0
  | .Y :: w => bal w + 1
  | _ :: w => bal w - 1

@[simp] theorem bal_nil : bal [] = 0 := rfl
@[simp] theorem bal_Y (w : List RB) : bal (.Y :: w) = bal w + 1 := rfl
@[simp] theorem bal_V (w : List RB) : bal (.V :: w) = bal w - 1 := rfl
@[simp] theorem bal_X (w : List RB) : bal (.X :: w) = bal w - 1 := rfl

theorem bal_append (w v : List RB) : bal (w ++ v) = bal w + bal v := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [bal, ih] <;> ring

/-- A *Dyck prefix*: no closing letter is unmatched. -/
def DyckPre (w : List RB) : Prop := ∀ p, p <+: w → 0 ≤ bal p

theorem DyckPre.nil : DyckPre [] := by
  intro p hp
  obtain rfl := List.prefix_nil.mp hp
  simp

theorem DyckPre.prefix {w p : List RB} (h : DyckPre w) (hp : p <+: w) : DyckPre p :=
  fun q hq => h q (hq.trans hp)

theorem DyckPre.bal_nonneg {w : List RB} (h : DyckPre w) : 0 ≤ bal w := h w (List.prefix_refl w)

/-- A prefix of a concatenation either sits inside the left factor or extends it. -/
theorem prefix_append_cases {p w v : List RB} (h : p <+: w ++ v) :
    p <+: w ∨ ∃ q, p = w ++ q ∧ q <+: v := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append w v) with h1 | h2
  · exact Or.inl h1
  · obtain ⟨q, rfl⟩ := h2
    refine Or.inr ⟨q, rfl, ?_⟩
    obtain ⟨r, hr⟩ := h
    exact ⟨r, by simpa [List.append_assoc] using hr⟩

theorem prefix_singleton_cases {q : List RB} {b : RB} (h : q <+: [b]) : q = [] ∨ q = [b] := by
  cases q with
  | nil => exact Or.inl rfl
  | cons c t =>
      obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp h
      obtain rfl := List.prefix_nil.mp ht
      exact Or.inr rfl

theorem DyckPre.append {w v : List RB} (hw : DyckPre w) (hv : DyckPre v) : DyckPre (w ++ v) := by
  intro p hp
  rcases prefix_append_cases hp with h | ⟨q, rfl, hq⟩
  · exact hw p h
  · rw [bal_append]
    have h1 := hw.bal_nonneg
    have h2 := hv q hq
    omega

theorem DyckPre.cons_Y {w : List RB} (h : DyckPre w) : DyckPre (.Y :: w) := by
  intro p hp
  cases p with
  | nil => simp
  | cons b t =>
      obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp hp
      have := h t ht
      simp only [bal_Y]
      omega

/-- A balanced word (a *forest*). -/
def Bal (w : List RB) : Prop := DyckPre w ∧ bal w = 0

/-- The word contains a closing letter. -/
def HasCl (w : List RB) : Prop := ∃ b ∈ w, b = RB.V ∨ b = RB.X

theorem eq_replicate_Y {w : List RB} (hw : Digs w) (h : ¬ HasCl w) :
    w = List.replicate w.length RB.Y := by
  induction w with
  | nil => simp
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      have hbY : b = RB.Y := by
        rcases hb with rfl | rfl | rfl
        · rfl
        · exact absurd ⟨RB.V, by simp, Or.inl rfl⟩ h
        · exact absurd ⟨RB.X, by simp, Or.inr rfl⟩ h
      subst hbY
      have h' : ¬ HasCl w := by
        rintro ⟨c, hc, hcl⟩
        exact h ⟨c, by simp [hc], hcl⟩
      rw [List.length_cons, List.replicate_succ]
      exact congrArg _ (ih hw' h')

theorem bal_replicate_Y (n : ℕ) : bal (List.replicate n RB.Y) = (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, bal_Y, ih]; push_cast; ring

/-- A nonempty balanced word contains a closing letter. -/
theorem HasCl.of_bal {w : List RB} (hw : Digs w) (h : Bal w) (hne : w ≠ []) : HasCl w := by
  by_contra hc
  have hrep := eq_replicate_Y hw hc
  have hlen : 0 < w.length := List.length_pos_iff.mpr hne
  have : bal w = (w.length : ℤ) := by rw [hrep, bal_replicate_Y]; simp
  rw [h.2] at this
  omega

/-- A closing letter in front of a balanced word, under an opening letter, is
again a Dyck prefix. -/
theorem dyckPre_wrap {e : List RB} {cl : RB} (he : Bal e) (hcl : cl = RB.V ∨ cl = RB.X) :
    DyckPre (RB.Y :: (e ++ [cl])) := by
  intro r hr
  cases r with
  | nil => simp
  | cons b t =>
      obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp hr
      have hbt : -1 ≤ bal t := by
        rcases prefix_append_cases ht with h | ⟨q, rfl, hq⟩
        · have := he.1 t h
          omega
        · rcases prefix_singleton_cases hq with rfl | rfl
          · have := he.2
            simp
            omega
          · have := he.2
            rw [bal_append, this]
            rcases hcl with rfl | rfl <;> simp
      simp only [bal_Y]
      omega

/-- **Splitting a Dyck prefix at its last unmatched opening letter.** -/
private theorem dyck_split_aux : ∀ (n : ℕ) (p : List RB), p.length ≤ n → Digs p → DyckPre p →
    1 ≤ bal p → ∃ q e, p = q ++ RB.Y :: e ∧ DyckPre q ∧ Bal e := by
  intro n
  induction n with
  | zero =>
      intro p hp _ _ hb
      obtain rfl : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hp)
      simp at hb
  | succ n ih =>
      intro p hlen hdigs hd hb
      rcases List.eq_nil_or_concat p with rfl | ⟨p', b, hcat⟩
      · simp at hb
      · rw [List.concat_eq_append] at hcat
        subst hcat
        have hdp' : DyckPre p' := hd.prefix (List.prefix_append _ _)
        have hdigs' : Digs p' := (hdigs.of_append).1
        have hlen' : p'.length ≤ n := by
          have : (p' ++ [b]).length = p'.length + 1 := by simp
          omega
        have hbb : Dig b := (hdigs.of_append).2 b (by simp)
        rcases hbb with rfl | rfl | rfl
        · -- the last letter is an opening `Y`
          exact ⟨p', [], rfl, hdp', DyckPre.nil, rfl⟩
        · -- the last letter closes
          have hb' : 2 ≤ bal p' := by
            rw [bal_append] at hb
            simp at hb
            omega
          obtain ⟨q, e, rfl, hdq, hbe⟩ := ih p' hlen' hdigs' hdp' (by omega)
          have hdigsq : Digs q := (hdigs'.of_append).1
          have hdigse : Digs e := ((hdigs'.of_append).2.of_cons).2
          have hbq : 1 ≤ bal q := by
            rw [bal_append, bal_Y, hbe.2] at hb'
            omega
          have hlenq : q.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          obtain ⟨q', e', hqe, hdq', hbe'⟩ := ih q hlenq hdigsq hdq hbq
          refine ⟨q', e' ++ RB.Y :: (e ++ [RB.V]), ?_, hdq', ?_, ?_⟩
          · rw [hqe]
            simp
          · exact hbe'.1.append (dyckPre_wrap hbe (Or.inl rfl))
          · rw [bal_append, hbe'.2, bal_Y, bal_append, hbe.2]
            simp
        · have hb' : 2 ≤ bal p' := by
            rw [bal_append] at hb
            simp at hb
            omega
          obtain ⟨q, e, rfl, hdq, hbe⟩ := ih p' hlen' hdigs' hdp' (by omega)
          have hdigsq : Digs q := (hdigs'.of_append).1
          have hdigse : Digs e := ((hdigs'.of_append).2.of_cons).2
          have hbq : 1 ≤ bal q := by
            rw [bal_append, bal_Y, hbe.2] at hb'
            omega
          have hlenq : q.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          obtain ⟨q', e', hqe, hdq', hbe'⟩ := ih q hlenq hdigsq hdq hbq
          refine ⟨q', e' ++ RB.Y :: (e ++ [RB.X]), ?_, hdq', ?_, ?_⟩
          · rw [hqe]
            simp
          · exact hbe'.1.append (dyckPre_wrap hbe (Or.inr rfl))
          · rw [bal_append, hbe'.2, bal_Y, bal_append, hbe.2]
            simp

theorem dyck_split {p : List RB} (hp : Digs p) (hd : DyckPre p) (hb : 1 ≤ bal p) :
    ∃ q e, p = q ++ RB.Y :: e ∧ DyckPre q ∧ Bal e :=
  dyck_split_aux p.length p (le_refl _) hp hd hb

/-! ## The matched-group expansion lemma -/

private theorem trun_bounds : ∀ (n : ℕ) (w : List RB), w.length ≤ n → Digs w → DyckPre w →
    ∀ a c : ℤ, 0 ≤ c → c ≤ trun w a c ∧ (HasCl w → 4 * c + 2 ≤ trun w a c) := by
  intro n
  induction n with
  | zero =>
      intro w hlen _ _ a c hc
      obtain rfl : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exact ⟨le_refl _, by rintro ⟨b, hb, _⟩; simp at hb⟩
  | succ n ih =>
      intro w hlen hdigs hd a c hc
      rcases List.eq_nil_or_concat w with rfl | ⟨p, b, hcat⟩
      · exact ⟨le_refl _, by rintro ⟨b, hb, _⟩; simp at hb⟩
      · rw [List.concat_eq_append] at hcat
        subst hcat
        have hdp : DyckPre p := hd.prefix (List.prefix_append _ _)
        have hdigsp : Digs p := (hdigs.of_append).1
        have hlenp : p.length ≤ n := by
          have : (p ++ [b]).length = p.length + 1 := by simp
          omega
        have hbb : Dig b := (hdigs.of_append).2 b (by simp)
        have hsplit : trun (p ++ [b]) a c = rstep (qout b (rrun p a)) (trun p a c) := by
          rw [trun_append]
          simp
        rcases hbb with rfl | rfl | rfl
        · -- an opening `Y`
          obtain ⟨h1, h2⟩ := ih p hlenp hdigsp hdp a c hc
          have hcl : HasCl (p ++ [RB.Y]) → HasCl p := by
            rintro ⟨x, hx, hxc⟩
            rcases List.mem_append.mp hx with h | h
            · exact ⟨x, h, hxc⟩
            · simp at h
              subst h
              rcases hxc with h | h <;> simp at h
          rw [hsplit]
          simp only [qout, rstep_Y]
          exact ⟨by omega, fun hh => by have := h2 (hcl hh); omega⟩
        · -- a closing `V`
          have hbalp : 1 ≤ bal p := by
            have h0 := hd.bal_nonneg
            rw [bal_append] at h0
            simp at h0
            omega
          obtain ⟨q, e, rfl, hdq, hbe⟩ := dyck_split hdigsp hdp hbalp
          have hdigsq : Digs q := (hdigsp.of_append).1
          have hdigse : Digs e := ((hdigsp.of_append).2.of_cons).2
          have hlenq : q.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          have hlene : e.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          obtain ⟨hq1, _⟩ := ih q hlenq hdigsq hdq a c hc
          set cq := trun q a c with hcq
          set aq := rrun q a with haq
          have hc1 : 0 ≤ 2 * cq + 1 := by omega
          obtain ⟨he1, he2⟩ := ih e hlene hdigse hbe.1 (2 * aq + 1) (2 * cq + 1) hc1
          have hrun : trun ((q ++ RB.Y :: e) ++ [RB.V]) a c =
              2 * trun e (2 * aq + 1) (2 * cq + 1) + 1 := by
            rw [trun_append, trun_append]
            simp only [trun_cons, trun_nil, rrun_append, rrun_cons, qout, rstep_Y,
              rstep_V, ← hcq, ← haq]
          rw [hrun]
          exact ⟨by omega, fun _ => by omega⟩
        · -- a closing `X`
          have hbalp : 1 ≤ bal p := by
            have h0 := hd.bal_nonneg
            rw [bal_append] at h0
            simp at h0
            omega
          obtain ⟨q, e, rfl, hdq, hbe⟩ := dyck_split hdigsp hdp hbalp
          have hdigsq : Digs q := (hdigsp.of_append).1
          have hdigse : Digs e := ((hdigsp.of_append).2.of_cons).2
          have hlenq : q.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          have hlene : e.length ≤ n := by
            have h1 : (q ++ RB.Y :: e).length = q.length + e.length + 1 := by simp; omega
            omega
          obtain ⟨hq1, _⟩ := ih q hlenq hdigsq hdq a c hc
          set cq := trun q a c with hcq
          set aq := rrun q a with haq
          have hc1 : 0 ≤ 2 * cq + 1 := by omega
          obtain ⟨he1, he2⟩ := ih e hlene hdigse hbe.1 (2 * aq + 1) (2 * cq + 1) hc1
          set a2 := rrun e (2 * aq + 1) with ha2
          set c2 := trun e (2 * aq + 1) (2 * cq + 1) with hc2
          have hrun : trun ((q ++ RB.Y :: e) ++ [RB.X]) a c = rstep (qout RB.X a2) c2 := by
            rw [trun_append, trun_append]
            simp only [trun_cons, trun_nil, rrun_append, rrun_cons, qout, rstep_Y,
              ← hcq, ← haq, ← ha2, ← hc2]
          rw [hrun]
          by_cases hodd : a2 % 2 = 1
          · simp only [qout, hodd, if_pos, rstep_V]
            refine ⟨by omega, fun _ => by omega⟩
          · -- the interior cannot be empty: the opening `Y` made the counter odd
            have hne : e ≠ [] := by
              rintro rfl
              simp only [ha2, rrun_nil] at hodd
              omega
            have hcle : HasCl e := HasCl.of_bal hdigse hbe hne
            have hbig := he2 hcle
            simp only [qout, hodd, if_false, rstep_X]
            refine ⟨by omega, fun _ => by omega⟩

/-- **A matched group multiplies the second counter by four.**  A Dyck prefix
that contains a closing letter — i.e. a completed pair — takes any nonnegative
second counter `c` to at least `4c+2`. -/
theorem trun_ge_of_hasCl {w : List RB} (hw : Digs w) (hd : DyckPre w) (hcl : HasCl w)
    {a c : ℤ} (hc : 0 ≤ c) : 4 * c + 2 ≤ trun w a c :=
  (trun_bounds w.length w (le_refl _) hw hd a c hc).2 hcl

/-- A word of `Y`s has value `2^n - 1`. -/
theorem rrun_replicate_Y (n : ℕ) (a : ℤ) :
    rrun (List.replicate n RB.Y) a = 2 ^ n * (a + 1) - 1 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, rrun_cons, ih, rstep_Y]
      ring

/-- **The exceptional low-counter lemma.**  A nonempty clean Dyck prefix whose
own reset value is `0` transduces to a word of value at least `2`. -/
theorem trun_ge_two {w : List RB} (hw : Digs w) (hd : DyckPre w) (hne : w ≠ [])
    (h0 : rrun w 0 = 0) : 2 ≤ trun w 0 0 := by
  have hcl : HasCl w := by
    by_contra hc
    have hrep := eq_replicate_Y hw hc
    have hlen : 0 < w.length := List.length_pos_iff.mpr hne
    rw [hrep, rrun_replicate_Y] at h0
    have h2 : (2 : ℤ) ≤ 2 ^ w.length := by
      calc (2:ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w.length := by
            exact pow_le_pow_right₀ (by norm_num) hlen
    omega
  have := trun_ge_of_hasCl hw hd hcl (a := 0) (c := 0) (le_refl 0)
  omega

/-! ## Counting `F`/`G` blocks -/

/-- The number of `F`/`G` blocks in a right word.  Only the pop rule of the
block simulator creates such blocks (used to transfer runs to the sibling). -/
def fgc : List RB → ℕ
  | [] => 0
  | b :: w => (if b = .F ∨ b = .G then 1 else 0) + fgc w

@[simp] theorem fgc_nil : fgc [] = 0 := rfl

@[simp] theorem fgc_cons (b : RB) (w : List RB) :
    fgc (b :: w) = (if b = .F ∨ b = .G then 1 else 0) + fgc w := rfl

theorem fgc_append (w v : List RB) : fgc (w ++ v) = fgc w + fgc v := by
  induction w with
  | nil => simp
  | cons b w ih => simp [ih]; omega

theorem fgc_replicate (n : ℕ) (b : RB) (hb : b ≠ .F ∧ b ≠ .G) :
    fgc (List.replicate n b) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, hb.1, hb.2]

/-- A digit word has no `F`/`G` block. -/
theorem fgc_digs {w : List RB} (hw : Digs w) : fgc w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      obtain ⟨hb, hw'⟩ := hw.of_cons
      rcases hb with rfl | rfl | rfl <;> simp [ih hw']

end BB25.Prefix
