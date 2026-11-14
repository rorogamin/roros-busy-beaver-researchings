import RequestProject.Blocks

/-!
# The whole mixed left word as one counter

This file formalizes the operational part of the "mixed counter" non-halting
argument: the capacity `Kcap` of an arbitrary left word (including buried `D`
blocks), its saturation image `Phi`, the wide cascade, the right counter, and
the exact reset-to-reset return.
-/

namespace TM25

open LB RB Hd

/-! ## Reachability -/

/-- `b` is reachable from `a` in the block system. -/
def Reach (a b : ACfg) : Prop := ∃ t, arun t a = some b

theorem Reach.refl (a : ACfg) : Reach a a := ⟨0, rfl⟩

theorem Reach.trans {a b c : ACfg} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨m, hm⟩ := h₁; obtain ⟨n, hn⟩ := h₂; exact ⟨m + n, arun_comp hm hn⟩

theorem Reach.step {a b c : ACfg} (h : astep a = AStep.next b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h₂
  exact ⟨n + 1, by simp only [arun, h]; exact hn⟩

/-- One step followed by a run: a run of positive length. -/
theorem Reach.step_pos {a b c : ACfg} (h : astep a = AStep.next b) (h₂ : Reach b c) :
    ∃ t, 0 < t ∧ arun t a = some c := by
  obtain ⟨n, hn⟩ := h₂
  exact ⟨n + 1, by omega, by simp only [arun, h]; exact hn⟩

/-- Take one block step (discharged by unfolding `astep`). -/
macro "astep1" : tactic => `(tactic| refine Reach.step (by first | rfl | (simp only [astep]; done) | (simp only [astep]; rfl) | (simp [astep]; rfl)) ?_)

/-! ## Capacity and saturation image of a mixed left word -/

/-- The exact remaining capacity of a left word (nearest-head block first). -/
def Kcap : List LB → Nat
  | [] => 0
  | U :: l => 2 * Kcap l + 1
  | W :: l => 2 * Kcap l
  | D :: l => Kcap l / 2

/-- The saturation image: the right word left behind when the left word
overflows.  (Nearest-head first.) -/
def Phi : List LB → List RB
  | [] => []
  | U :: l => Phi l ++ [V]
  | W :: l => Phi l ++ [V]
  | D :: l => Phi l ++ [if Kcap l % 2 = 0 then C else C1]

/-- **Mixed-left lemma.**  A complete left excursion exists iff the capacity is
positive; it decreases the capacity by one and preserves the saturation image.
When the capacity is zero, the excursion reaches the left end and emits the
saturation image. -/
theorem left_excursion : ∀ (n : Nat) (l : List LB), l.length = n → ∀ rs : List RB,
    (0 < Kcap l → ∃ l', l'.length = l.length ∧ Kcap l' + 1 = Kcap l ∧ Phi l' = Phi l ∧
        Reach ⟨l, lt, rs⟩ ⟨l', gt, rs⟩) ∧
    (Kcap l = 0 → Reach ⟨l, lt, rs⟩ ⟨[], lt, Phi l ++ rs⟩) := by
  intro n
  induction n with
  | zero =>
    intro l hl rs
    rw [List.length_eq_zero_iff] at hl
    subst hl
    refine ⟨fun h => by simp [Kcap] at h, fun _ => ?_⟩
    simpa [Phi] using Reach.refl _
  | succ n ih =>
    intro l hl rs
    obtain ⟨b, t, rfl⟩ : ∃ b t, l = b :: t := by
      cases l with
      | nil => simp at hl
      | cons b t => exact ⟨b, t, rfl⟩
    have ht : t.length = n := by simpa using hl
    cases b with
    | U =>
      refine ⟨fun _ => ⟨W :: t, rfl, by simp [Kcap], by simp [Phi], ?_⟩, fun h => by
        simp [Kcap] at h⟩
      astep1; exact Reach.refl _
    | W =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hk : 0 < Kcap t := by simp [Kcap] at h; omega
        obtain ⟨t', htl, hk', hp', hr⟩ := (ih t ht (V :: rs)).1 hk
        refine ⟨U :: t', by simp [htl], by simp [Kcap]; omega, by simp [Phi, hp'], ?_⟩
        astep1
        exact hr.trans (by astep1; exact Reach.refl _)
      · have hk : Kcap t = 0 := by simp [Kcap] at h; omega
        have hr := (ih t ht (V :: rs)).2 hk
        astep1
        simpa [Phi] using hr
    | D =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hk : 2 ≤ Kcap t := by simp [Kcap] at h; omega
        obtain ⟨t1, ht1, hk1, hp1, hr1⟩ := (ih t ht (C :: rs)).1 (by omega)
        obtain ⟨t2, ht2, hk2, hp2, hr2⟩ := (ih t1 (by omega) (C1 :: rs)).1 (by omega)
        refine ⟨D :: t2, by simp [ht2, ht1], ?_, ?_, ?_⟩
        · simp [Kcap]; omega
        · have hpar : (Kcap t2 % 2 = 0) ↔ (Kcap t % 2 = 0) := by omega
          simp only [Phi, hp2, hp1]
          by_cases hp : Kcap t % 2 = 0
          · simp [hp, hpar.2 hp]
          · simp [hp, show ¬ Kcap t2 % 2 = 0 from fun h => hp (hpar.1 h)]
        · astep1
          refine hr1.trans ?_
          astep1
          refine hr2.trans ?_
          astep1; exact Reach.refl _
      · have hk : Kcap t = 0 ∨ Kcap t = 1 := by simp [Kcap] at h; omega
        rcases hk with hk | hk
        · have hr := (ih t ht (C :: rs)).2 hk
          astep1
          simpa [Phi, hk] using hr
        · obtain ⟨t1, ht1, hk1, hp1, hr1⟩ := (ih t ht (C :: rs)).1 (by omega)
          have hr2 := (ih t1 (by omega) (C1 :: rs)).2 (by omega)
          astep1
          refine hr1.trans ?_
          astep1
          simpa [Phi, hk, hp1] using hr2

theorem left_exc_pos {l : List LB} (rs : List RB) (h : 0 < Kcap l) :
    ∃ l', Kcap l' + 1 = Kcap l ∧ Phi l' = Phi l ∧ Reach ⟨l, lt, rs⟩ ⟨l', gt, rs⟩ := by
  obtain ⟨l', -, h1, h2, h3⟩ := (left_excursion l.length l rfl rs).1 h
  exact ⟨l', h1, h2, h3⟩

theorem left_exc_zero {l : List LB} (rs : List RB) (h : Kcap l = 0) :
    Reach ⟨l, lt, rs⟩ ⟨[], lt, Phi l ++ rs⟩ :=
  (left_excursion l.length l rfl rs).2 h

/-! ## The wide cascade -/

/-- Validity of a wide cascade started with left capacity `E`. -/
def cOK : Nat → List RB → Bool
  | _, [] => true
  | E, V :: w => cOK (2 * E + 1) w
  | E, C1 :: w => decide (1 ≤ E) && cOK (2 * E - 1) w
  | E, C :: w => decide (6 ≤ E) && cOK ((E - 6) / 2) w
  | _, _ :: _ => false

/-- The left capacity after the wide cascade. -/
def cCap : Nat → List RB → Nat
  | E, [] => E
  | E, V :: w => cCap (2 * E + 1) w
  | E, C1 :: w => cCap (2 * E - 1) w
  | E, C :: w => cCap ((E - 6) / 2) w
  | E, _ :: _ => E

/-- The saturation image emitted by the wide cascade. -/
def cEmit : Nat → List RB → List RB
  | _, [] => []
  | E, V :: w => V :: cEmit (2 * E + 1) w
  | E, C1 :: w => V :: cEmit (2 * E - 1) w
  | E, C :: w => (if E % 2 = 0 then C else C1) :: cEmit ((E - 6) / 2) w
  | _, _ :: _ => []

/-- **Cascade lemma.** A valid wide cascade through the reset word `w` is a
finite safe computation, whose final left word has the predicted capacity and
saturation image. -/
theorem cascade : ∀ (w : List RB) (l : List LB) (r : List RB), cOK (Kcap l) w = true →
    ∃ l', Kcap l' = cCap (Kcap l) w ∧ Phi l' = Phi l ++ cEmit (Kcap l) w ∧
      Reach ⟨l, wgt, w ++ r⟩ ⟨l', wgt, r⟩ := by
  intro w
  induction w with
  | nil => intro l r _; exact ⟨l, rfl, by simp [cEmit], Reach.refl _⟩
  | cons c w ih =>
    intro l r hok
    cases c with
    | V =>
      simp only [cOK] at hok
      obtain ⟨l', h1, h2, h3⟩ := ih (U :: l) r (by simpa [Kcap] using hok)
      refine ⟨l', by simpa [cCap, Kcap] using h1, by simp [cEmit, h2, Phi, Kcap], ?_⟩
      astep1; exact h3
    | C1 =>
      simp only [cOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hE, hok⟩ := hok
      obtain ⟨m, hm1, hm2, hm3⟩ := left_exc_pos (P :: V :: w ++ r) (l := l) (by omega)
      have hK : Kcap (U :: m) = 2 * Kcap l - 1 := by simp [Kcap]; omega
      obtain ⟨l', h1, h2, h3⟩ := ih (U :: m) r (by rw [hK]; exact hok)
      refine ⟨l', by rw [h1, hK]; rfl, by rw [h2]; simp [cEmit, Phi, hm2, hK], ?_⟩
      astep1
      refine hm3.trans ?_
      astep1; astep1; exact h3
    | C =>
      simp only [cOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hE, hok⟩ := hok
      obtain ⟨l1, k1, p1, r1⟩ := left_exc_pos (C :: S :: w ++ r) (l := l) (by omega)
      obtain ⟨l2, k2, p2, r2⟩ := left_exc_pos (C1 :: S :: w ++ r) (l := l1) (by omega)
      obtain ⟨l3, k3, p3, r3⟩ := left_exc_pos (C :: Q :: w ++ r) (l := l2) (by omega)
      obtain ⟨l4, k4, p4, r4⟩ := left_exc_pos (C1 :: Q :: w ++ r) (l := l3) (by omega)
      obtain ⟨l5, k5, p5, r5⟩ := left_exc_pos (C :: P :: w ++ r) (l := l4) (by omega)
      obtain ⟨l6, k6, p6, r6⟩ := left_exc_pos (C1 :: P :: w ++ r) (l := l5) (by omega)
      have hK : Kcap (D :: l6) = (Kcap l - 6) / 2 := by simp [Kcap]; congr 1; omega
      obtain ⟨l', h1, h2, h3⟩ := ih (D :: l6) r (by rw [hK]; exact hok)
      refine ⟨l', by rw [h1, hK]; rfl, ?_, ?_⟩
      · rw [h2, hK]
        have hpar : (Kcap l6 % 2 = 0) ↔ (Kcap l % 2 = 0) := by omega
        simp only [Phi, p6, p5, p4, p3, p2, p1, cEmit, List.append_assoc, List.cons_append,
          List.nil_append]
        by_cases hp : Kcap l % 2 = 0
        · simp [hp, hpar.2 hp]
        · simp [hp, show ¬ Kcap l6 % 2 = 0 from fun h => hp (hpar.1 h)]
      · astep1
        refine r1.trans ?_; astep1
        refine r2.trans ?_; astep1; astep1; astep1
        refine r3.trans ?_; astep1
        refine r4.trans ?_; astep1; astep1; astep1
        refine r5.trans ?_; astep1
        refine r6.trans ?_; astep1; astep1
        exact h3
    | G => simp [cOK] at hok
    | P => simp [cOK] at hok
    | S => simp [cOK] at hok
    | Q => simp [cOK] at hok

end TM25
