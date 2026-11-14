import RequestProject.MixedLeft

/-!
# The right counter and the exact reset-to-reset return
-/

namespace TM25

open LB RB Hd

/-! ## The right counter as one integer -/

/-- The right word enumerated by an integer `M ≥ 2`: the binary digits of `M`
below its two leading bits (least significant first, `C = 0`, `C1 = 1`), followed
by the tail `P Q` if the second leading bit of `M` is `1`. -/
def encR (M : Nat) : List RB :=
  if M < 4 then (if M = 3 then [P, Q] else [])
  else (if M % 2 = 0 then C else C1) :: encR (M / 2)
decreasing_by omega

theorem encR_two : encR 2 = [] := by rw [encR]; simp

theorem encR_three : encR 3 = [P, Q] := by rw [encR]; simp

theorem encR_ge {M : Nat} (h : 4 ≤ M) :
    encR M = (if M % 2 = 0 then C else C1) :: encR (M / 2) := by
  rw [encR, if_neg (by omega)]

/-- **Right excursion.**  A complete right excursion increments the right
counter by one; it never touches the left word. -/
theorem right_exc : ∀ M, 2 ≤ M → ∀ m : List LB,
    Reach ⟨m, gt, encR M⟩ ⟨m, lt, encR (M + 1)⟩ := by
  intro M
  induction M using Nat.strongRecOn with
  | _ M ih =>
    intro hM m
    rcases (show M = 2 ∨ M = 3 ∨ 4 ≤ M by omega) with rfl | rfl | h4
    · rw [encR_two, encR_three]; astep1; exact Reach.refl _
    · rw [encR_three, encR_ge (by decide : 4 ≤ 3 + 1)]
      simp only [show (3 + 1) / 2 = 2 from rfl, show (3 + 1) % 2 = 0 from rfl, if_true, encR_two]
      astep1; astep1; exact Reach.refl _
    · rw [encR_ge h4, encR_ge (by omega : 4 ≤ M + 1)]
      rcases Nat.mod_two_eq_zero_or_one M with he | ho
      · have h1 : (M + 1) % 2 = 1 := by omega
        have h2 : (M + 1) / 2 = M / 2 := by omega
        rw [if_pos he, if_neg (by omega), h2]
        astep1; exact Reach.refl _
      · have h1 : (M + 1) % 2 = 0 := by omega
        have h2 : (M + 1) / 2 = M / 2 + 1 := by omega
        rw [if_neg (by omega), if_pos h1, h2]
        astep1
        refine (ih (M / 2) (by omega) (by omega) (D :: m)).trans ?_
        astep1; exact Reach.refl _

/-- Complemented binary digits of `d`, least significant first
(`C1` for a `0` bit of `d`, `C` for a `1` bit). -/
def compbits : Nat → Nat → List RB
  | 0, _ => []
  | N + 1, d => (if d % 2 = 0 then C1 else C) :: compbits N (d / 2)

theorem encR_comp : ∀ N d, d < 2 ^ N → encR (4 * 2 ^ N - 1 - d) = compbits N d ++ [P, Q] := by
  intro N
  induction N with
  | zero => intro d hd; simp at hd; subst hd; simp [compbits, encR_three]
  | succ N ih =>
    intro d hd
    have hp : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
    rw [encR_ge (by omega), compbits]
    have hq : (4 * 2 ^ (N + 1) - 1 - d) / 2 = 4 * 2 ^ N - 1 - d / 2 := by omega
    rw [hq, ih (d / 2) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one d with he | ho
    · rw [if_neg (by omega), if_pos he]; rfl
    · rw [if_pos (by omega), if_neg (by omega)]; rfl

/-! ## Alternating left and right excursions -/

/-- After `Kcap m` pairs of excursions the left word saturates and emits its
image in front of the right counter. -/
theorem pair_iter : ∀ k (m : List LB) M, Kcap m = k → 2 ≤ M →
    Reach ⟨m, lt, encR M⟩ ⟨[], lt, Phi m ++ encR (M + k)⟩ := by
  intro k
  induction k with
  | zero => intro m M hk _; simpa using left_exc_zero (encR M) hk
  | succ k ih =>
    intro m M hk hM
    obtain ⟨m', h1, h2, h3⟩ := left_exc_pos (encR M) (l := m) (by omega)
    refine h3.trans ((right_exc M hM m').trans ?_)
    have := ih m' (M + 1) (by omega) (by omega)
    rw [h2] at this
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- The right word `C G G` left by the bottom of the cascade: six pairs of
excursions normalise it to `C C C = encR 16`, then `pair_iter` finishes. -/
theorem cgg_phase (m : List LB) (h6 : 6 ≤ Kcap m) :
    Reach ⟨m, lt, [C, G, G]⟩ ⟨[], lt, Phi m ++ encR (Kcap m + 10)⟩ := by
  obtain ⟨m1, k1, p1, r1⟩ := left_exc_pos [C, G, G] (l := m) (by omega)
  obtain ⟨m2, k2, p2, r2⟩ := left_exc_pos [C1, G, G] (l := m1) (by omega)
  obtain ⟨m3, k3, p3, r3⟩ := left_exc_pos [C, C, G] (l := m2) (by omega)
  obtain ⟨m4, k4, p4, r4⟩ := left_exc_pos [C1, C, G] (l := m3) (by omega)
  obtain ⟨m5, k5, p5, r5⟩ := left_exc_pos [C, C1, G] (l := m4) (by omega)
  obtain ⟨m6, k6, p6, r6⟩ := left_exc_pos [C1, C1, G] (l := m5) (by omega)
  have h16 : encR 16 = [C, C, C] := by
    rw [encR_ge (by decide), encR_ge (by decide), encR_ge (by decide), encR_two]; rfl
  have hfin := pair_iter (Kcap m6) m6 16 rfl (by decide)
  rw [h16] at hfin
  refine r1.trans ?_; astep1
  refine r2.trans ?_; astep1; astep1; astep1
  refine r3.trans ?_; astep1
  refine r4.trans ?_; astep1; astep1; astep1
  refine r5.trans ?_; astep1
  refine r6.trans ?_; astep1; astep1; astep1; astep1; astep1
  refine hfin.trans ?_
  rw [p6, p5, p4, p3, p2, p1, show 16 + Kcap m6 = Kcap m + 10 by omega]
  exact Reach.refl _

/-! ## The exact reset return -/

/-- The reset configuration with body `w`: empty left word, head `<`, right
word `w P Q`. -/
def resetCfg (w : List RB) : ACfg := ⟨[], lt, w ++ [P, Q]⟩

/-- **Exact reset return.**  If the wide cascade through `u` is valid and leaves
capacity at least `7`, and `cCap 0 u + 10 + d = 4 * 2^N` with `d < 2^N`, then
the reset with body `u C1` leads (in a positive, finite, halt-free block run)
to the reset with body `cEmit 0 u ++ compbits N d`. -/
theorem reset_return (u : List RB) (hok : cOK 0 u = true) (h7 : 7 ≤ cCap 0 u) (N d : Nat)
    (hd : d < 2 ^ N) (hNd : cCap 0 u + 10 + d = 4 * 2 ^ N) :
    ∃ t, 0 < t ∧ arun t (resetCfg (u ++ [C1])) = some (resetCfg (cEmit 0 u ++ compbits N d)) := by
  refine Reach.step_pos (b := ⟨[], wgt, u ++ [C1] ++ [P, Q]⟩) rfl ?_
  obtain ⟨lu, hk, hp, hr⟩ := cascade u [] [C1, P, Q] (by simpa [Kcap] using hok)
  simp only [Kcap, Phi, List.nil_append] at hk hp
  have hr' : Reach ⟨[], wgt, u ++ [C1] ++ [P, Q]⟩ ⟨lu, wgt, [C1, P, Q]⟩ := by simpa using hr
  refine hr'.trans ?_
  obtain ⟨m, km, pm, rm⟩ := left_exc_pos [P, V, P, Q] (l := lu) (by omega)
  astep1
  refine rm.trans ?_
  astep1; astep1; astep1; astep1; astep1; astep1; astep1; astep1; astep1
  refine (cgg_phase m (by omega)).trans ?_
  have hM : Kcap m + 10 = 4 * 2 ^ N - 1 - d := by omega
  rw [hM, encR_comp N d hd, pm, hp]
  simp only [resetCfg, List.append_assoc]
  exact Reach.refl _

end TM25
