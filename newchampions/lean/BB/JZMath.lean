/-
  BB/JZMath.lean
  Pure arithmetic of the Jacobzheng f_{ω×2} engine: recurrences `h`, `hc`, `ho`, `hoc`,
  mod-3 invariants, and FGH lower bounds.
-/

import BB.TM
import BB.FGH

namespace BB

def h : Nat → Nat → Nat
  | 0, n => 4 * n + 7
  | m + 1, n => iter (h m) (n + 1) 3

def hc : Nat → Nat → Nat → Nat
  | _, 0, n => n
  | m, k + 1, n => hc (m + 1) k (h m n)

def ho : Nat → Nat → Nat
  | 0, n =>
    match n % 3 with
    | 0 => hc 0 (n / 3) 7 + 2 * (n / 3) + 3
    | 1 => n + 4
    | _ => hc 0 (n / 3) 7 + 2 * (n / 3 + 1) + 3
  | m + 1, n => iter (ho m) (n + 1) 6

def hoc : Nat → Nat → Nat → Nat
  | _, 0, n => n
  | m, k + 1, n => hoc (m + 1) k (ho m n)

theorem mod3_cases (x : Nat) :
    (∃ q, x = 3 * q) ∨ (∃ q, x = 3 * q + 1) ∨ (∃ q, x = 3 * q + 2) := by
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h
  · exact Or.inl ⟨x / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨x / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨x / 3, by omega⟩)

theorem ho0_mod0 (q : Nat) : ho 0 (3 * q) = hc 0 q 7 + 2 * q + 3 := by
  have hm : (3 * q) % 3 = 0 := by omega
  have hd : (3 * q) / 3 = q := by omega
  simp [ho, hm, hd]

theorem ho0_mod1 (q : Nat) : ho 0 (3 * q + 1) = 3 * q + 5 := by
  have hm : (3 * q + 1) % 3 = 1 := by omega
  simp [ho, hm]

theorem ho0_mod2 (q : Nat) : ho 0 (3 * q + 2) = hc 0 q 7 + 2 * (q + 1) + 3 := by
  have hm : (3 * q + 2) % 3 = 2 := by omega
  have hd : (3 * q + 2) / 3 = q := by omega
  simp [ho, hm, hd]

theorem h_ge_3x1 (m x : Nat) : 3 * x + 1 ≤ h m x := by
  induction m generalizing x with
  | zero => simp [h]; omega
  | succ m' ih =>
    have hstep : ∀ k, 3 * k + 1 ≤ iter (h m') k 3 := by
      intro k
      induction k with
      | zero => simp [iter]
      | succ p ihp =>
        rw [iter_succ]
        have := ih (iter (h m') p 3)
        omega
    have := hstep (x + 1)
    show 3 * x + 1 ≤ iter (h m') (x + 1) 3
    omega

theorem h_mono (m : Nat) {x y : Nat} (hxy : x ≤ y) : h m x ≤ h m y := by
  induction m generalizing x y with
  | zero => simp [h]; omega
  | succ m' _ =>
    exact iter_mono_steps (h m') (fun z => Nat.le_trans (by omega) (h_ge_3x1 m' z))
      (Nat.add_le_add_right hxy 1) 3

theorem h_mod3 (m x : Nat) : h m x % 3 = (x + 1) % 3 := by
  induction m generalizing x with
  | zero => simp [h]; omega
  | succ m' ih =>
    have hiter : ∀ k z, iter (h m') k z % 3 = (z + k) % 3 := by
      intro k z
      induction k with
      | zero => simp [iter]
      | succ p ihp => rw [iter_succ, ih]; omega
    show iter (h m') (x + 1) 3 % 3 = (x + 1) % 3
    rw [hiter]; omega

theorem hc_snoc (m k n : Nat) : hc m (k + 1) n = h (m + k) (hc m k n) := by
  induction k generalizing m n with
  | zero => simp [hc]
  | succ p ih =>
    have e1 : hc m (p + 1 + 1) n = hc (m + 1) (p + 1) (h m n) := rfl
    have e2 : hc m (p + 1) n = hc (m + 1) p (h m n) := rfl
    rw [e1, ih, e2, show m + 1 + p = m + (p + 1) by omega]

theorem hc_mod3 (m k n : Nat) : hc m k n % 3 = (n + k) % 3 := by
  induction k generalizing m n with
  | zero => simp [hc]
  | succ p ih => show hc (m + 1) p (h m n) % 3 = _; have := h_mod3 m n; rw [ih]; omega

theorem hc0_ge_3k (k : Nat) : 3 * k + 7 ≤ hc 0 k 7 := by
  induction k with
  | zero => simp [hc]
  | succ p ih =>
    rw [hc_snoc]
    have := h_ge_3x1 (0 + p) (hc 0 p 7)
    omega

theorem hc0_ge_15q (q : Nat) (hq : 1 ≤ q) : 15 * q + 15 ≤ hc 0 q 7 := by
  induction q with
  | zero => omega
  | succ p ih =>
    cases p with
    | zero => have : hc 0 (0 + 1) 7 = 35 := rfl
              omega
    | succ p' =>
      specialize ih (by omega)
      rw [hc_snoc]
      have := h_ge_3x1 (0 + (p' + 1)) (hc 0 (p' + 1) 7)
      omega

theorem hc0_mono {a b : Nat} (hab : a ≤ b) : hc 0 a 7 ≤ hc 0 b 7 := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step p _ ih =>
    rw [hc_snoc]
    exact Nat.le_trans ih (Nat.le_trans (by omega) (h_ge_3x1 _ _))

theorem ho_ge_add4 (m x : Nat) : x + 4 ≤ ho m x := by
  induction m generalizing x with
  | zero =>
    rcases mod3_cases x with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hb := hc0_ge_3k q
      rw [ho0_mod0]; omega
    · rw [ho0_mod1]; omega
    · have hb := hc0_ge_3k q
      rw [ho0_mod2]; omega
  | succ m' ih =>
    have hstep : ∀ k, k + 4 ≤ iter (ho m') k 6 := by
      intro k
      induction k with
      | zero => simp [iter]
      | succ p ihp =>
        rw [iter_succ]
        have := ih (iter (ho m') p 6)
        omega
    have := hstep (x + 1)
    show x + 4 ≤ iter (ho m') (x + 1) 6
    omega

theorem ho_succ_mono (m : Nat) {x y : Nat} (hxy : x ≤ y) : ho (m + 1) x ≤ ho (m + 1) y :=
  iter_mono_steps (ho m) (fun z => Nat.le_trans (by omega) (ho_ge_add4 m z))
    (Nat.add_le_add_right hxy 1) 6

theorem ho_mod3 (m x : Nat) : ho m x % 3 = (x + 1) % 3 := by
  induction m generalizing x with
  | zero =>
    rcases mod3_cases x with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [ho0_mod0, Nat.add_mod, Nat.add_mod (hc 0 q 7), hc_mod3]; omega
    · rw [ho0_mod1]; omega
    · rw [ho0_mod2, Nat.add_mod, Nat.add_mod (hc 0 q 7), hc_mod3]; omega
  | succ m' ih =>
    have hiter : ∀ k z, iter (ho m') k z % 3 = (z + k) % 3 := by
      intro k z
      induction k with
      | zero => simp [iter]
      | succ p ihp => rw [iter_succ, ih]; omega
    show iter (ho m') (x + 1) 6 % 3 = (x + 1) % 3
    rw [hiter]; omega

theorem hoc_snoc (m k n : Nat) : hoc m (k + 1) n = ho (m + k) (hoc m k n) := by
  induction k generalizing m n with
  | zero => simp [hoc]
  | succ p ih =>
    have e1 : hoc m (p + 1 + 1) n = hoc (m + 1) (p + 1) (ho m n) := rfl
    have e2 : hoc m (p + 1) n = hoc (m + 1) p (ho m n) := rfl
    rw [e1, ih, e2, show m + 1 + p = m + (p + 1) by omega]

theorem hoc_mod3 (m k n : Nat) : hoc m k n % 3 = (n + k) % 3 := by
  induction k generalizing m n with
  | zero => simp [hoc]
  | succ p ih => show hoc (m + 1) p (ho m n) % 3 = _; have := ho_mod3 m n; rw [ih]; omega

theorem hoc_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (m n : Nat) : hoc m k1 n ≤ hoc m k2 n := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step p _ ih =>
    rw [hoc_snoc]
    exact Nat.le_trans ih (Nat.le_trans (by omega) (ho_ge_add4 _ _))

theorem hoc_ge_add4 (m k n : Nat) : n + 4 * k ≤ hoc m k n := by
  induction k with
  | zero => simp [hoc]
  | succ p ih =>
    rw [hoc_snoc]
    have := ho_ge_add4 (m + p) (hoc m p n)
    omega

theorem iter_le_iter (f g : Nat → Nat) (hfg : ∀ z, f z ≤ g z)
    (hg_mono : ∀ a b, a ≤ b → g a ≤ g b) (k y : Nat) :
    iter f k y ≤ iter g k y := by
  induction k with
  | zero => exact Nat.le_refl y
  | succ p ih =>
    rw [iter_succ, iter_succ]
    exact Nat.le_trans (hfg _) (hg_mono _ _ ih)

theorem fFin_le_h (m x : Nat) : fFin m x ≤ h m (3 * x) := by
  induction m generalizing x with
  | zero => rw [show fFin 0 x = x + 1 from rfl]; simp [h]; omega
  | succ m' ih =>
    show iter (fFin m') x x ≤ iter (h m') (3 * x + 1) 3
    have hstep : ∀ z, fFin m' z ≤ h m' (h m' z) := fun z =>
      Nat.le_trans (ih z) (h_mono m' (Nat.le_trans (by omega) (h_ge_3x1 m' z)))
    have hmono2 : ∀ a b, a ≤ b → h m' (h m' a) ≤ h m' (h m' b) := fun a b hab =>
      h_mono m' (h_mono m' hab)
    have h1 := iter_le_iter (fFin m') (fun z => h m' (h m' z)) hstep hmono2 x x
    rw [iter_two_mul] at h1
    have h2 : iter (h m') (2 * x) x ≤ iter (h m') (2 * x) (iter (h m') (x + 1) 3) := by
      apply iter_mono_arg (h m') (fun _ _ hab => h_mono m' hab)
      have hst : ∀ k, 3 * k + 1 ≤ iter (h m') k 3 := by
        intro k; induction k with
        | zero => simp [iter]
        | succ p ihp => rw [iter_succ]; have := h_ge_3x1 m' (iter (h m') p 3); omega
      have := hst (x + 1); omega
    rw [← iter_add] at h2
    have h3 : 2 * x + (x + 1) = 3 * x + 1 := by omega
    rw [h3] at h2
    exact Nat.le_trans h1 h2

theorem f_omega_le_hc (k : Nat) : f_omega k ≤ hc 0 (k + 1) 7 := by
  have h1 := fFin_le_h k k
  have h2 := h_mono k (show 3 * k ≤ hc 0 k 7 by have := hc0_ge_3k k; omega)
  rw [hc_snoc, Nat.zero_add]
  exact Nat.le_trans h1 h2

theorem ho0_iter2_ge_5x3 (z : Nat) : 5 * z + 3 ≤ iter (ho 0) 2 z := by
  rw [iter_succ, iter_succ, iter_zero]
  have hadd := ho_ge_add4 0 (ho 0 z)
  rcases mod3_cases z with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have h0 := hc0_ge_3k q
    rcases (by omega : q = 0 ∨ 1 ≤ q) with rfl | hq
    · rw [ho0_mod0] at hadd ⊢; omega
    · have hhc := hc0_ge_15q q hq
      rw [ho0_mod0] at hadd ⊢; omega
  · have hhc := hc0_ge_15q (q + 1) (by omega)
    rw [ho0_mod1, show 3 * q + 5 = 3 * (q + 1) + 2 by omega, ho0_mod2]; omega
  · have h0 := hc0_ge_3k q
    rcases (by omega : q = 0 ∨ 1 ≤ q) with rfl | hq
    · rw [ho0_mod2] at hadd ⊢; omega
    · have hhc := hc0_ge_15q q hq
      rw [ho0_mod2] at hadd ⊢; omega

theorem ho0_iter2_gt_f_omega {y z : Nat} (hz : 3 * y + 3 ≤ z) :
    f_omega y < iter (ho 0) 2 z := by
  have hfc := f_omega_le_hc y
  rw [iter_succ, iter_succ, iter_zero]
  have hadd := ho_ge_add4 0 (ho 0 z)
  rcases mod3_cases z with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have := hc0_mono (show y + 1 ≤ q by omega)
    rw [ho0_mod0] at hadd ⊢; omega
  · have := hc0_mono (show y + 1 ≤ q + 1 by omega)
    rw [ho0_mod1, show 3 * q + 5 = 3 * (q + 1) + 2 by omega, ho0_mod2]; omega
  · have := hc0_mono (show y + 1 ≤ q by omega)
    rw [ho0_mod2] at hadd ⊢; omega

theorem ho_ge_5x3 (m x : Nat) : 5 * x + 3 ≤ ho (m + 1) x := by
  induction m generalizing x with
  | zero =>
    have htwo : ∀ k, 5 * k + 3 ≤ iter (ho 0) (k + 1) 6 ∧ 5 * (k + 1) + 3 ≤ iter (ho 0) (k + 2) 6 := by
      intro k
      induction k with
      | zero =>
        have h06 : ho 0 6 = hc 0 2 7 + 7 := ho0_mod0 2
        have hhc := hc0_ge_3k 2
        have hadd := ho_ge_add4 0 (ho 0 6)
        refine ⟨?_, ?_⟩
        · show 5 * 0 + 3 ≤ iter (ho 0) 1 6
          rw [iter_succ, iter_zero, h06]; omega
        · show 5 * (0 + 1) + 3 ≤ iter (ho 0) 2 6
          rw [iter_succ, iter_succ, iter_zero]; omega
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have e : k + 1 + 2 = 2 + (k + 1) := by omega
        rw [e, iter_add]
        have h2 := ho0_iter2_ge_5x3 (iter (ho 0) (k + 1) 6)
        have := ih.1
        omega
    exact (htwo x).1
  | succ m' ih =>
    have hstep : ∀ k, 5 * k + 3 ≤ iter (ho (m' + 1)) k 6 := by
      intro k
      induction k with
      | zero => simp [iter]
      | succ p ihp =>
        rw [iter_succ]
        have := ih (iter (ho (m' + 1)) p 6)
        omega
    have := hstep (x + 1)
    show 5 * x + 3 ≤ iter (ho (m' + 1)) (x + 1) 6
    omega

theorem f_omega_lt_ho1_2 (y : Nat) : f_omega y < ho 1 (ho 1 y) := by
  have hy5 : 5 * y + 3 ≤ ho 1 y := ho_ge_5x3 0 y
  have hgt : f_omega y < iter (ho 0) 2 (ho 1 y) := ho0_iter2_gt_f_omega (by omega)
  have heq : iter (ho 0) 2 (ho 1 y) = ho 1 (y + 2) := by
    show iter (ho 0) 2 (iter (ho 0) (y + 1) 6) = iter (ho 0) (y + 2 + 1) 6
    rw [← iter_add, show 2 + (y + 1) = y + 2 + 1 by omega]
  rw [heq] at hgt
  exact Nat.lt_of_lt_of_le hgt (ho_succ_mono 0 (by omega))

theorem f_omega_plus_le_ho (m x : Nat) (hm : 1 ≤ m) :
    f_omega_plus m x ≤ ho (m + 1) (3 * x) := by
  induction m generalizing x with
  | zero => omega
  | succ m' ih =>
    have hstep1 : ∀ g k, (∀ z, ho g z + 0 ≤ ho g z) → k + 6 ≤ iter (ho g) k 6 := by
      intro g k _
      induction k with
      | zero => simp [iter]
      | succ p ihp => rw [iter_succ]; have := ho_ge_add4 g (iter (ho g) p 6); omega
    cases m' with
    | zero =>
      show iter f_omega x x ≤ iter (ho 1) (3 * x + 1) 6
      have hstep : ∀ z, f_omega z ≤ ho 1 (ho 1 z) := fun z => Nat.le_of_lt (f_omega_lt_ho1_2 z)
      have hmono2 : ∀ a b, a ≤ b → ho 1 (ho 1 a) ≤ ho 1 (ho 1 b) := fun a b hab =>
        ho_succ_mono 0 (ho_succ_mono 0 hab)
      have h1 := iter_le_iter f_omega (fun z => ho 1 (ho 1 z)) hstep hmono2 x x
      rw [iter_two_mul] at h1
      have h2 : iter (ho 1) (2 * x) x ≤ iter (ho 1) (2 * x) (iter (ho 1) (x + 1) 6) := by
        apply iter_mono_arg (ho 1) (fun _ _ hab => ho_succ_mono 0 hab)
        have := hstep1 1 (x + 1) (fun _ => Nat.le_refl _); omega
      rw [← iter_add, show 2 * x + (x + 1) = 3 * x + 1 by omega] at h2
      exact Nat.le_trans h1 h2
    | succ m'' =>
      have ih' : ∀ z, f_omega_plus (m'' + 1) z ≤ ho (m'' + 1 + 1) (3 * z) := fun z => ih z (by omega)
      show iter (f_omega_plus (m'' + 1)) x x ≤ iter (ho (m'' + 2)) (3 * x + 1) 6
      have hstep : ∀ z, f_omega_plus (m'' + 1) z ≤ ho (m'' + 2) (ho (m'' + 2) z) := fun z =>
        Nat.le_trans (ih' z) (ho_succ_mono (m'' + 1) (Nat.le_trans (by omega) (ho_ge_5x3 (m'' + 1) z)))
      have hmono2 : ∀ a b, a ≤ b → ho (m'' + 2) (ho (m'' + 2) a) ≤ ho (m'' + 2) (ho (m'' + 2) b) :=
        fun a b hab => ho_succ_mono (m'' + 1) (ho_succ_mono (m'' + 1) hab)
      have h1 := iter_le_iter (f_omega_plus (m'' + 1)) (fun z => ho (m'' + 2) (ho (m'' + 2) z))
        hstep hmono2 x x
      rw [iter_two_mul] at h1
      have h2 : iter (ho (m'' + 2)) (2 * x) x ≤
                iter (ho (m'' + 2)) (2 * x) (iter (ho (m'' + 2)) (x + 1) 6) := by
        apply iter_mono_arg (ho (m'' + 2)) (fun _ _ hab => ho_succ_mono (m'' + 1) hab)
        have := hstep1 (m'' + 2) (x + 1) (fun _ => Nat.le_refl _); omega
      rw [← iter_add, show 2 * x + (x + 1) = 3 * x + 1 by omega] at h2
      exact Nat.le_trans h1 h2

theorem f_omega_mul2_pos (x : Nat) : 1 ≤ f_omega_mul2 x := by
  have h0 : f_omega_mul2 0 = 1 := rfl
  have := (fOmegaMul_props 2 0).mono 0 x (Nat.zero_le x)
  exact Nat.le_trans (Nat.le_of_eq h0.symm) this

theorem f_omega_mul2_le_hoc (k n : Nat) (hn : 10 ≤ n) :
    f_omega_mul2 k ≤ hoc 0 (k + 2) n := by
  cases k with
  | zero =>
    have hge := hoc_ge_add4 0 2 n
    have := f_omega_mul2_pos 0
    have h0 : f_omega_mul2 0 = 1 := rfl
    show f_omega_mul2 0 ≤ hoc 0 2 n
    omega
  | succ k' =>
    have hplus := f_omega_plus_le_ho (k' + 1) (k' + 1) (by omega)
    have hhoc : hoc 0 (k' + 3) n = ho (k' + 2) (hoc 0 (k' + 2) n) := by
      have := hoc_snoc 0 (k' + 2) n
      simpa using this
    have hadd := hoc_ge_add4 0 (k' + 2) n
    have hle : 3 * (k' + 1) ≤ hoc 0 (k' + 2) n := by omega
    have hmono := ho_succ_mono (k' + 1) hle
    show f_omega_plus (k' + 1) (k' + 1) ≤ hoc 0 (k' + 3) n
    rw [hhoc]
    exact Nat.le_trans hplus hmono

theorem hoc_round_step {x B : Nat} (hB : 3 * (x + 6) ≤ B) :
    3 * (f_omega_mul2 x + 6) + 10 ≤ hoc 0 (B / 3 - 2) 10 := by
  have h1 : x + 4 ≤ B / 3 - 2 := by omega
  have h2 := hoc_mono_k h1 0 10
  have h3 := f_omega_mul2_le_hoc x 10 (by omega)
  have h4 : hoc 0 (x + 3) 10 = ho (x + 2) (hoc 0 (x + 2) 10) := by
    have := hoc_snoc 0 (x + 2) 10
    simpa using this
  have h5 : hoc 0 (x + 4) 10 = ho (x + 3) (hoc 0 (x + 3) 10) := by
    have := hoc_snoc 0 (x + 3) 10
    simpa using this
  have ha : 5 * hoc 0 (x + 2) 10 + 3 ≤ ho (x + 2) (hoc 0 (x + 2) 10) := ho_ge_5x3 (x + 1) _
  have hb : 5 * hoc 0 (x + 3) 10 + 3 ≤ ho (x + 3) (hoc 0 (x + 3) 10) := ho_ge_5x3 (x + 2) _
  have hf := f_omega_mul2_pos x
  omega

theorem fFin_lt_f_omega_succ (k : Nat) (hk : 1 ≤ k) : fFin k (k + 1) < f_omega (k + 1) := by
  have e1 : f_omega (k + 1) = fFin (k + 1) (k + 1) := f_omega_eq (k + 1)
  have e2 : fFin (k + 1) (k + 1) = iter (fFin k) (k + 1) (k + 1) := f_succ_eq k (k + 1)
  have hsucc : f_omega (k + 1) = fFin k (iter (fFin k) k (k + 1)) := by rw [e1, e2, iter_succ]
  have hone : iter (fFin k) 1 (k + 1) = fFin k (k + 1) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, iter_succ, iter_zero]
  have h1k : fFin k (k + 1) ≤ iter (fFin k) k (k + 1) := by
    rw [← hone]
    exact iter_mono_steps (fFin k) (fFin_props k).ge_self hk (k + 1)
  have hm := (fFin_props k).mono _ _ h1k
  have hpos : 1 ≤ fFin k (k + 1) := by
    have := (fFin_props k).gt_pos (k + 1) (by omega); omega
  have hg := (fFin_props k).gt_pos (fFin k (k + 1)) hpos
  rw [hsucc]; omega

theorem ho_succ_eq (m n : Nat) : ho (m + 1) n = iter (ho m) (n + 1) 6 := rfl
theorem hoc_3_eq (n : Nat) : hoc 0 3 n = ho 2 (ho 1 (ho 0 n)) := rfl

theorem seed_bound_hoc3 : 3 * (fFin 5 2 + 6) + 10 ≤ hoc 0 3 10 := by
  have hcomb : ∀ a b c d e g : Nat,
      a ≤ b → b < c → c < d → d + 48 ≤ e → 5 * e + 3 ≤ g → 3 * (a + 6) + 10 ≤ g := by
    intro a b c d e g _ _ _ _ _; omega
  have hf5 : fFin 5 2 ≤ fFin 5 6 := (fFin_props 5).mono 2 6 (by omega)
  have hf6 : fFin 5 6 < f_omega 6 := by
    rw [show (6 : Nat) = 5 + 1 from rfl]
    exact fFin_lt_f_omega_succ 5 (by omega)
  have h06 : ho 0 6 = hc 0 2 7 + 2 * 2 + 3 := by
    rw [show (6 : Nat) = 3 * 2 from rfl, ho0_mod0]
  have hhc : 45 ≤ hc 0 2 7 := hc0_ge_15q 2 (by omega)
  have hge21 : 3 * 6 + 3 ≤ ho 0 6 := by rw [h06]; omega
  have hi3 : f_omega 6 < iter (ho 0) 3 6 := by
    have hone : iter (ho 0) 1 6 = ho 0 6 := by
      rw [show (1 : Nat) = 0 + 1 from rfl, iter_succ, iter_zero]
    have e := iter_add (ho 0) 2 1 6
    rw [hone] at e
    rw [show (2 + 1 : Nat) = 3 from rfl] at e
    rw [e]
    exact ho0_iter2_gt_f_omega hge21
  have hsteps : iter (ho 0) 3 6 + 48 ≤ ho 1 14 := by
    rw [show (1 : Nat) = 0 + 1 from rfl, ho_succ_eq]
    have hadd12 : ∀ j x, x + 4 * j ≤ iter (ho 0) j x := by
      intro j x
      induction j with
      | zero => simp [iter]
      | succ p ihp => rw [iter_succ]; have := ho_ge_add4 0 (iter (ho 0) p x); omega
    have h15 : iter (ho 0) (14 + 1) 6 = iter (ho 0) 12 (iter (ho 0) 3 6) := by
      rw [show (14 + 1 : Nat) = 12 + 3 from rfl, iter_add]
    rw [h15, show (48 : Nat) = 4 * 12 from rfl]
    exact hadd12 12 (iter (ho 0) 3 6)
  have hh010 : ho 0 10 = 14 := by
    rw [show (10 : Nat) = 3 * 3 + 1 from rfl, ho0_mod1]
  rw [hoc_3_eq, hh010]
  have hho2 : 5 * ho 1 14 + 3 ≤ ho 2 (ho 1 14) := by
    rw [show (2 : Nat) = 1 + 1 from rfl]
    exact ho_ge_5x3 1 (ho 1 14)
  exact hcomb _ _ _ _ _ _ hf5 hf6 hi3 hsteps hho2

end BB
