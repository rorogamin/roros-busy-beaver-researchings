/-
  BB/FGH.lean
  Exact, axiom-free, structurally recursive (System T) Wainer Fast-Growing Hierarchy
  up to ω^2 · c + ω · a + b with standard fundamental sequences:
    f_0(n) = n + 1
    f_{α+1}(n) = f_α^n(n)
    f_ω(n) = f_n(n)
    f_{ω·(a+1)}(n) = f_{ω·a + n}(n)
    f_{ω^2·(c+1)}(n) = f_{ω^2·c + ω·n}(n)
-/

namespace BB

/-- `n`-fold composition of `g` applied to `x`: `g^n(x)`. -/
def iter (g : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => g (iter g n x)

/-- Successor step in FGH: `g ↦ (n ↦ g^n(n))`. -/
def fNext (g : Nat → Nat) (n : Nat) : Nat := iter g n n

/-- Finite addition of ordinals: `fPlus g b` applies `fNext` `b` times to `g`. -/
def fPlus (g : Nat → Nat) : Nat → Nat → Nat
  | 0 => g
  | b + 1 => fNext (fPlus g b)

/-- Diagonalization along a `Nat`-indexed family of functions: `(F_n(n))`. -/
def fDiag (F : Nat → Nat → Nat) (n : Nat) : Nat := F n n

/-- Adding `ω · a` above a base function `g`. -/
def fOmegaStep (g : Nat → Nat) : Nat → Nat → Nat
  | 0 => g
  | a + 1 => fDiag (fPlus (fOmegaStep g a))

/-- Adding `ω^2 · c` above a base function `g`. -/
def fOmega2Step (g : Nat → Nat) : Nat → Nat → Nat
  | 0 => g
  | c + 1 => fDiag (fOmegaStep (fOmega2Step g c))

/-- Base function `f_0(n) = n + 1`. -/
def fZero (n : Nat) : Nat := n + 1

/-- Finite levels `f_k(n)`. -/
def fFin (k : Nat) : Nat → Nat := fPlus fZero k

/-- Level `ω · a + b`: `f_{ω·a + b}(n)`. -/
def fOmegaMul (a b : Nat) : Nat → Nat := fPlus (fOmegaStep fZero a) b

/-- Level `ω^2 · c + ω · a + b`: `f_{ω^2·c + ω·a + b}(n)`. -/
def fOmega2 (c a b : Nat) : Nat → Nat := fPlus (fOmegaStep (fOmega2Step fZero c) a) b

/-! ### Standard Named Aliases -/

abbrev f_omega (n : Nat) : Nat := fOmegaMul 1 0 n
abbrev f_omega_plus (k n : Nat) : Nat := fOmegaMul 1 k n
abbrev f_omega_mul2 (n : Nat) : Nat := fOmegaMul 2 0 n
abbrev f_omega_mul2_plus (k n : Nat) : Nat := fOmegaMul 2 k n
abbrev f_omega2 (n : Nat) : Nat := fOmega2 1 0 0 n
abbrev f_omega2_plus (k n : Nat) : Nat := fOmega2 1 0 k n

/-! ### Definitional Sanity Checks of Standard FGH Equations -/

theorem f_0_eq (n : Nat) : fFin 0 n = n + 1 := rfl
theorem f_succ_eq (k n : Nat) : fFin (k + 1) n = iter (fFin k) n n := rfl
theorem f_omega_eq (n : Nat) : f_omega n = fFin n n := rfl
theorem f_omega_plus_succ_eq (k n : Nat) : f_omega_plus (k + 1) n = iter (f_omega_plus k) n n := rfl
theorem f_omega_mul2_eq (n : Nat) : f_omega_mul2 n = f_omega_plus n n := rfl
theorem f_omega_mul2_plus_succ_eq (k n : Nat) :
    f_omega_mul2_plus (k + 1) n = iter (f_omega_mul2_plus k) n n := rfl
theorem f_omega2_eq (n : Nat) : f_omega2 n = fOmegaMul n 0 n := rfl
theorem f_omega2_plus_succ_eq (k n : Nat) :
    f_omega2_plus (k + 1) n = iter (f_omega2_plus k) n n := rfl

/-! ### Iteration Lemmas -/

theorem iter_zero (g : Nat → Nat) (x : Nat) : iter g 0 x = x := rfl
theorem iter_succ (g : Nat → Nat) (n x : Nat) : iter g (n + 1) x = g (iter g n x) := rfl

theorem iter_add (g : Nat → Nat) (a b x : Nat) :
    iter g (a + b) x = iter g a (iter g b x) := by
  induction a with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.succ_add, iter_succ, iter_succ, ih]

theorem iter_mono_arg (g : Nat → Nat) (hg : ∀ x y, x ≤ y → g x ≤ g y)
    (n : Nat) {x y : Nat} (hxy : x ≤ y) :
    iter g n x ≤ iter g n y := by
  induction n with
  | zero => exact hxy
  | succ k ih => exact hg _ _ ih

theorem iter_ge_self (g : Nat → Nat) (hg : ∀ x, x ≤ g x) (n x : Nat) :
    x ≤ iter g n x := by
  induction n with
  | zero => exact Nat.le_refl x
  | succ k ih => exact Nat.le_trans ih (hg _)

theorem iter_ge_add_pos (g : Nat → Nat) (hg : ∀ x, 1 ≤ x → x + 1 ≤ g x)
    (n x : Nat) (hx : 1 ≤ x) :
    x + n ≤ iter g n x := by
  induction n with
  | zero => exact Nat.le_refl x
  | succ k ih =>
    rw [iter_succ, ← Nat.add_assoc]
    have h1 : 1 ≤ iter g k x := Nat.le_trans (Nat.le_trans hx (Nat.le_add_right x k)) ih
    exact Nat.le_trans (Nat.add_le_add_right ih 1) (hg _ h1)

theorem iter_mono_steps (g : Nat → Nat) (hg : ∀ x, x ≤ g x)
    {n m : Nat} (hnm : n ≤ m) (x : Nat) :
    iter g n x ≤ iter g m x := by
  induction hnm with
  | refl => exact Nat.le_refl _
  | @step k _ ih => exact Nat.le_trans ih (hg _)

theorem iter_two_mul (g : Nat → Nat) (n x : Nat) :
    iter (fun y => g (g y)) n x = iter g (2 * n) x := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h2, iter_succ, iter_succ, iter_succ, ih]

/-! ### Generic Monotonicity & Growth for Every FGH Combinator -/

structure FGHProps (g : Nat → Nat) : Prop where
  ge_self : ∀ n, n ≤ g n
  gt_pos  : ∀ n, 1 ≤ n → n + 1 ≤ g n
  mono    : ∀ x y, x ≤ y → g x ≤ g y

theorem fZero_props : FGHProps fZero where
  ge_self n := Nat.le_succ n
  gt_pos n _ := Nat.le_refl (n + 1)
  mono _ _ h := Nat.add_le_add_right h 1

theorem fNext_props {g : Nat → Nat} (hg : FGHProps g) : FGHProps (fNext g) where
  ge_self n := iter_ge_self g hg.ge_self n n
  gt_pos n hn :=
    Nat.le_trans (by omega : n + 1 ≤ n + n) (iter_ge_add_pos g hg.gt_pos n n hn)
  mono x y hxy :=
    Nat.le_trans
      (iter_mono_steps g hg.ge_self hxy x)
      (iter_mono_arg g hg.mono y hxy)

theorem fNext_ge {g : Nat → Nat} (hg : FGHProps g) (n : Nat) (hn : 1 ≤ n) :
    g n ≤ fNext g n := by
  cases n with
  | zero => cases hn
  | succ m =>
    show g (m + 1) ≤ g (iter g m (m + 1))
    exact hg.mono _ _ (iter_ge_self g hg.ge_self m (m + 1))

theorem fPlus_props {g : Nat → Nat} (hg : FGHProps g) (b : Nat) : FGHProps (fPlus g b) := by
  induction b with
  | zero => exact hg
  | succ k ih => exact fNext_props ih

theorem fPlus_mono_idx {g : Nat → Nat} (hg : FGHProps g) {b1 b2 : Nat} (hb : b1 ≤ b2)
    (n : Nat) (hn : 1 ≤ n) : fPlus g b1 n ≤ fPlus g b2 n := by
  induction hb with
  | refl => exact Nat.le_refl _
  | @step k _ ih => exact Nat.le_trans ih (fNext_ge (fPlus_props hg k) n hn)

theorem fDiag_props {F : Nat → Nat → Nat}
    (hF : ∀ k, FGHProps (F k))
    (hmono : ∀ k1 k2 n, 1 ≤ n → k1 ≤ k2 → F k1 n ≤ F k2 n) :
    FGHProps (fDiag F) where
  ge_self n := (hF n).ge_self n
  gt_pos n hn := (hF n).gt_pos n hn
  mono x y hxy := by
    cases x with
    | zero =>
      cases y with
      | zero => exact Nat.le_refl _
      | succ my =>
        exact Nat.le_trans ((hF 0).mono 0 (my + 1) (Nat.zero_le _))
          (hmono 0 (my + 1) (my + 1) (Nat.succ_pos my) (Nat.zero_le _))
    | succ mx =>
      have hy1 : 1 ≤ y := Nat.le_trans (Nat.succ_pos mx) hxy
      exact Nat.le_trans ((hF (mx + 1)).mono (mx + 1) y hxy)
        (hmono (mx + 1) y y hy1 hxy)

theorem fOmegaStep_props {g : Nat → Nat} (hg : FGHProps g) (a : Nat) :
    FGHProps (fOmegaStep g a) := by
  induction a with
  | zero => exact hg
  | succ a' ih =>
    exact fDiag_props (fun b => fPlus_props ih b) (fun _ _ n hn hb => fPlus_mono_idx ih hb n hn)

theorem fOmegaStep_mono_idx {g : Nat → Nat} (hg : FGHProps g) {a1 a2 : Nat} (ha : a1 ≤ a2)
    (n : Nat) (hn : 1 ≤ n) : fOmegaStep g a1 n ≤ fOmegaStep g a2 n := by
  induction ha with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    have hstep : fOmegaStep g k n ≤ fPlus (fOmegaStep g k) n n :=
      fPlus_mono_idx (fOmegaStep_props hg k) (Nat.zero_le n) n hn
    exact Nat.le_trans ih hstep

theorem fOmega2Step_props {g : Nat → Nat} (hg : FGHProps g) (c : Nat) :
    FGHProps (fOmega2Step g c) := by
  induction c with
  | zero => exact hg
  | succ c' ih =>
    exact fDiag_props (fun a => fOmegaStep_props ih a)
      (fun _ _ n hn ha => fOmegaStep_mono_idx ih ha n hn)

theorem fFin_props (k : Nat) : FGHProps (fFin k) := fPlus_props fZero_props k
theorem fOmegaMul_props (a b : Nat) : FGHProps (fOmegaMul a b) :=
  fPlus_props (fOmegaStep_props fZero_props a) b
theorem fOmega2_props (c a b : Nat) : FGHProps (fOmega2 c a b) :=
  fPlus_props (fOmegaStep_props (fOmega2Step_props fZero_props c) a) b

/-! ### Reusable Level-Climbing Lemma (`H^2 > f_α  ⟹  (H^n(c))^2 > f_{α+1}`) -/

theorem climb_level
    (H f : Nat → Nat) (c : Nat)
    (hc : 2 ≤ c)
    (hH_mono : ∀ x y, x ≤ y → H x ≤ H y)
    (hH_inc  : ∀ x, 2 ≤ x → x + 1 ≤ H x)
    (hH2_gt  : ∀ x, 2 ≤ x → f x < H (H x))
    (hH_ge3  : ∀ x, 2 ≤ x → 3 * x ≤ iter H x c)
    (hf_props : FGHProps f) :
    ∀ x, 2 ≤ x → fNext f x < iter H (iter H x c) c := by
  intro x hx
  have h1 : 3 * x ≤ iter H x c := hH_ge3 x hx
  have hH_self : ∀ y, 2 ≤ y → y ≤ H y := fun y hy => Nat.le_trans (Nat.le_succ y) (hH_inc y hy)
  have hiter_lb : ∀ k y, 2 ≤ y → 2 ≤ iter H k y := by
    intro k y hy
    induction k with
    | zero => exact hy
    | succ m ih => exact Nat.le_trans ih (hH_self _ ih)
  have h_steps : ∀ a b, a ≤ b → iter H a c ≤ iter H b c := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | @step k _ ih => exact Nat.le_trans ih (hH_self _ (hiter_lb k c hc))
  have h_ge3 : iter H (3 * x) c ≤ iter H (iter H x c) c := h_steps (3 * x) _ h1
  have h3x : 3 * x = 2 * x + x := by omega
  rw [h3x, iter_add] at h_ge3
  have hx_le : x ≤ iter H x c := Nat.le_trans (by omega : x ≤ 3 * x) h1
  have h_arg : iter H (2 * x) x ≤ iter H (2 * x) (iter H x c) :=
    iter_mono_arg H hH_mono (2 * x) hx_le
  have h_strict : ∀ k y, 1 ≤ k → 2 ≤ y → iter f k y < iter (fun z => H (H z)) k y := by
    intro k y hk hy
    cases k with
    | zero => cases hk
    | succ m =>
      have hle : ∀ j, 2 ≤ iter f j y ∧ iter f j y ≤ iter (fun z => H (H z)) j y := by
        intro j
        induction j with
        | zero => exact ⟨hy, Nat.le_refl y⟩
        | succ j' ihj =>
          refine ⟨Nat.le_trans ihj.1 (hf_props.ge_self _), ?_⟩
          have hstep1 : f (iter f j' y) ≤ f (iter (fun z => H (H z)) j' y) :=
            hf_props.mono _ _ ihj.2
          have hstep2 : f (iter (fun z => H (H z)) j' y) <
              H (H (iter (fun z => H (H z)) j' y)) :=
            hH2_gt _ (Nat.le_trans ihj.1 ihj.2)
          exact Nat.le_trans hstep1 (Nat.le_of_lt hstep2)
      have hm := hle m
      have hstep1 : f (iter f m y) ≤ f (iter (fun z => H (H z)) m y) :=
        hf_props.mono _ _ hm.2
      have hstep2 : f (iter (fun z => H (H z)) m y) <
          H (H (iter (fun z => H (H z)) m y)) :=
        hH2_gt _ (Nat.le_trans hm.1 hm.2)
      exact Nat.lt_of_le_of_lt hstep1 hstep2
  have hfin := h_strict x x (by omega) hx
  rw [iter_two_mul] at hfin
  exact Nat.lt_of_lt_of_le hfin (Nat.le_trans h_arg h_ge3)

/-- Strict domination preserved under positive iteration `iter f n y < iter H n y`. -/
theorem iter_strict_dom (H f : Nat → Nat) (b : Nat)
    (hdom : ∀ z, b ≤ z → f z < H z)
    (hf : FGHProps f) :
    ∀ n y, 1 ≤ n → b ≤ y → iter f n y < iter H n y := by
  intro n y hn hy
  cases n with
  | zero => cases hn
  | succ m =>
    have hle : ∀ j, b ≤ iter f j y ∧ iter f j y ≤ iter H j y := by
      intro j
      induction j with
      | zero => exact ⟨hy, Nat.le_refl y⟩
      | succ j' ihj =>
        refine ⟨Nat.le_trans ihj.1 (hf.ge_self _), ?_⟩
        have h1 := hf.mono _ _ ihj.2
        have h2 := hdom _ (Nat.le_trans ihj.1 ihj.2)
        exact Nat.le_trans h1 (Nat.le_of_lt h2)
    have hm := hle m
    have h1 := hf.mono _ _ hm.2
    have h2 := hdom _ (Nat.le_trans hm.1 hm.2)
    exact Nat.lt_of_le_of_lt h1 h2

/-- Single-step level-climbing lemma (`H > f_α  ⟹  H^{2x}(c) > f_{α+1}(x)`). -/
theorem climb_double (H f : Nat → Nat) (c : Nat) (hc : 1 ≤ c)
    (hmono : ∀ x y, x ≤ y → H x ≤ H y)
    (hinc : ∀ x, 1 ≤ x → x + 1 ≤ H x)
    (hdom : ∀ x, 1 ≤ x → f x < H x)
    (hf : FGHProps f) :
    ∀ x, 1 ≤ x → fNext f x < iter H (2 * x) c := by
  intro x hx
  have h2x : 2 * x = x + x := by omega
  rw [h2x, iter_add]
  have hbase : x ≤ iter H x c := by
    have h := iter_ge_add_pos H hinc x c hc
    omega
  have harg : iter H x x ≤ iter H x (iter H x c) := iter_mono_arg H hmono x hbase
  have hlt : iter f x x < iter H x x := iter_strict_dom H f 1 hdom hf x x hx hx
  exact Nat.lt_of_lt_of_le hlt harg

end BB
