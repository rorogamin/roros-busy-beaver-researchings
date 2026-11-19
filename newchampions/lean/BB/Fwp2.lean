/-
  BB/Fwp2.lean
  Reusable, axiom-free formalization of the 7-state `Fwp2` (`f_{ω^2}`) core
  (`fwp2_6`), built directly on top of `KropitzCore tm 3`.
  Powers ALL `BB(7..11, 6..9)` champions!
-/

import BB.TM
import BB.FGH
import BB.Kropitz

namespace BB

/-- The 7-state `Fwp2` (`f_{ω^2}`) core transitions (extending `KropitzCore tm 3`). -/
structure Fwp2Core (tm : TM) : Prop where
  kc : KropitzCore tm 3
  A4 : tm 0 4 = some ⟨4, Dir.L, some 1⟩
  B4 : tm 1 4 = some ⟨3, Dir.L, some 5⟩
  B5 : tm 1 5 = some ⟨5, Dir.R, some 1⟩
  C4 : tm 2 4 = some ⟨4, Dir.L, some 2⟩
  C5 : tm 2 5 = some ⟨1, Dir.L, some 4⟩
  D1 : tm 3 1 = some ⟨3, Dir.R, some 4⟩
  D5 : tm 3 5 = some ⟨3, Dir.R, some 3⟩
  E0 : tm 4 0 = some ⟨5, Dir.R, some 1⟩
  E1 : tm 4 1 = some ⟨3, Dir.R, some 4⟩
  E3 : tm 4 3 = some ⟨4, Dir.L, some 2⟩
  E4 : tm 4 4 = some ⟨3, Dir.L, some 6⟩
  E5 : tm 4 5 = some ⟨5, Dir.L, some 4⟩
  F0 : tm 5 0 = some ⟨5, Dir.R, some 1⟩
  F3 : tm 5 3 = some ⟨1, Dir.L, some 5⟩
  G0 : tm 6 0 = some ⟨5, Dir.L, some 5⟩
  G3 : tm 6 3 = some ⟨1, Dir.L, some 6⟩
  G5 : tm 6 5 = some ⟨5, Dir.L, some 6⟩

/-- Macro configuration `Scfg r k m R = 0^∞ 5^r 3^(2m+1) 2^(k+1) A> R`. -/
def Scfg (r k m : Nat) (R : List Nat) : Config :=
  mkCfgR (some 0) (rep (k + 1) 2 (rep (2 * m + 1) 3 (rep r 5 []))) R

/-- Structurally recursive exit function along a level function `step`. -/
def PexitOf (step : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, M => M + 1
  | k + 1, M => PexitOf step k (step (k + 1) M)

/-- One `ω`-jump above `prev` (`f_{ω·r + k} ↦ f_{ω·(r+1) + k}`). -/
def Plevel (prev : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, m => PexitOf prev (2 * m + 2) 0
  | k + 1, m => iter (Plevel prev k) (2 * m + 2) 0

/-- Full `Fwp2` accumulator function `Pfn r k m` (`≥ f_{ω·r + k}(m)`). -/
def Pfn : Nat → Nat → Nat → Nat
  | 0 => Kfn
  | r + 1 => Plevel (Pfn r)

/-- Value produced by empty-3 entry `5^(r+1) 2 A> 1 R --> Scfg (r+1) 0 (Pempty r) R`. -/
def Pempty (r : Nat) : Nat := PexitOf (Pfn r) 1 0

/-! ### Mathematical Growth Properties of `Pfn` and `Pempty` -/

private structure LevelProps (r : Nat) (step : Nat → Nat → Nat) : Prop where
  ge_succ   : ∀ k m, m + 1 ≤ step k m
  mono_m    : ∀ k x y, x ≤ y → step k x ≤ step k y
  mono_k    : ∀ k1 k2 m, k1 ≤ k2 → step k1 m ≤ step k2 m
  zero_ge   : ∀ k, k + 1 ≤ step k 0
  succ_zero : ∀ k, step k (step k 0) ≤ step (k + 1) 0
  ge_fgh    : ∀ k m, fOmegaMul r k m ≤ step k m

private theorem PexitOf_ge {step : Nat → Nat → Nat} (hge : ∀ k m, m + 1 ≤ step k m)
    (k M : Nat) : M + 1 ≤ PexitOf step k M := by
  induction k generalizing M with
  | zero => exact Nat.le_refl (M + 1)
  | succ j ih =>
    have h1 := ih (step (j + 1) M)
    have h2 := hge (j + 1) M
    change M + 1 ≤ PexitOf step j (step (j + 1) M)
    omega

private theorem PexitOf_mono_M {step : Nat → Nat → Nat} (hmono : ∀ k x y, x ≤ y → step k x ≤ step k y)
    (k : Nat) {x y : Nat} (hxy : x ≤ y) : PexitOf step k x ≤ PexitOf step k y := by
  induction k generalizing x y with
  | zero => exact Nat.add_le_add_right hxy 1
  | succ j ih => exact ih (hmono (j + 1) x y hxy)

private theorem PexitOf_step_k {step : Nat → Nat → Nat}
    (hge : ∀ k m, m + 1 ≤ step k m) (hmono : ∀ k x y, x ≤ y → step k x ≤ step k y)
    (k M : Nat) : PexitOf step k M ≤ PexitOf step (k + 1) M :=
  PexitOf_mono_M hmono k (Nat.le_trans (Nat.le_succ M) (hge (k + 1) M))

private theorem PexitOf_mono_k {step : Nat → Nat → Nat}
    (hge : ∀ k m, m + 1 ≤ step k m) (hmono : ∀ k x y, x ≤ y → step k x ≤ step k y)
    {k1 k2 : Nat} (hk : k1 ≤ k2) (M : Nat) : PexitOf step k1 M ≤ PexitOf step k2 M := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (PexitOf_step_k hge hmono j M)

private theorem level0_props : LevelProps 0 Kfn where
  ge_succ := Kfn_ge_succ
  mono_m k _ _ h := Kfn_mono k h
  mono_k _ _ m hk := Kfn_mono_k hk m
  zero_ge := Kfn_zero_ge
  succ_zero _ := Nat.le_refl _
  ge_fgh := Kfn_ge_fFin

private theorem level_step_props {r : Nat} {step : Nat → Nat → Nat} (hp : LevelProps r step) :
    LevelProps (r + 1) (Plevel step) := by
  have h0_ge_fgh : ∀ m, fOmegaMul (r + 1) 0 m ≤ Plevel step 0 m := by
    intro m
    have h1 : step (2 * m + 2) 0 + 1 ≤ PexitOf step (2 * m + 2) 0 := by
      change step (2 * m + 2) 0 + 1 ≤ PexitOf step (2 * m + 1) (step (2 * m + 2) 0)
      exact PexitOf_ge hp.ge_succ (2 * m + 1) (step (2 * m + 2) 0)
    have h2 : step (2 * m + 1) (step (2 * m + 1) 0) ≤ step (2 * m + 2) 0 :=
      hp.succ_zero (2 * m + 1)
    have h3 : m ≤ step (2 * m + 1) 0 :=
      Nat.le_trans (by omega : m ≤ 2 * m + 2) (hp.zero_ge (2 * m + 1))
    have h4 : step (2 * m + 1) m ≤ step (2 * m + 2) 0 :=
      Nat.le_trans (hp.mono_m (2 * m + 1) _ _ h3) h2
    have h5 : fOmegaMul r m m ≤ step (2 * m + 1) m :=
      Nat.le_trans (hp.ge_fgh m m) (hp.mono_k m (2 * m + 1) m (by omega))
    change fOmegaMul r m m ≤ PexitOf step (2 * m + 2) 0
    omega
  have hge_succ : ∀ k m, m + 1 ≤ Plevel step k m := by
    intro k
    induction k with
    | zero =>
      intro m
      have h1 : step (2 * m + 2) 0 + 1 ≤ Plevel step 0 m := by
        change step (2 * m + 2) 0 + 1 ≤ PexitOf step (2 * m + 1) (step (2 * m + 2) 0)
        exact PexitOf_ge hp.ge_succ (2 * m + 1) (step (2 * m + 2) 0)
      have h2 := hp.zero_ge (2 * m + 2)
      omega
    | succ j ih =>
      intro m
      change m + 1 ≤ iter (Plevel step j) (2 * m + 2) 0
      have hsplit : 2 * m + 2 = (2 * m + 1) + 1 := by omega
      rw [hsplit, iter_add]
      have h0 : 1 ≤ Plevel step j 0 := ih 0
      have h := iter_ge_add_pos (Plevel step j) (fun x _ => ih x) (2 * m + 1) (Plevel step j 0) h0
      change m + 1 ≤ iter (Plevel step j) (2 * m + 1) (Plevel step j 0)
      omega
  have hmono_m : ∀ k x y, x ≤ y → Plevel step k x ≤ Plevel step k y := by
    intro k
    induction k with
    | zero =>
      intro x y hxy
      exact PexitOf_mono_k hp.ge_succ hp.mono_m (by omega) 0
    | succ j _ =>
      intro x y hxy
      change iter (Plevel step j) (2 * x + 2) 0 ≤ iter (Plevel step j) (2 * y + 2) 0
      exact iter_mono_steps (Plevel step j)
        (fun z => Nat.le_trans (Nat.le_succ z) (hge_succ j z)) (by omega) 0
  have hstep_k : ∀ k m, Plevel step k m ≤ Plevel step (k + 1) m := by
    intro k m
    change Plevel step k m ≤ iter (Plevel step k) (2 * m + 2) 0
    have hsplit : 2 * m + 2 = 1 + (2 * m + 1) := by omega
    rw [hsplit, iter_add]
    have hg : ∀ n, n ≤ iter (Plevel step k) n 0 := by
      intro n
      induction n with
      | zero => exact Nat.le_refl 0
      | succ p ihp =>
        rw [iter_succ]
        exact Nat.le_trans (Nat.add_le_add_right ihp 1) (hge_succ k _)
    exact hmono_m k m _ (Nat.le_trans (by omega : m ≤ 2 * m + 1) (hg (2 * m + 1)))
  have hmono_k : ∀ k1 k2 m, k1 ≤ k2 → Plevel step k1 m ≤ Plevel step k2 m := by
    intro k1 k2 m hk
    induction hk with
    | refl => exact Nat.le_refl _
    | @step j _ ih => exact Nat.le_trans ih (hstep_k j m)
  have hzero_ge : ∀ k, k + 1 ≤ Plevel step k 0 := by
    intro k
    induction k with
    | zero => exact hge_succ 0 0
    | succ j ih =>
      change j + 2 ≤ Plevel step j (Plevel step j 0)
      have h := hge_succ j (Plevel step j 0)
      omega
  have hge_fgh : ∀ k m, fOmegaMul (r + 1) k m ≤ Plevel step k m := by
    intro k
    induction k with
    | zero => exact h0_ge_fgh
    | succ j ih =>
      intro m
      change iter (fOmegaMul (r + 1) j) m m ≤ iter (Plevel step j) (2 * m + 2) 0
      have hsplit : 2 * m + 2 = m + (m + 2) := by omega
      rw [hsplit, iter_add (Plevel step j)]
      have hbase : m ≤ iter (Plevel step j) (m + 2) 0 := by
        have hg : ∀ n, n ≤ iter (Plevel step j) n 0 := by
          intro n
          induction n with
          | zero => exact Nat.le_refl 0
          | succ p ihp =>
            rw [iter_succ]
            exact Nat.le_trans (Nat.add_le_add_right ihp 1) (hge_succ j _)
        exact Nat.le_trans (by omega : m ≤ m + 2) (hg (m + 2))
      have hfn : ∀ n x, iter (fOmegaMul (r + 1) j) n x ≤ iter (Plevel step j) n x := by
        intro n x
        induction n with
        | zero => exact Nat.le_refl x
        | succ p ihp =>
          rw [iter_succ, iter_succ]
          exact Nat.le_trans ((fOmegaMul_props (r + 1) j).mono _ _ ihp) (ih _)
      exact Nat.le_trans (hfn m m) (iter_mono_arg (Plevel step j) (hmono_m j) m hbase)
  exact ⟨hge_succ, hmono_m, hmono_k, hzero_ge, fun _ => Nat.le_refl _, hge_fgh⟩

private theorem Pfn_props (r : Nat) : LevelProps r (Pfn r) := by
  induction r with
  | zero => exact level0_props
  | succ r' ih => exact level_step_props ih

theorem Pfn_ge_succ (r k m : Nat) : m + 1 ≤ Pfn r k m := (Pfn_props r).ge_succ k m
theorem Pfn_mono_m (r k : Nat) {x y : Nat} (hxy : x ≤ y) : Pfn r k x ≤ Pfn r k y :=
  (Pfn_props r).mono_m k x y hxy
theorem Pfn_ge_fgh (r k m : Nat) : fOmegaMul r k m ≤ Pfn r k m := (Pfn_props r).ge_fgh k m

theorem Pfn_step_r (r : Nat) : ∀ k m, Pfn r k m ≤ Pfn (r + 1) k m := by
  intro k
  induction k with
  | zero =>
    intro m
    have hp := Pfn_props r
    have h1 : Pfn r (2 * m + 2) 0 + 1 ≤ PexitOf (Pfn r) (2 * m + 2) 0 := by
      change Pfn r (2 * m + 2) 0 + 1 ≤ PexitOf (Pfn r) (2 * m + 1) (Pfn r (2 * m + 2) 0)
      exact PexitOf_ge hp.ge_succ (2 * m + 1) (Pfn r (2 * m + 2) 0)
    have h2 : Pfn r (2 * m + 1) (Pfn r (2 * m + 1) 0) ≤ Pfn r (2 * m + 2) 0 :=
      hp.succ_zero (2 * m + 1)
    have h3 : m ≤ Pfn r (2 * m + 1) 0 :=
      Nat.le_trans (by omega : m ≤ 2 * m + 2) (hp.zero_ge (2 * m + 1))
    have h4 : Pfn r 0 m ≤ Pfn r (2 * m + 1) m := hp.mono_k 0 (2 * m + 1) m (Nat.zero_le _)
    have h5 : Pfn r (2 * m + 1) m ≤ Pfn r (2 * m + 1) (Pfn r (2 * m + 1) 0) :=
      hp.mono_m (2 * m + 1) m _ h3
    change Pfn r 0 m ≤ PexitOf (Pfn r) (2 * m + 2) 0
    omega
  | succ j ih =>
    intro m
    have hP : Pfn r (j + 1) m = iter (Pfn r j) (2 * m + 2) 0 := by cases r <;> rfl
    rw [hP]
    change iter (Pfn r j) (2 * m + 2) 0 ≤ iter (Pfn (r + 1) j) (2 * m + 2) 0
    have hfn : ∀ n x, iter (Pfn r j) n x ≤ iter (Pfn (r + 1) j) n x := by
      intro n x
      induction n with
      | zero => exact Nat.le_refl x
      | succ p ihp =>
        rw [iter_succ, iter_succ]
        exact Nat.le_trans (Pfn_mono_m r j ihp) (ih _)
    exact hfn (2 * m + 2) 0

theorem Pfn_mono_r {r1 r2 : Nat} (hr : r1 ≤ r2) (k m : Nat) : Pfn r1 k m ≤ Pfn r2 k m := by
  induction hr with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Pfn_step_r j k m)

theorem Pfn_r_zero_ge (r : Nat) : r + 1 ≤ Pfn r 0 0 := by
  induction r with
  | zero => exact Nat.le_refl 1
  | succ r' ih =>
    have hp := Pfn_props r'
    have h1 : Pfn r' 2 0 + 1 ≤ Pfn (r' + 1) 0 0 := by
      change Pfn r' 2 0 + 1 ≤ PexitOf (Pfn r') 1 (Pfn r' 2 0)
      exact PexitOf_ge hp.ge_succ 1 (Pfn r' 2 0)
    have h2 : Pfn r' 0 0 ≤ Pfn r' 2 0 := hp.mono_k 0 2 0 (by omega)
    omega

theorem Pempty_mono {r1 r2 : Nat} (hr : r1 ≤ r2) : Pempty r1 ≤ Pempty r2 := by
  change Pfn r1 1 0 + 1 ≤ Pfn r2 1 0 + 1
  exact Nat.add_le_add_right (Pfn_mono_r hr 1 0) 1

theorem Pempty_ge (r : Nat) : r + 2 ≤ Pempty r := by
  change r + 2 ≤ Pfn r 1 0 + 1
  have h1 := Pfn_r_zero_ge r
  have h2 := (Pfn_props r).mono_k 0 1 0 (by omega)
  omega

/-- Key `f_{ω^2}` Domination Theorem: `f_{ω^2}(r) < Pempty r` for ALL `r : Nat`! -/
theorem Pempty_gt_f_omega2 (r : Nat) : f_omega2 r < Pempty r := by
  change fOmegaMul r 0 r < Pfn r 1 0 + 1
  have h1 : fOmegaMul r 0 r ≤ Pfn r 0 r := Pfn_ge_fgh r 0 r
  have h2 : r ≤ Pfn r 0 0 := Nat.le_trans (Nat.le_succ r) (Pfn_r_zero_ge r)
  have h3 : Pfn r 0 r ≤ Pfn r 0 (Pfn r 0 0) := Pfn_mono_m r 0 h2
  have h4 : Pfn r 0 (Pfn r 0 0) ≤ Pfn r 1 0 := (Pfn_props r).succ_zero 0
  omega

/-! ### Operational Engine Lemmas for `Fwp2Core` -/

section Fwp2Lemmas

variable {tm : TM} (hf : Fwp2Core tm)
include hf

private theorem loop_B5 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) L (rep n 5 R)) (mkCfgR (some 1) (rep n 5 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) L (5 :: rep k 5 R)) =
              some (mkCfgR (some 1) (5 :: L) (rep k 5 R)) :=
      step_mkCfgR_R hf.B5
    have h2 := ih (5 :: L); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_E1 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) L (rep n 1 R)) (mkCfgR (some 4) (rep n 3 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 4) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 4) (3 :: L) (rep k 1 R)) :=
      step_mkCfgR_R hf.E1
    have h2 := ih (3 :: L); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_E5 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) (rep n 5 L) (5 :: R)) (mkCfgR (some 4) L (5 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 4) (5 :: rep k 5 L) (5 :: R)) =
              some (mkCfgR (some 4) (rep k 5 L) (5 :: 5 :: R)) :=
      step_mkCfgR_L_cons hf.E5
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 5) (rep n 3 L) (3 :: R)) (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.F3
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_G3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 6) (rep n 3 L) (3 :: R)) (mkCfgR (some 6) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 6) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 6) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.G3
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_G5 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 6) (rep n 5 L) (5 :: R)) (mkCfgR (some 6) L (5 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 6) (5 :: rep k 5 L) (5 :: R)) =
              some (mkCfgR (some 6) (rep k 5 L) (5 :: 5 :: R)) :=
      step_mkCfgR_L_cons hf.G5
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

private theorem loop_C_4 (n : Nat) :
    ∀ j L R, ∃ t, Reaches tm (mkCfgR (some 2) (rep n 3 L) (2 :: rep j 3 (4 :: R)))
                             (mkCfgR (some 2) L (2 :: rep (j + n) 3 (4 :: R))) t := by
  induction n with
  | zero => intro j L R; exact ⟨0, reaches_zero tm _⟩
  | succ k ih =>
    intro j L R
    have h1 : step tm (mkCfgR (some 2) (3 :: rep k 3 L) (2 :: rep j 3 (4 :: R))) =
              some (mkCfgR (some 2) (rep k 3 L) (3 :: 3 :: rep j 3 (4 :: R))) :=
      step_mkCfgR_L_cons hf.kc.C2
    have h2 := loop_C3 hf.kc (j + 2) (rep k 3 L) (4 :: R)
    have h3 : step tm (mkCfgR (some 2) (2 :: rep (j + 1) 2 (rep k 3 L)) (4 :: R)) =
              some (mkCfgR (some 2) (rep (j + 1) 2 (rep k 3 L)) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons hf.C4
    have h4 := loop_C2 hf.kc (j + 1) (rep k 3 L) (4 :: R)
    have hstep := reaches_trans (steps_succ tm _ _ _ _ h1 h2) (steps_succ tm _ _ _ _ h3 h4)
    obtain ⟨t2, hrest⟩ := ih (j + 1) L R
    have hadd : j + 1 + k = j + (k + 1) := by omega
    rw [hadd] at hrest
    exact ⟨_, reaches_trans hstep hrest⟩

/-- Shared bounce: `0^∞ 5^r C> 2 3^q R  -->  0^∞ 5^r 3 2^(q+1) A> R` (for ANY `r, q`). -/
private theorem bounce_C2_5r (r q : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 2) (rep r 5 []) (2 :: rep q 3 R))
                    (mkCfgR (some 0) (rep (q + 1) 2 (3 :: rep r 5 [])) R) t := by
  cases r with
  | zero =>
    have h1 : step tm (mkCfgR (some 2) [] (2 :: rep q 3 R)) =
              some (mkCfgR (some 2) [] (0 :: 3 :: rep q 3 R)) :=
      step_mkCfgR_L_nil hf.kc.C2
    have h2 : step tm (mkCfgR (some 2) [] (0 :: 3 :: rep q 3 R)) =
              some (mkCfgR (some 1) [3] (3 :: rep q 3 R)) :=
      step_mkCfgR_R hf.kc.C0
    have h3 : step tm (mkCfgR (some 1) [3] (3 :: rep q 3 R)) =
              some (mkCfgR (some 0) [2, 3] (rep q 3 R)) :=
      step_mkCfgR_R hf.kc.B3
    have h4 := loop_A3 hf.kc q [2, 3] R
    have hrep : rep q 2 [2, 3] = rep (q + 1) 2 [3] := by rw [rep_snoc_one]; rfl
    rw [hrep] at h4
    exact ⟨_, steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3 h4))⟩
  | succ r' =>
    have h1 : step tm (mkCfgR (some 2) (5 :: rep r' 5 []) (2 :: rep q 3 R)) =
              some (mkCfgR (some 2) (rep r' 5 []) (5 :: 3 :: rep q 3 R)) :=
      step_mkCfgR_L_cons hf.kc.C2
    have hmid : ∃ tm1, Reaches tm
        (mkCfgR (some 2) (rep r' 5 []) (5 :: 3 :: rep q 3 R))
        (mkCfgR (some 1) (rep (r' + 1) 5 []) (1 :: 3 :: rep q 3 R)) tm1 := by
      cases r' with
      | zero =>
        have ha : step tm (mkCfgR (some 2) [] (5 :: 3 :: rep q 3 R)) =
                  some (mkCfgR (some 4) [] (0 :: 1 :: 3 :: rep q 3 R)) := step_mkCfgR_L_nil hf.C5
        have hb : step tm (mkCfgR (some 4) [] (0 :: 1 :: 3 :: rep q 3 R)) =
                  some (mkCfgR (some 1) [5] (1 :: 3 :: rep q 3 R)) := step_mkCfgR_R hf.E0
        exact ⟨2, steps_succ tm 1 _ _ _ ha (steps_one tm _ _ hb)⟩
      | succ r'' =>
        have ha : step tm (mkCfgR (some 2) (5 :: rep r'' 5 []) (5 :: 3 :: rep q 3 R)) =
                  some (mkCfgR (some 4) (rep r'' 5 []) (5 :: 1 :: 3 :: rep q 3 R)) :=
          step_mkCfgR_L_cons hf.C5
        have hb := loop_E5 hf r'' [] (1 :: 3 :: rep q 3 R)
        have hc : step tm (mkCfgR (some 4) [] (5 :: rep r'' 5 (1 :: 3 :: rep q 3 R))) =
                  some (mkCfgR (some 4) [] (0 :: rep (r'' + 1) 5 (1 :: 3 :: rep q 3 R))) :=
          step_mkCfgR_L_nil hf.E5
        have hd : step tm (mkCfgR (some 4) [] (0 :: rep (r'' + 1) 5 (1 :: 3 :: rep q 3 R))) =
                  some (mkCfgR (some 1) [5] (rep (r'' + 1) 5 (1 :: 3 :: rep q 3 R))) :=
          step_mkCfgR_R hf.E0
        have he := loop_B5 hf (r'' + 1) [5] (1 :: 3 :: rep q 3 R)
        have hrep5 : rep (r'' + 1) 5 [5] = rep (r'' + 2) 5 [] := by rw [rep_snoc_one]; rfl
        rw [hrep5] at he
        exact ⟨_, steps_succ tm _ _ _ _ ha (reaches_trans hb
          (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd he)))⟩
    obtain ⟨tm1, hmidp⟩ := hmid
    have h5 : step tm (mkCfgR (some 1) (rep (r' + 1) 5 []) (1 :: 3 :: rep q 3 R)) =
              some (mkCfgR (some 1) (3 :: rep (r' + 1) 5 []) (3 :: rep q 3 R)) :=
      step_mkCfgR_R hf.kc.B1
    have h6 : step tm (mkCfgR (some 1) (3 :: rep (r' + 1) 5 []) (3 :: rep q 3 R)) =
              some (mkCfgR (some 0) (2 :: 3 :: rep (r' + 1) 5 []) (rep q 3 R)) :=
      step_mkCfgR_R hf.kc.B3
    have h7 := loop_A3 hf.kc q (2 :: 3 :: rep (r' + 1) 5 []) R
    have hrepA : rep q 2 (2 :: 3 :: rep (r' + 1) 5 []) = rep (q + 1) 2 (3 :: rep (r' + 1) 5 []) := by
      rw [rep_snoc_one]; rfl
    rw [hrepA] at h7
    exact ⟨_, steps_succ tm _ _ _ _ h1 (reaches_trans hmidp
      (steps_succ tm _ _ _ _ h5 (steps_succ tm _ _ _ _ h6 h7)))⟩

/-- Entry `(r + 1, k = 0)`: `Scfg (r + 1) 0 m (1 :: R) --> Scfg r (2 * m + 2) 0 (4 :: R)`. -/
private theorem fwp2_level0_entry (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (1 :: R)) (Scfg r (2 * m + 2) 0 (4 :: R)) t := by
  have h1 : step tm (Scfg (r + 1) 0 m (1 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hf.kc.A1
  have h2 := loop_B2_3 hf.kc (2 * m + 1) (rep (r + 1) 5 []) (3 :: R)
  have h3 : step tm (mkCfgR (some 1) (5 :: rep r 5 []) (2 :: rep (2 * m + 1) 1 (3 :: R))) =
            some (mkCfgR (some 3) (rep r 5 []) (5 :: 1 :: rep (2 * m + 1) 1 (3 :: R))) :=
    step_mkCfgR_L_cons hf.kc.B2
  have h4 : step tm (mkCfgR (some 3) (rep r 5 []) (5 :: 1 :: rep (2 * m + 1) 1 (3 :: R))) =
            some (mkCfgR (some 3) (3 :: rep r 5 []) (1 :: rep (2 * m + 1) 1 (3 :: R))) :=
    step_mkCfgR_R hf.D5
  have h5 : step tm (mkCfgR (some 3) (3 :: rep r 5 []) (1 :: rep (2 * m + 1) 1 (3 :: R))) =
            some (mkCfgR (some 4) (3 :: 3 :: rep r 5 []) (rep (2 * m + 1) 1 (3 :: R))) :=
    step_mkCfgR_R hf.D1
  have h6 := loop_E1 hf (2 * m + 1) (3 :: 3 :: rep r 5 []) (3 :: R)
  have hrepE : rep (2 * m + 1) 3 (3 :: 3 :: rep r 5 []) = rep (2 * m + 3) 3 (rep r 5 []) := by
    rw [rep_snoc_one, rep_snoc_one]; rfl
  rw [hrepE] at h6
  have h7 : step tm (mkCfgR (some 4) (3 :: rep (2 * m + 2) 3 (rep r 5 [])) (3 :: R)) =
            some (mkCfgR (some 2) (rep (2 * m + 2) 3 (rep r 5 [])) (3 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.E3
  have h8 : step tm (mkCfgR (some 2) (rep (2 * m + 2) 3 (rep r 5 [])) (3 :: 4 :: R)) =
            some (mkCfgR (some 2) (2 :: rep (2 * m + 2) 3 (rep r 5 [])) (4 :: R)) :=
    step_mkCfgR_R hf.kc.C3
  have h9 : step tm (mkCfgR (some 2) (2 :: rep (2 * m + 2) 3 (rep r 5 [])) (4 :: R)) =
            some (mkCfgR (some 2) (rep (2 * m + 2) 3 (rep r 5 [])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.C4
  obtain ⟨t10, h10⟩ := loop_C_4 hf (2 * m + 2) 0 (rep r 5 []) R
  simp only [Nat.zero_add] at h10
  obtain ⟨t11, h11⟩ := bounce_C2_5r hf r (2 * m + 2) (4 :: R)
  have ha := steps_succ tm _ _ _ _ h1 (reaches_trans h2
    (steps_succ tm _ _ _ _ h3 (steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5 h6))))
  have hb := steps_succ tm _ _ _ _ h7 (steps_succ tm _ _ _ _ h8
    (steps_succ tm _ _ _ _ h9 (reaches_trans h10 h11)))
  exact ⟨_, reaches_trans ha hb⟩

/-- Empty-3 Entry: `5^(r+1) 2 A> 1 R --> Scfg r 1 0 (4 :: R)`. -/
private theorem fwp2_empty3_entry (r : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: R))
                    (Scfg r 1 0 (4 :: R)) t := by
  have h1 : step tm (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: R)) =
            some (mkCfgR (some 1) (5 :: rep r 5 []) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hf.kc.A1
  have h2 : step tm (mkCfgR (some 1) (5 :: rep r 5 []) (2 :: 3 :: R)) =
            some (mkCfgR (some 3) (rep r 5 []) (5 :: 1 :: 3 :: R)) :=
    step_mkCfgR_L_cons hf.kc.B2
  have h3 : step tm (mkCfgR (some 3) (rep r 5 []) (5 :: 1 :: 3 :: R)) =
            some (mkCfgR (some 3) (3 :: rep r 5 []) (1 :: 3 :: R)) :=
    step_mkCfgR_R hf.D5
  have h4 : step tm (mkCfgR (some 3) (3 :: rep r 5 []) (1 :: 3 :: R)) =
            some (mkCfgR (some 4) (3 :: 3 :: rep r 5 []) (3 :: R)) :=
    step_mkCfgR_R hf.D1
  have h5 : step tm (mkCfgR (some 4) (3 :: 3 :: rep r 5 []) (3 :: R)) =
            some (mkCfgR (some 2) (3 :: rep r 5 []) (3 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.E3
  have h6 : step tm (mkCfgR (some 2) (3 :: rep r 5 []) (3 :: 4 :: R)) =
            some (mkCfgR (some 2) (2 :: 3 :: rep r 5 []) (4 :: R)) :=
    step_mkCfgR_R hf.kc.C3
  have h7 : step tm (mkCfgR (some 2) (2 :: 3 :: rep r 5 []) (4 :: R)) =
            some (mkCfgR (some 2) (3 :: rep r 5 []) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.C4
  obtain ⟨t8, h8⟩ := loop_C_4 hf 1 0 (rep r 5 []) R
  simp only [Nat.zero_add] at h8
  obtain ⟨t9, h9⟩ := bounce_C2_5r hf r 1 (4 :: R)
  exact ⟨_, steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3
    (steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5 (steps_succ tm _ _ _ _ h6
      (steps_succ tm _ _ _ _ h7 (reaches_trans h8 h9)))))))⟩

/-- Bounce for `k + 1` copies of `2` over `rep r 5 []`. -/
private theorem bounce_S_2k (r k : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 (rep r 5 [])) (2 :: R))
                    (mkCfgR (some 0) (rep (k + 1) 2 (3 :: rep r 5 [])) (1 :: R)) t := by
  have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 (rep r 5 [])) (2 :: R)) =
            some (mkCfgR (some 3) (rep k 2 (rep r 5 [])) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons hf.kc.B2
  cases k with
  | zero =>
    cases r with
    | zero =>
      have h2 : step tm (mkCfgR (some 3) [] (2 :: 1 :: R)) =
                some (mkCfgR (some 2) [] (0 :: 3 :: 1 :: R)) := step_mkCfgR_L_nil hf.kc.D2
      have h3 : step tm (mkCfgR (some 2) [] (0 :: 3 :: 1 :: R)) =
                some (mkCfgR (some 1) [3] (3 :: 1 :: R)) := step_mkCfgR_R hf.kc.C0
      have h4 : step tm (mkCfgR (some 1) [3] (3 :: 1 :: R)) =
                some (mkCfgR (some 0) [2, 3] (1 :: R)) := step_mkCfgR_R hf.kc.B3
      exact ⟨4, steps_succ tm 3 _ _ _ h1 (steps_succ tm 2 _ _ _ h2
        (steps_succ tm 1 _ _ _ h3 (steps_one tm _ _ h4)))⟩
    | succ r' =>
      have h2 : step tm (mkCfgR (some 3) (5 :: rep r' 5 []) (2 :: 1 :: R)) =
                some (mkCfgR (some 2) (rep r' 5 []) (5 :: 3 :: 1 :: R)) :=
        step_mkCfgR_L_cons hf.kc.D2
      -- Reuse the same `C5 -> E -> B -> A` bounce!
      have hmid : ∃ tm1, Reaches tm
          (mkCfgR (some 2) (rep r' 5 []) (5 :: 3 :: 1 :: R))
          (mkCfgR (some 1) (rep (r' + 1) 5 []) (1 :: 3 :: 1 :: R)) tm1 := by
        cases r' with
        | zero =>
          have ha : step tm (mkCfgR (some 2) [] (5 :: 3 :: 1 :: R)) =
                    some (mkCfgR (some 4) [] (0 :: 1 :: 3 :: 1 :: R)) := step_mkCfgR_L_nil hf.C5
          have hb : step tm (mkCfgR (some 4) [] (0 :: 1 :: 3 :: 1 :: R)) =
                    some (mkCfgR (some 1) [5] (1 :: 3 :: 1 :: R)) := step_mkCfgR_R hf.E0
          exact ⟨2, steps_succ tm 1 _ _ _ ha (steps_one tm _ _ hb)⟩
        | succ r'' =>
          have ha : step tm (mkCfgR (some 2) (5 :: rep r'' 5 []) (5 :: 3 :: 1 :: R)) =
                    some (mkCfgR (some 4) (rep r'' 5 []) (5 :: 1 :: 3 :: 1 :: R)) :=
            step_mkCfgR_L_cons hf.C5
          have hb := loop_E5 hf r'' [] (1 :: 3 :: 1 :: R)
          have hc : step tm (mkCfgR (some 4) [] (5 :: rep r'' 5 (1 :: 3 :: 1 :: R))) =
                    some (mkCfgR (some 4) [] (0 :: rep (r'' + 1) 5 (1 :: 3 :: 1 :: R))) :=
            step_mkCfgR_L_nil hf.E5
          have hd : step tm (mkCfgR (some 4) [] (0 :: rep (r'' + 1) 5 (1 :: 3 :: 1 :: R))) =
                    some (mkCfgR (some 1) [5] (rep (r'' + 1) 5 (1 :: 3 :: 1 :: R))) :=
            step_mkCfgR_R hf.E0
          have he := loop_B5 hf (r'' + 1) [5] (1 :: 3 :: 1 :: R)
          have hrep5 : rep (r'' + 1) 5 [5] = rep (r'' + 2) 5 [] := by rw [rep_snoc_one]; rfl
          rw [hrep5] at he
          exact ⟨_, steps_succ tm _ _ _ _ ha (reaches_trans hb
            (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd he)))⟩
      obtain ⟨tm1, hmidp⟩ := hmid
      have h5 : step tm (mkCfgR (some 1) (rep (r' + 1) 5 []) (1 :: 3 :: 1 :: R)) =
                some (mkCfgR (some 1) (3 :: rep (r' + 1) 5 []) (3 :: 1 :: R)) :=
        step_mkCfgR_R hf.kc.B1
      have h6 : step tm (mkCfgR (some 1) (3 :: rep (r' + 1) 5 []) (3 :: 1 :: R)) =
                some (mkCfgR (some 0) (2 :: 3 :: rep (r' + 1) 5 []) (1 :: R)) :=
        step_mkCfgR_R hf.kc.B3
      exact ⟨_, steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2
        (reaches_trans hmidp (steps_succ tm _ _ _ _ h5 (steps_one tm _ _ h6))))⟩
  | succ k' =>
    have h2 : step tm (mkCfgR (some 3) (2 :: rep k' 2 (rep r 5 [])) (2 :: 1 :: R)) =
              some (mkCfgR (some 2) (rep k' 2 (rep r 5 [])) (2 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.kc.D2
    have h3 := loop_C2 hf.kc k' (rep r 5 []) (3 :: 1 :: R)
    have hrepR : rep k' 3 (3 :: 1 :: R) = rep (k' + 1) 3 (1 :: R) := by rw [rep_snoc_one]; rfl
    rw [hrepR] at h3
    obtain ⟨t4, h4⟩ := bounce_C2_5r hf r (k' + 1) (1 :: R)
    exact ⟨_, steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (reaches_trans h3 h4))⟩

/-- Base exit `(r, k = 0)`: `Scfg r 0 M (4 :: R) --> Scfg (r + 1) 0 (M + 1) R` in `t ≥ M + 1` steps. -/
private theorem fwp2_exit_zero (r M : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg r 0 M (4 :: R)) (Scfg (r + 1) 0 (M + 1) R) t ∧ M + 1 ≤ t := by
  cases r with
  | zero =>
    have h1 : step tm (Scfg 0 0 M (4 :: R)) =
              some (mkCfgR (some 1) (rep (2 * M + 1) 3 []) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons hf.A4
    have h2 := kropitz_level0_from_B hf.kc M (4 :: R)
    have h3 : step tm (mkCfgR (some 1) (3 :: rep (2 * M + 2) 3 []) (4 :: R)) =
              some (mkCfgR (some 5) (rep (2 * M + 2) 3 []) (3 :: 3 :: R)) :=
      step_mkCfgR_L_cons hf.B4
    have h4 := loop_F3 hf (2 * M + 2) [] (3 :: R)
    have h5 : step tm (mkCfgR (some 5) [] (3 :: rep (2 * M + 2) 1 (3 :: R))) =
              some (mkCfgR (some 5) [] (0 :: rep (2 * M + 3) 1 (3 :: R))) :=
      step_mkCfgR_L_nil hf.F3
    have h6 : step tm (mkCfgR (some 5) [] (0 :: rep (2 * M + 3) 1 (3 :: R))) =
              some (mkCfgR (some 1) [5] (rep (2 * M + 3) 1 (3 :: R))) :=
      step_mkCfgR_R hf.F0
    have h7 := loop_B1 hf.kc (2 * M + 3) [5] (3 :: R)
    have h8 : step tm (mkCfgR (some 1) (rep (2 * M + 3) 3 [5]) (3 :: R)) =
              some (Scfg 1 0 (M + 1) R) := by
      have hm : 2 * (M + 1) + 1 = 2 * M + 3 := by omega
      unfold Scfg; rw [hm]
      exact step_mkCfgR_R hf.kc.B3
    have hall := steps_succ tm _ _ _ _ h1 (reaches_trans h2
      (steps_succ tm _ _ _ _ h3 (reaches_trans h4
        (steps_succ tm _ _ _ _ h5 (steps_succ tm _ _ _ _ h6
          (reaches_trans h7 (steps_one tm _ _ h8)))))))
    exact ⟨_, hall, by omega⟩
  | succ r' =>
    have h1 : step tm (Scfg (r' + 1) 0 M (4 :: R)) =
              some (mkCfgR (some 1) (rep (2 * M + 1) 3 (rep (r' + 1) 5 [])) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons hf.A4
    have h2 := loop_B2_3 hf.kc (2 * M + 1) (rep (r' + 1) 5 []) (4 :: R)
    have h3 : step tm (mkCfgR (some 1) (5 :: rep r' 5 []) (2 :: rep (2 * M + 1) 1 (4 :: R))) =
              some (mkCfgR (some 3) (rep r' 5 []) (5 :: 1 :: rep (2 * M + 1) 1 (4 :: R))) :=
      step_mkCfgR_L_cons hf.kc.B2
    have h4 : step tm (mkCfgR (some 3) (rep r' 5 []) (5 :: 1 :: rep (2 * M + 1) 1 (4 :: R))) =
              some (mkCfgR (some 3) (3 :: rep r' 5 []) (1 :: rep (2 * M + 1) 1 (4 :: R))) :=
      step_mkCfgR_R hf.D5
    have h5 : step tm (mkCfgR (some 3) (3 :: rep r' 5 []) (1 :: rep (2 * M + 1) 1 (4 :: R))) =
              some (mkCfgR (some 4) (3 :: 3 :: rep r' 5 []) (rep (2 * M + 1) 1 (4 :: R))) :=
      step_mkCfgR_R hf.D1
    have h6 := loop_E1 hf (2 * M + 1) (3 :: 3 :: rep r' 5 []) (4 :: R)
    have hrepE : rep (2 * M + 1) 3 (3 :: 3 :: rep r' 5 []) = rep (2 * M + 3) 3 (rep r' 5 []) := by
      rw [rep_snoc_one, rep_snoc_one]; rfl
    rw [hrepE] at h6
    have h7 : step tm (mkCfgR (some 4) (3 :: rep (2 * M + 2) 3 (rep r' 5 [])) (4 :: R)) =
              some (mkCfgR (some 6) (rep (2 * M + 2) 3 (rep r' 5 [])) (3 :: 3 :: R)) :=
      step_mkCfgR_L_cons hf.E4
    have h8 := loop_G3 hf (2 * M + 2) (rep r' 5 []) (3 :: R)
    have hback : ∃ tb, Reaches tm
        (mkCfgR (some 6) (rep r' 5 []) (3 :: rep (2 * M + 2) 1 (3 :: R)))
        (mkCfgR (some 1) (rep (r' + 2) 5 []) (rep (2 * M + 3) 1 (3 :: R))) tb := by
      cases r' with
      | zero =>
        have ga : step tm (mkCfgR (some 6) [] (3 :: rep (2 * M + 2) 1 (3 :: R))) =
                  some (mkCfgR (some 6) [] (0 :: rep (2 * M + 3) 1 (3 :: R))) :=
          step_mkCfgR_L_nil hf.G3
        have gb : step tm (mkCfgR (some 6) [] (0 :: rep (2 * M + 3) 1 (3 :: R))) =
                  some (mkCfgR (some 5) [] (0 :: 5 :: rep (2 * M + 3) 1 (3 :: R))) :=
          step_mkCfgR_L_nil hf.G0
        have gc : step tm (mkCfgR (some 5) [] (0 :: 5 :: rep (2 * M + 3) 1 (3 :: R))) =
                  some (mkCfgR (some 1) [5] (5 :: rep (2 * M + 3) 1 (3 :: R))) :=
          step_mkCfgR_R hf.F0
        have gd : step tm (mkCfgR (some 1) [5] (5 :: rep (2 * M + 3) 1 (3 :: R))) =
                  some (mkCfgR (some 1) [5, 5] (rep (2 * M + 3) 1 (3 :: R))) :=
          step_mkCfgR_R hf.B5
        exact ⟨4, steps_succ tm 3 _ _ _ ga (steps_succ tm 2 _ _ _ gb
          (steps_succ tm 1 _ _ _ gc (steps_one tm _ _ gd)))⟩
      | succ r'' =>
        have ga : step tm (mkCfgR (some 6) (5 :: rep r'' 5 []) (3 :: rep (2 * M + 2) 1 (3 :: R))) =
                  some (mkCfgR (some 6) (rep r'' 5 []) (5 :: rep (2 * M + 3) 1 (3 :: R))) :=
          step_mkCfgR_L_cons hf.G3
        have gb := loop_G5 hf r'' [] (rep (2 * M + 3) 1 (3 :: R))
        have gc : step tm (mkCfgR (some 6) [] (5 :: rep r'' 5 (rep (2 * M + 3) 1 (3 :: R)))) =
                  some (mkCfgR (some 6) [] (0 :: rep (r'' + 1) 5 (rep (2 * M + 3) 1 (3 :: R)))) :=
          step_mkCfgR_L_nil hf.G5
        have gd : step tm (mkCfgR (some 6) [] (0 :: rep (r'' + 1) 5 (rep (2 * M + 3) 1 (3 :: R)))) =
                  some (mkCfgR (some 5) [] (0 :: rep (r'' + 2) 5 (rep (2 * M + 3) 1 (3 :: R)))) :=
          step_mkCfgR_L_nil hf.G0
        have ge : step tm (mkCfgR (some 5) [] (0 :: rep (r'' + 2) 5 (rep (2 * M + 3) 1 (3 :: R)))) =
                  some (mkCfgR (some 1) [5] (rep (r'' + 2) 5 (rep (2 * M + 3) 1 (3 :: R)))) :=
          step_mkCfgR_R hf.F0
        have gf := loop_B5 hf (r'' + 2) [5] (rep (2 * M + 3) 1 (3 :: R))
        have hrep5 : rep (r'' + 2) 5 [5] = rep (r'' + 3) 5 [] := by rw [rep_snoc_one]; rfl
        rw [hrep5] at gf
        exact ⟨_, steps_succ tm _ _ _ _ ga (reaches_trans gb
          (steps_succ tm _ _ _ _ gc (steps_succ tm _ _ _ _ gd (steps_succ tm _ _ _ _ ge gf))))⟩
    obtain ⟨tb, hbackp⟩ := hback
    have h9 := loop_B1 hf.kc (2 * M + 3) (rep (r' + 2) 5 []) (3 :: R)
    have h10 : step tm (mkCfgR (some 1) (rep (2 * M + 3) 3 (rep (r' + 2) 5 [])) (3 :: R)) =
               some (Scfg (r' + 2) 0 (M + 1) R) := by
      have hm : 2 * (M + 1) + 1 = 2 * M + 3 := by omega
      unfold Scfg; rw [hm]
      exact step_mkCfgR_R hf.kc.B3
    have ha := steps_succ tm _ _ _ _ h1 (reaches_trans h2
      (steps_succ tm _ _ _ _ h3 (steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5 h6))))
    have hb := steps_succ tm _ _ _ _ h7 (reaches_trans h8 (reaches_trans hbackp
      (reaches_trans h9 (steps_one tm _ _ h10))))
    exact ⟨_, reaches_trans ha hb, by omega⟩

/-- Simultaneous induction on `r` proving BOTH `fwp2_step` (`1`) AND `fwp2_exit` (`4`). -/
private theorem fwp2_main (r : Nat) :
    (∀ k m R, ∃ t, Reaches tm (Scfg r k m (1 :: R)) (Scfg r k (Pfn r k m) R) t ∧ Pfn r k m ≤ t) ∧
    (∀ k M R, ∃ t, Reaches tm (Scfg r k M (4 :: R)) (Scfg (r + 1) 0 (PexitOf (Pfn r) k M) R) t ∧
                   PexitOf (Pfn r) k M ≤ t) := by
  have mk_rep : ∀ (r0 : Nat) (k : Nat),
      (∀ m R, ∃ t, Reaches tm (Scfg r0 k m (1 :: R)) (Scfg r0 k (Pfn r0 k m) R) t ∧ Pfn r0 k m ≤ t) →
      ∀ n m R, ∃ t, Reaches tm (Scfg r0 k m (rep n 1 R)) (Scfg r0 k (iter (Pfn r0 k) n m) R) t ∧
                    (1 ≤ n → iter (Pfn r0 k) n m ≤ t) := by
    intro r0 k hstep n
    induction n with
    | zero => intro m R; exact ⟨0, reaches_zero tm _, fun h => by cases h⟩
    | succ p ihp =>
      intro m R
      cases p with
      | zero =>
        obtain ⟨t1, h1, hle1⟩ := hstep m R
        exact ⟨t1, h1, fun _ => hle1⟩
      | succ p' =>
        obtain ⟨t1, h1, _⟩ := hstep m (rep (p' + 1) 1 R)
        obtain ⟨t2, h2, hle2⟩ := ihp (Pfn r0 k m) R
        have hcomm : iter (Pfn r0 k) (p' + 1) (Pfn r0 k m) = iter (Pfn r0 k) (p' + 2) m :=
          (iter_add (Pfn r0 k) (p' + 1) 1 m).symm
        rw [hcomm] at h2 hle2
        exact ⟨t1 + t2, reaches_trans h1 h2, fun _ =>
          Nat.le_trans (hle2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩
  have mk_exit : ∀ (r0 : Nat),
      (∀ k m R, ∃ t, Reaches tm (Scfg r0 k m (1 :: R)) (Scfg r0 k (Pfn r0 k m) R) t ∧ Pfn r0 k m ≤ t) →
      ∀ k M R, ∃ t, Reaches tm (Scfg r0 k M (4 :: R)) (Scfg (r0 + 1) 0 (PexitOf (Pfn r0) k M) R) t ∧
                    PexitOf (Pfn r0) k M ≤ t := by
    intro r0 hstep k
    induction k with
    | zero => exact fwp2_exit_zero hf r0
    | succ j ih =>
      intro M R
      have h1 : step tm (Scfg r0 (j + 1) M (4 :: R)) =
                some (mkCfgR (some 1) (rep (j + 1) 2 (rep (2 * M + 1) 3 (rep r0 5 []))) (2 :: 4 :: R)) :=
        step_mkCfgR_L_cons hf.A4
      have h2 := loop_B2_2k hf.kc j (2 * M + 1) (rep r0 5 []) (4 :: R)
      obtain ⟨t3, h3⟩ := bounce_S_2k hf r0 j (rep (2 * M + 1) 1 (4 :: R))
      obtain ⟨t4, h4, _⟩ := mk_rep r0 j (hstep j) (2 * M + 2) 0 (4 :: R)
      obtain ⟨t5, h5, hle5⟩ := ih (Pfn r0 (j + 1) M) R
      have hP : iter (Pfn r0 j) (2 * M + 2) 0 = Pfn r0 (j + 1) M := by
        cases r0 <;> rfl
      rw [hP] at h4
      have hall := reaches_trans (reaches_trans (steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3)) h4) h5
      exact ⟨_, hall, Nat.le_trans hle5 (Nat.le_add_left _ _)⟩
  induction r with
  | zero =>
    have hstep0 : ∀ k m R, ∃ t, Reaches tm (Scfg 0 k m (1 :: R)) (Scfg 0 k (Pfn 0 k m) R) t ∧ Pfn 0 k m ≤ t := by
      intro k
      induction k with
      | zero =>
        intro m R
        exact ⟨8 * m + 9, kropitz_K1 hf.kc m R, by change m + 1 ≤ 8 * m + 9; omega⟩
      | succ j ih =>
        intro m R
        have h1 := kropitz_K2 hf.kc j m R
        obtain ⟨t2, h2, hle2⟩ := mk_rep 0 j ih (2 * m + 2) 0 (3 :: R)
        have h3 : step tm (Scfg 0 j (Pfn 0 (j + 1) m) (3 :: R)) =
                  some (Scfg 0 (j + 1) (Pfn 0 (j + 1) m) R) :=
          step_mkCfgR_R hf.kc.A3
        have hall := reaches_trans (reaches_trans h1 h2) (steps_one tm _ _ h3)
        exact ⟨_, hall, Nat.le_trans (hle2 (by omega)) (by omega)⟩
    exact ⟨hstep0, mk_exit 0 hstep0⟩
  | succ r' ih =>
    have hstepS : ∀ k m R, ∃ t, Reaches tm (Scfg (r' + 1) k m (1 :: R)) (Scfg (r' + 1) k (Pfn (r' + 1) k m) R) t ∧
        Pfn (r' + 1) k m ≤ t := by
      intro k
      induction k with
      | zero =>
        intro m R
        obtain ⟨t1, h1⟩ := fwp2_level0_entry hf r' m R
        obtain ⟨t2, h2, hle2⟩ := ih.2 (2 * m + 2) 0 R
        exact ⟨t1 + t2, reaches_trans h1 h2, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩
      | succ j ihk =>
        intro m R
        have h1 : step tm (Scfg (r' + 1) (j + 1) m (1 :: R)) =
                  some (mkCfgR (some 1) (rep (j + 1) 2 (rep (2 * m + 1) 3 (rep (r' + 1) 5 []))) (2 :: 3 :: R)) :=
          step_mkCfgR_L_cons hf.kc.A1
        have h2 := loop_B2_2k hf.kc j (2 * m + 1) (rep (r' + 1) 5 []) (3 :: R)
        obtain ⟨t3, h3⟩ := bounce_S_2k hf (r' + 1) j (rep (2 * m + 1) 1 (3 :: R))
        obtain ⟨t4, h4, hle4⟩ := mk_rep (r' + 1) j ihk (2 * m + 2) 0 (3 :: R)
        have h5 : step tm (Scfg (r' + 1) j (Pfn (r' + 1) (j + 1) m) (3 :: R)) =
                  some (Scfg (r' + 1) (j + 1) (Pfn (r' + 1) (j + 1) m) R) :=
          step_mkCfgR_R hf.kc.A3
        have hall := reaches_trans (reaches_trans (steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3)) h4)
          (steps_one tm _ _ h5)
        exact ⟨_, hall, Nat.le_trans (hle4 (by omega)) (by omega)⟩
    exact ⟨hstepS, mk_exit (r' + 1) hstepS⟩

/-- Main `Fwp2` Step Theorem: `Scfg r k m (1 :: R) --> Scfg r k (Pfn r k m) R` with `Pfn r k m ≤ t`. -/
theorem fwp2_step (r k m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg r k m (1 :: R)) (Scfg r k (Pfn r k m) R) t ∧ Pfn r k m ≤ t :=
  (fwp2_main hf r).1 k m R

/-- Main `Fwp2` Empty-3 Theorem: `5^(r+1) 2 A> 1 R --> Scfg (r+1) 0 (Pempty r) R` with `Pempty r ≤ t`. -/
theorem fwp2_empty3 (r : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 0) (2 :: rep (r + 1) 5 []) (1 :: R))
                    (Scfg (r + 1) 0 (Pempty r) R) t ∧ Pempty r ≤ t := by
  obtain ⟨t1, h1⟩ := fwp2_empty3_entry hf r R
  obtain ⟨t2, h2, hle2⟩ := (fwp2_main hf r).2 1 0 R
  exact ⟨t1 + t2, reaches_trans h1 h2, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

end Fwp2Lemmas
end BB
