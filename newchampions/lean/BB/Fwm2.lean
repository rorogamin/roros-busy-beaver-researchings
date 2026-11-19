/-
  BB/Fwm2.lean
  Reusable, axiom-free formalization of the 6-state `Fwm2` (`f_{ω×2}`) core
  built directly on top of `KropitzCore tm 3`.
  Powers BB(6, 7), BB(6, 8), and BB(6, 9).
-/

import BB.TM
import BB.FGH
import BB.Kropitz

namespace BB

/-- The `Fwm2` core transitions (extending `KropitzCore tm 3`). -/
structure Fwm2Core (tm : TM) : Prop where
  kc : KropitzCore tm 3
  A4 : tm 0 4 = some ⟨4, Dir.L, some 1⟩
  B4 : tm 1 4 = some ⟨3, Dir.L, some 5⟩
  C4 : tm 2 4 = some ⟨4, Dir.L, some 2⟩
  C5 : tm 2 5 = some ⟨0, Dir.L, some 4⟩
  D5 : tm 3 5 = some ⟨3, Dir.R, some 4⟩
  E0 : tm 4 0 = some ⟨5, Dir.R, some 2⟩
  E1 : tm 4 1 = some ⟨3, Dir.R, some 4⟩
  E3 : tm 4 3 = some ⟨4, Dir.L, some 2⟩
  F0 : tm 5 0 = some ⟨5, Dir.R, some 1⟩
  F3 : tm 5 3 = some ⟨1, Dir.L, some 5⟩

/-- Macro configuration `B5cfg k m R = 0^∞ 5 3^(2m+1) 2^(k+1) A> R`. -/
def B5cfg (k m : Nat) (R : List Nat) : Config :=
  mkCfgR (some 0) (rep (k + 1) 2 (rep (2 * m + 1) 3 [5])) R

/-- Exit accumulator from Kropitz `Bcfg k M (4 :: R)` back to `B5cfg 0 (Wexit k M) R`. -/
def Wexit : Nat → Nat → Nat
  | 0, M => M + 1
  | k + 1, M => Wexit k (Kfn (k + 1) M)

/-- `Fwm2` mathematical accumulator function `Wfn k m` (`> f_{ω+k}(m)` for all `k, m`). -/
def Wfn : Nat → Nat → Nat
  | 0, m => Wexit (2 * m + 2) 0
  | k + 1, m => iter (Wfn k) (2 * m + 2) 0

/-! ### Mathematical Growth Properties of `Wexit` and `Wfn` -/

theorem Wexit_ge (k M : Nat) : M + 1 ≤ Wexit k M := by
  induction k generalizing M with
  | zero => exact Nat.le_refl (M + 1)
  | succ j ih =>
    have h1 := ih (Kfn (j + 1) M)
    have h2 := Kfn_ge_succ (j + 1) M
    change M + 1 ≤ Wexit j (Kfn (j + 1) M)
    omega

theorem Wexit_mono_M (k : Nat) {x y : Nat} (hxy : x ≤ y) : Wexit k x ≤ Wexit k y := by
  induction k generalizing x y with
  | zero => exact Nat.add_le_add_right hxy 1
  | succ j ih => exact ih (Kfn_mono (j + 1) hxy)

theorem Wexit_step_k (k M : Nat) : Wexit k M ≤ Wexit (k + 1) M :=
  Wexit_mono_M k (Nat.le_trans (Nat.le_succ M) (Kfn_ge_succ (k + 1) M))

theorem Wexit_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (M : Nat) : Wexit k1 M ≤ Wexit k2 M := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Wexit_step_k j M)

theorem Wfn_zero_0 : Wfn 0 0 = 15 := rfl

theorem Wfn_zero_gt_f_omega (m : Nat) : f_omega m < Wfn 0 m := by
  have h1 : Kfn (2 * m + 2) 0 + 1 ≤ Wexit (2 * m + 2) 0 := by
    change Kfn (2 * m + 2) 0 + 1 ≤ Wexit (2 * m + 1) (Kfn (2 * m + 2) 0)
    exact Wexit_ge (2 * m + 1) (Kfn (2 * m + 2) 0)
  have h2 : Kfn (2 * m + 2) 0 = Kfn (2 * m + 1) (Kfn (2 * m + 1) 0) := rfl
  have h3 : m ≤ Kfn (2 * m + 1) 0 := Nat.le_trans (by omega : m ≤ 2 * m + 2) (Kfn_zero_ge (2 * m + 1))
  have h4 : Kfn (2 * m + 1) m ≤ Kfn (2 * m + 2) 0 := by
    rw [h2]; exact Kfn_mono (2 * m + 1) h3
  have h5 : fFin m m ≤ Kfn (2 * m + 1) m :=
    Nat.le_trans (Kfn_ge_fFin m m) (Kfn_mono_k (by omega : m ≤ 2 * m + 1) m)
  change fFin m m < Wexit (2 * m + 2) 0
  omega

theorem Wfn_ge_succ (k m : Nat) : m + 1 ≤ Wfn k m := by
  induction k generalizing m with
  | zero =>
    have h1 := Wfn_zero_gt_f_omega m
    have h2 : m ≤ f_omega m := (fOmegaMul_props 1 0).ge_self m
    omega
  | succ j ih =>
    have hsplit : 2 * m + 2 = (2 * m + 1) + 1 := by omega
    change m + 1 ≤ iter (Wfn j) (2 * m + 2) 0
    rw [hsplit, iter_add]
    have h0 : 1 ≤ Wfn j 0 := ih 0
    have h := iter_ge_add_pos (Wfn j) (fun x _ => ih x) (2 * m + 1) (Wfn j 0) h0
    change m + 1 ≤ iter (Wfn j) (2 * m + 1) (Wfn j 0)
    omega

theorem Wfn_mono (k : Nat) {x y : Nat} (hxy : x ≤ y) : Wfn k x ≤ Wfn k y := by
  induction k generalizing x y with
  | zero =>
    exact Wexit_mono_k (by omega) 0
  | succ j _ =>
    change iter (Wfn j) (2 * x + 2) 0 ≤ iter (Wfn j) (2 * y + 2) 0
    exact iter_mono_steps (Wfn j) (fun z => Nat.le_trans (Nat.le_succ z) (Wfn_ge_succ j z)) (by omega) 0

theorem Wfn_zero_ge (k : Nat) : k + 15 ≤ Wfn k 0 := by
  induction k with
  | zero => rw [Wfn_zero_0]; exact Nat.le_refl 15
  | succ j ih =>
    change j + 16 ≤ Wfn j (Wfn j 0)
    have h := Wfn_ge_succ j (Wfn j 0)
    omega

theorem Wfn_step_k (k m : Nat) : Wfn k m ≤ Wfn (k + 1) m := by
  change Wfn k m ≤ iter (Wfn k) (2 * m + 2) 0
  have hsplit : 2 * m + 2 = 1 + (2 * m + 1) := by omega
  rw [hsplit, iter_add]
  have hg : ∀ n, n ≤ iter (Wfn k) n 0 := by
    intro n
    induction n with
    | zero => exact Nat.le_refl 0
    | succ p ihp =>
      rw [iter_succ]
      exact Nat.le_trans (Nat.add_le_add_right ihp 1) (Wfn_ge_succ k _)
  exact Wfn_mono k (Nat.le_trans (by omega : m ≤ 2 * m + 1) (hg (2 * m + 1)))

theorem Wfn_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (m : Nat) : Wfn k1 m ≤ Wfn k2 m := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Wfn_step_k j m)

theorem Wfn_gt_f_omega_plus (k m : Nat) : f_omega_plus k m < Wfn k m := by
  induction k generalizing m with
  | zero => exact Wfn_zero_gt_f_omega m
  | succ j ih =>
    cases m with
    | zero =>
      have h0 : f_omega_plus (j + 1) 0 = 0 := rfl
      have h1 := Wfn_ge_succ (j + 1) 0
      omega
    | succ m' =>
      change iter (f_omega_plus j) (m' + 1) (m' + 1) < iter (Wfn j) (2 * (m' + 1) + 2) 0
      have hsplit : 2 * (m' + 1) + 2 = (m' + 1) + (m' + 3) := by omega
      rw [hsplit, iter_add (Wfn j)]
      have hbase : m' + 1 ≤ iter (Wfn j) (m' + 3) 0 := by
        have hg : ∀ n, n ≤ iter (Wfn j) n 0 := by
          intro n
          induction n with
          | zero => exact Nat.le_refl 0
          | succ p ihp =>
            rw [iter_succ]
            exact Nat.le_trans (Nat.add_le_add_right ihp 1) (Wfn_ge_succ j _)
        exact Nat.le_trans (by omega : m' + 1 ≤ m' + 3) (hg (m' + 3))
      have hlt : iter (f_omega_plus j) (m' + 1) (m' + 1) < iter (Wfn j) (m' + 1) (m' + 1) :=
        iter_strict_dom (Wfn j) (f_omega_plus j) 0 (fun z _ => ih z) (fOmegaMul_props 1 j)
          (m' + 1) (m' + 1) (Nat.succ_pos m') (Nat.zero_le _)
      have harg := iter_mono_arg (Wfn j) (fun _ _ h => Wfn_mono j h) (m' + 1) hbase
      exact Nat.lt_of_lt_of_le hlt harg

/-- For every `n`, `Wfn (n + 1) 0 > f_{ω×2}(n)`. -/
theorem Wfn_succ_zero_gt_f_omega_mul2 (n : Nat) : f_omega_mul2 n < Wfn (n + 1) 0 := by
  change f_omega_plus n n < Wfn n (Wfn n 0)
  have h1 : f_omega_plus n n < Wfn n n := Wfn_gt_f_omega_plus n n
  have h2 : n ≤ Wfn n 0 := Nat.le_trans (by omega : n ≤ n + 15) (Wfn_zero_ge n)
  exact Nat.lt_of_lt_of_le h1 (Wfn_mono n h2)

/-! ### Operational Engine Lemmas for `Fwm2Core` -/

section Fwm2Lemmas

variable {tm : TM} (hf : Fwm2Core tm)
include hf

private theorem loop_E1 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) L (rep n 1 R)) (mkCfgR (some 4) (rep n 3 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 4) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 4) (3 :: L) (rep k 1 R)) :=
      step_mkCfgR_R hf.E1
    have h2 := ih (3 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.F3
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

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

/-- Entry for level 0: `B5cfg 0 m (1 :: R) --> Bcfg (2*m + 2) 0 (4 :: R)`. -/
private theorem fwm2_level0_entry (m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (B5cfg 0 m (1 :: R)) (Bcfg (2 * m + 2) 0 (4 :: R)) t := by
  have h1 : step tm (B5cfg 0 m (1 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + 1) 3 [5]) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hf.kc.A1
  have h2 := loop_B2_3 hf.kc (2 * m + 1) [5] (3 :: R)
  have h3 : step tm (mkCfgR (some 1) [5] (2 :: rep (2 * m + 1) 1 (3 :: R))) =
            some (mkCfgR (some 3) [] (5 :: rep (2 * m + 2) 1 (3 :: R))) :=
    step_mkCfgR_L_cons hf.kc.B2
  have h4 : step tm (mkCfgR (some 3) [] (5 :: rep (2 * m + 2) 1 (3 :: R))) =
            some (mkCfgR (some 4) [3] (rep (2 * m + 2) 1 (3 :: R))) :=
    step_mkCfgR_R hf.D5
  have h5 := loop_E1 hf (2 * m + 2) [3] (3 :: R)
  have hrepE : rep (2 * m + 2) 3 [3] = rep (2 * m + 3) 3 [] := by
    rw [rep_snoc_one]; rfl
  rw [hrepE] at h5
  have h6 : step tm (mkCfgR (some 4) (3 :: rep (2 * m + 2) 3 []) (3 :: R)) =
            some (mkCfgR (some 2) (rep (2 * m + 2) 3 []) (3 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.E3
  have h7 : step tm (mkCfgR (some 2) (rep (2 * m + 2) 3 []) (3 :: 4 :: R)) =
            some (mkCfgR (some 2) (2 :: rep (2 * m + 2) 3 []) (4 :: R)) :=
    step_mkCfgR_R hf.kc.C3
  have h8 : step tm (mkCfgR (some 2) (2 :: rep (2 * m + 2) 3 []) (4 :: R)) =
            some (mkCfgR (some 2) (rep (2 * m + 2) 3 []) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons hf.C4
  obtain ⟨t9, h9⟩ := loop_C_4 hf (2 * m + 2) 0 [] R
  simp only [Nat.zero_add] at h9
  have h10 : step tm (mkCfgR (some 2) [] (2 :: rep (2 * m + 2) 3 (4 :: R))) =
             some (mkCfgR (some 2) [] (0 :: 3 :: rep (2 * m + 2) 3 (4 :: R))) :=
    step_mkCfgR_L_nil hf.kc.C2
  have h11 : step tm (mkCfgR (some 2) [] (0 :: 3 :: rep (2 * m + 2) 3 (4 :: R))) =
             some (mkCfgR (some 1) [3] (3 :: rep (2 * m + 2) 3 (4 :: R))) :=
    step_mkCfgR_R hf.kc.C0
  have h12 : step tm (mkCfgR (some 1) [3] (3 :: rep (2 * m + 2) 3 (4 :: R))) =
             some (mkCfgR (some 0) [2, 3] (rep (2 * m + 2) 3 (4 :: R))) :=
    step_mkCfgR_R hf.kc.B3
  have h13 := loop_A3 hf.kc (2 * m + 2) [2, 3] (4 :: R)
  have hrepA : rep (2 * m + 2) 2 [2, 3] = rep (2 * m + 3) 2 [3] := by
    rw [rep_snoc_one]; rfl
  rw [hrepA] at h13
  have ha := steps_succ tm _ _ _ _ h1 (reaches_trans h2
    (steps_succ tm _ _ _ _ h3 (steps_succ tm _ _ _ _ h4 h5)))
  have hb := steps_succ tm _ _ _ _ h6 (steps_succ tm _ _ _ _ h7
    (steps_succ tm _ _ _ _ h8 (reaches_trans h9
      (steps_succ tm _ _ _ _ h10 (steps_succ tm _ _ _ _ h11 (steps_succ tm _ _ _ _ h12 h13))))))
  exact ⟨_, reaches_trans ha hb⟩

/-- Exit from Kropitz `Bcfg k M (4 :: R)` back to `B5cfg 0 (Wexit k M) R` with `Wexit k M ≤ t`. -/
private theorem fwm2_exit (k : Nat) :
    ∀ M R, ∃ t, Reaches tm (Bcfg k M (4 :: R)) (B5cfg 0 (Wexit k M) R) t ∧ Wexit k M ≤ t := by
  induction k with
  | zero =>
    intro M R
    have h1 : step tm (Bcfg 0 M (4 :: R)) =
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
              some (B5cfg 0 (M + 1) R) := by
      have hm : 2 * (M + 1) + 1 = 2 * M + 3 := by omega
      unfold B5cfg; rw [hm]
      exact step_mkCfgR_R hf.kc.B3
    have h38 := steps_succ tm _ _ _ _ h3 (reaches_trans h4
      (steps_succ tm _ _ _ _ h5 (steps_succ tm _ _ _ _ h6
        (reaches_trans h7 (steps_one tm _ _ h8)))))
    have hall := steps_succ tm _ _ _ _ h1 (reaches_trans h2 h38)
    exact ⟨_, hall, by unfold Wexit; omega⟩
  | succ j ih =>
    intro M R
    have h1 : step tm (Bcfg (j + 1) M (4 :: R)) =
              some (mkCfgR (some 1) (rep (j + 1) 2 (rep (2 * M + 1) 3 [])) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons hf.A4
    have h2 := kropitz_levelS_from_B hf.kc j M (4 :: R)
    obtain ⟨t3, h3⟩ := kropitz_rep hf.kc j (2 * M + 2) 0 (4 :: R)
    obtain ⟨t4, h4, hle4⟩ := ih (Kfn (j + 1) M) R
    have hall := reaches_trans (reaches_trans (steps_succ tm _ _ _ _ h1 h2) h3) h4
    exact ⟨_, hall, Nat.le_trans hle4 (Nat.le_add_left _ _)⟩

/-- Bounce off `[5]` for `k + 1` copies of `2`. -/
private theorem bounce_B5_2k (k : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 [5]) (2 :: R))
               (mkCfgR (some 0) (rep (k + 1) 2 [3, 5]) (1 :: R)) (2 * k + 6) := by
  have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 [5]) (2 :: R)) =
            some (mkCfgR (some 3) (rep k 2 [5]) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons hf.kc.B2
  cases k with
  | zero =>
    have h2 : step tm (mkCfgR (some 3) [5] (2 :: 1 :: R)) =
              some (mkCfgR (some 2) [] (5 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.kc.D2
    have h3 : step tm (mkCfgR (some 2) [] (5 :: 3 :: 1 :: R)) =
              some (mkCfgR (some 4) [] (0 :: 0 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_nil_zero hf.C5
    have h4 : step tm (mkCfgR (some 4) [] (0 :: 0 :: 3 :: 1 :: R)) =
              some (mkCfgR (some 2) [5] (0 :: 3 :: 1 :: R)) :=
      step_mkCfgR_R hf.E0
    have h5 : step tm (mkCfgR (some 2) [5] (0 :: 3 :: 1 :: R)) =
              some (mkCfgR (some 1) [3, 5] (3 :: 1 :: R)) :=
      step_mkCfgR_R hf.kc.C0
    have h6 : step tm (mkCfgR (some 1) [3, 5] (3 :: 1 :: R)) =
              some (mkCfgR (some 0) [2, 3, 5] (1 :: R)) :=
      step_mkCfgR_R hf.kc.B3
    exact steps_succ tm 5 _ _ _ h1 (steps_succ tm 4 _ _ _ h2
      (steps_succ tm 3 _ _ _ h3 (steps_succ tm 2 _ _ _ h4
        (steps_succ tm 1 _ _ _ h5 (steps_one tm _ _ h6)))))
  | succ k' =>
    have h2 : step tm (mkCfgR (some 3) (2 :: rep k' 2 [5]) (2 :: 1 :: R)) =
              some (mkCfgR (some 2) (rep k' 2 [5]) (2 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hf.kc.D2
    have h3 := loop_C2 hf.kc k' [5] (3 :: 1 :: R)
    have h4 : step tm (mkCfgR (some 2) [5] (2 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 2) [] (5 :: 3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_L_cons hf.kc.C2
    have h5 : step tm (mkCfgR (some 2) [] (5 :: 3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 4) [] (0 :: 0 :: 3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_L_nil_zero hf.C5
    have h6 : step tm (mkCfgR (some 4) [] (0 :: 0 :: 3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 2) [5] (0 :: 3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_R hf.E0
    have h7 : step tm (mkCfgR (some 2) [5] (0 :: 3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 1) [3, 5] (3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_R hf.kc.C0
    have h8 : step tm (mkCfgR (some 1) [3, 5] (3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 0) [2, 3, 5] (rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_R hf.kc.B3
    have h9 := loop_A3 hf.kc (k' + 1) [2, 3, 5] (1 :: R)
    have hrepR : rep k' 3 (3 :: 1 :: R) = rep (k' + 1) 3 (1 :: R) := by
      rw [rep_snoc_one]; rfl
    have hrepL : rep (k' + 1) 2 [2, 3, 5] = rep (k' + 2) 2 [3, 5] := by
      rw [rep_snoc_one]; rfl
    rw [hrepR] at h3 h4 h5 h6 h7 h8
    rw [hrepL] at h9
    have h49 := steps_succ tm _ _ _ _ h4 (steps_succ tm _ _ _ _ h5
      (steps_succ tm _ _ _ _ h6 (steps_succ tm _ _ _ _ h7 (steps_succ tm _ _ _ _ h8 h9))))
    have hall := steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (reaches_trans h3 h49))
    have ht : k' + (k' + 1 + 1 + 1 + 1 + 1 + 1) + 1 + 1 = 2 * (k' + 1) + 6 := by omega
    rw [ht] at hall
    exact hall

/-- Main `Fwm2` Engine Theorem:
    `B5cfg k m (1 :: R) --> B5cfg k (Wfn k m) R` in `t` steps with `Wfn k m ≤ t`. -/
theorem fwm2_step (k : Nat) :
    ∀ m R, ∃ t, Reaches tm (B5cfg k m (1 :: R)) (B5cfg k (Wfn k m) R) t ∧ Wfn k m ≤ t := by
  induction k with
  | zero =>
    intro m R
    obtain ⟨t1, h1⟩ := fwm2_level0_entry hf m R
    obtain ⟨t2, h2, hle2⟩ := fwm2_exit hf (2 * m + 2) 0 R
    exact ⟨t1 + t2, reaches_trans h1 h2, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩
  | succ j ih =>
    have hiter : ∀ n m R, ∃ t, Reaches tm (B5cfg j m (rep n 1 R)) (B5cfg j (iter (Wfn j) n m) R) t ∧
        (1 ≤ n → iter (Wfn j) n m ≤ t) := by
      intro n
      induction n with
      | zero => intro m R; exact ⟨0, reaches_zero tm _, fun h => by cases h⟩
      | succ p ihp =>
        intro m R
        obtain ⟨t1, h1, hle1⟩ := ih m (rep p 1 R)
        obtain ⟨t2, h2, hle2⟩ := ihp (Wfn j m) R
        have hcomm : iter (Wfn j) p (Wfn j m) = iter (Wfn j) (p + 1) m := by
          rw [iter_add]; rfl
        rw [hcomm] at h2 hle2
        refine ⟨t1 + t2, reaches_trans h1 h2, fun _ => ?_⟩
        cases p with
        | zero =>
          simp only [iter] at hle1 ⊢
          exact Nat.le_trans hle1 (Nat.le_add_right _ _)
        | succ p' =>
          exact Nat.le_trans (hle2 (Nat.succ_pos p')) (Nat.le_add_left _ _)
    intro m R
    have h1 : step tm (B5cfg (j + 1) m (1 :: R)) =
              some (mkCfgR (some 1) (rep (j + 1) 2 (rep (2 * m + 1) 3 [5])) (2 :: 3 :: R)) :=
      step_mkCfgR_L_cons hf.kc.A1
    have h2 := loop_B2_2k hf.kc j (2 * m + 1) [5] (3 :: R)
    have h3 := bounce_B5_2k hf j (rep (2 * m + 1) 1 (3 :: R))
    have h13 := steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3)
    obtain ⟨t4, h4, hle4⟩ := hiter (2 * m + 2) 0 (3 :: R)
    have h5 : step tm (B5cfg j (Wfn (j + 1) m) (3 :: R)) =
              some (B5cfg (j + 1) (Wfn (j + 1) m) R) :=
      step_mkCfgR_R hf.kc.A3
    have hall := reaches_trans (reaches_trans h13 h4) (steps_one tm _ _ h5)
    have hlb : Wfn (j + 1) m ≤ t4 := hle4 (by omega)
    exact ⟨_, hall, Nat.le_trans hlb (by omega)⟩

end Fwm2Lemmas
end BB
