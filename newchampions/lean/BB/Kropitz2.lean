/-
  BB/Kropitz2.lean
  Reusable, axiom-free formalization of our 2-state, 9-symbol exact Kropitz f_ω core
  and generic reload / pass-2 reload / halt combinators for `BB(2, m)` champions:
    Core (`0..8`, `A0` & `B7` free for bootstraps/reloads/halts):
      A (0): ---  5LA  1LB  6RA  3RA  4RA  2RB  8LB  5LA
      B (1): 4RA  1LA  3LB  2RB  2RB  3LA  3LB  ---  8LB
    Macro configuration:
      `B2cfg k m R := mkCfgR (some 0) (rep (k + 1) 6 (4 :: rep (2 * m) 3 [])) R`
-/

import BB.TM
import BB.FGH
import BB.Kropitz

namespace BB

/-- The 2-state, 9-symbol exact Kropitz `f_ω` core transitions (states `A=0`, `B=1`, symbols `0..8`). -/
structure Kropitz2Core (tm : TM) : Prop where
  A1 : tm 0 1 = some ⟨5, Dir.L, some 0⟩
  A2 : tm 0 2 = some ⟨1, Dir.L, some 1⟩
  A3 : tm 0 3 = some ⟨6, Dir.R, some 0⟩
  A4 : tm 0 4 = some ⟨3, Dir.R, some 0⟩
  A5 : tm 0 5 = some ⟨4, Dir.R, some 0⟩
  A6 : tm 0 6 = some ⟨2, Dir.R, some 1⟩
  A7 : tm 0 7 = some ⟨8, Dir.L, some 1⟩
  A8 : tm 0 8 = some ⟨5, Dir.L, some 0⟩
  B0 : tm 1 0 = some ⟨4, Dir.R, some 0⟩
  B1 : tm 1 1 = some ⟨1, Dir.L, some 0⟩
  B2 : tm 1 2 = some ⟨3, Dir.L, some 1⟩
  B3 : tm 1 3 = some ⟨2, Dir.R, some 1⟩
  B4 : tm 1 4 = some ⟨2, Dir.R, some 1⟩
  B5 : tm 1 5 = some ⟨3, Dir.L, some 0⟩
  B6 : tm 1 6 = some ⟨3, Dir.L, some 1⟩
  B8 : tm 1 8 = some ⟨8, Dir.L, some 1⟩

/-- Canonical 2-state Kropitz macro configuration `0^∞ 3^(2m) 4 6^(k+1) A> R`. -/
def B2cfg (k m : Nat) (R : List Nat) : Config :=
  mkCfgR (some 0) (rep (k + 1) 6 (4 :: rep (2 * m) 3 [])) R

/-! ### Additional Properties of `Kfn` vs `fFin` and `f_omega` -/

theorem Kfn_strict_mono (k : Nat) : ∀ {x y : Nat}, x < y → Kfn k x < Kfn k y := by
  induction k with
  | zero => intro x y hxy; unfold Kfn; omega
  | succ j ih =>
    intro x y hxy
    have hsucc : ∀ z, z + 1 ≤ Kfn j z := Kfn_ge_succ j
    have hle_steps : 2 * x + 2 + 2 ≤ 2 * y + 2 := by omega
    have hmono_k := iter_mono_steps (Kfn j) (fun z => Nat.le_trans (Nat.le_succ z) (hsucc z)) hle_steps 0
    have hstep1 : iter (Kfn j) (2 * x + 2) 0 < iter (Kfn j) ((2 * x + 2) + 1) 0 := by
      rw [iter_succ]
      exact hsucc _
    have hstep2 : iter (Kfn j) ((2 * x + 2) + 1) 0 ≤ iter (Kfn j) (2 * x + 2 + 2) 0 := by
      rw [iter_succ]
      exact Nat.le_trans (Nat.le_succ _) (hsucc _)
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hstep1 hstep2) hmono_k

theorem Kfn_1_eq (m : Nat) : Kfn 1 m = 2 * m + 2 := by
  change iter (Kfn 0) (2 * m + 2) 0 = 2 * m + 2
  induction (2 * m + 2) with
  | zero => rfl
  | succ n ih => rw [iter_succ, Kfn, ih]

theorem Kfn_2_step (n : Nat) : iter (Kfn 1) n 0 + 2 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter_succ, Kfn_1_eq, Nat.pow_succ]
    omega

theorem Kfn_2_0_eq : Kfn 2 0 = 6 := by
  have h2u : Kfn 2 0 = iter (Kfn 1) 2 0 := rfl
  have h := Kfn_2_step 2
  rw [← h2u] at h
  omega

theorem Kfn_3_0_eq : Kfn 3 0 = 32766 := by
  have h3_unfold : Kfn 3 0 = iter (Kfn 2) 2 0 := rfl
  rw [h3_unfold, iter_succ, iter_succ, iter_zero]
  have h20 : Kfn 2 0 = 6 := Kfn_2_0_eq
  have h26 : Kfn 2 6 = 32766 := by
    have h2u : Kfn 2 6 = iter (Kfn 1) (2 * 6 + 2) 0 := rfl
    have h := Kfn_2_step (2 * 6 + 2)
    have hpow : 2 ^ (2 * 6 + 2 + 1) = 32768 := by decide
    rw [← h2u, hpow] at h
    omega
  rw [h20, h26]

theorem Kfn_3_0_pow : Kfn 3 0 + 2 = 2 ^ 15 := by
  rw [Kfn_3_0_eq]

theorem fFin_1_eq (n : Nat) : fFin 1 n = 2 * n := by
  change iter fZero n n = 2 * n
  suffices h : ∀ k x, iter fZero k x = x + k by rw [h n n]; omega
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; rw [iter_succ, ih]; change fZero (x + k) = _; unfold fZero; omega

theorem iter_fFin1 (n x : Nat) : iter (fFin 1) n x = x * 2 ^ n := by
  induction n with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter_succ, fFin_1_eq, ih, Nat.pow_succ]
    have hmul : 2 * (x * 2 ^ k) = x * (2 ^ k * 2) := by
      rw [← Nat.mul_assoc, Nat.mul_comm 2 x, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k)]
    exact hmul

theorem Kfn_zero_gt_fFin2 : ∀ k, 3 ≤ k → fFin k 2 < Kfn k 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ j ih =>
    rcases (by omega : j = 2 ∨ 3 ≤ j) with rfl | hj
    · have hf22 : fFin 2 2 = 8 := by
        have hu : fFin 2 2 = iter (fFin 1) 2 2 := rfl
        rw [hu, iter_fFin1]
      have hf32 : fFin 3 2 = 2048 := by
        have hu : fFin 3 2 = iter (fFin 2) 2 2 := rfl
        rw [hu, iter_succ, iter_succ, iter_zero, hf22]
        have hu2 : fFin 2 8 = iter (fFin 1) 8 8 := rfl
        rw [hu2, iter_fFin1]
      rw [hf32, Kfn_3_0_eq]
      omega
    · have hih := ih hj
      have hf : fFin (j + 1) 2 = fFin j (fFin j 2) := rfl
      have h1 : fFin j (fFin j 2) ≤ Kfn j (fFin j 2) := Kfn_ge_fFin j (fFin j 2)
      have h2 : Kfn j (fFin j 2) < Kfn j (Kfn j 0) := Kfn_strict_mono j hih
      have hk_eq : Kfn (j + 1) 0 = Kfn j (Kfn j 0) := by
        have hu : Kfn (j + 1) 0 = iter (Kfn j) 2 0 := rfl
        rw [hu, iter_succ, iter_succ, iter_zero]
      rw [hf, hk_eq]
      exact Nat.lt_of_le_of_lt h1 h2

theorem Kfn_zero_gt_fOmega (n : Nat) : f_omega n < Kfn (n + 1) 0 := by
  have h1 : f_omega n = fFin n n := rfl
  have h2 : fFin n n ≤ Kfn n n := Kfn_ge_fFin n n
  have hn : n < Kfn n 0 := Kfn_zero_ge n
  have h3 : Kfn n n < Kfn n (Kfn n 0) := Kfn_strict_mono n hn
  have hk_eq : Kfn (n + 1) 0 = Kfn n (Kfn n 0) := by
    show iter (Kfn n) 2 0 = Kfn n (Kfn n 0)
    rfl
  rw [h1, hk_eq]
  exact Nat.lt_of_le_of_lt h2 h3

section Kropitz2Lemmas

variable {tm : TM} (hc : Kropitz2Core tm)
include hc

/-! ### Basic Sweep Loops -/

theorem loop_B3_R (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) L (rep n 3 R)) (mkCfgR (some 1) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) L (3 :: rep k 3 R)) =
              some (mkCfgR (some 1) (2 :: L) (rep k 3 R)) :=
      step_mkCfgR_R hc.B3
    have h2 := ih (2 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem loop_A3_R (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) L (rep n 3 R)) (mkCfgR (some 0) (rep n 6 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 0) L (3 :: rep k 3 R)) =
              some (mkCfgR (some 0) (6 :: L) (rep k 3 R)) :=
      step_mkCfgR_R hc.A3
    have h2 := ih (6 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem loop_B6_L (n a : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep n 6 (a :: L)) (6 :: R))
               (mkCfgR (some 1) L (a :: rep (n + 1) 3 R)) (n + 1) := by
  induction n generalizing R with
  | zero =>
    exact steps_one tm _ _ (step_mkCfgR_L_cons hc.B6)
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) (6 :: rep k 6 (a :: L)) (6 :: R)) =
              some (mkCfgR (some 1) (rep k 6 (a :: L)) (6 :: 3 :: R)) :=
      step_mkCfgR_L_cons hc.B6
    have h2 := ih (3 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ tm (k + 1) _ _ _ h1 h2

theorem loop_B2_L (n a : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep n 2 (a :: L)) (2 :: R))
               (mkCfgR (some 1) L (a :: rep (n + 1) 3 R)) (n + 1) := by
  induction n generalizing R with
  | zero =>
    exact steps_one tm _ _ (step_mkCfgR_L_cons hc.B2)
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 (a :: L)) (2 :: R)) =
              some (mkCfgR (some 1) (rep k 2 (a :: L)) (2 :: 3 :: R)) :=
      step_mkCfgR_L_cons hc.B2
    have h2 := ih (3 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ tm (k + 1) _ _ _ h1 h2

theorem loop_B2_L_nil (n : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep n 2 []) (2 :: R))
               (mkCfgR (some 1) [] (0 :: rep (n + 1) 3 R)) (n + 1) := by
  induction n generalizing R with
  | zero =>
    exact steps_one tm _ _ (step_mkCfgR_L_nil hc.B2)
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 []) (2 :: R)) =
              some (mkCfgR (some 1) (rep k 2 []) (2 :: 3 :: R)) :=
      step_mkCfgR_L_cons hc.B2
    have h2 := ih (3 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ tm (k + 1) _ _ _ h1 h2

/-! ### Kropitz `f_ω` Step (`B2cfg k m (s :: R) --> B2cfg k (Kfn k m) R` for `s = 1` or `s = 8`) -/

theorem step_A2_3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) (rep n 2 (3 :: L)) (2 :: R))
               (mkCfgR (some 0) (rep n 2 L) (2 :: 1 :: R)) (2 * n + 3) := by
  cases n with
  | zero =>
    have h1 : step tm (mkCfgR (some 0) (3 :: L) (2 :: R)) =
              some (mkCfgR (some 1) L (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.A2
    have h2 : step tm (mkCfgR (some 1) L (3 :: 1 :: R)) =
              some (mkCfgR (some 1) (2 :: L) (1 :: R)) :=
      step_mkCfgR_R hc.B3
    have h3 : step tm (mkCfgR (some 1) (2 :: L) (1 :: R)) =
              some (mkCfgR (some 0) L (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.B1
    exact steps_succ tm 2 _ _ _ h1 (steps_succ tm 1 _ _ _ h2 (steps_one tm _ _ h3))
  | succ k =>
    have h1 : step tm (mkCfgR (some 0) (2 :: rep k 2 (3 :: L)) (2 :: R)) =
              some (mkCfgR (some 1) (rep k 2 (3 :: L)) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.A2
    have h2 := loop_B2_L hc k 3 L (1 :: R)
    have h3 := loop_B3_R hc (k + 2) L (1 :: R)
    have hrep3 : 3 :: rep (k + 1) 3 (1 :: R) = rep (k + 2) 3 (1 :: R) := rfl
    rw [hrep3] at h2
    have h4 : step tm (mkCfgR (some 1) (rep (k + 2) 2 L) (1 :: R)) =
              some (mkCfgR (some 0) (rep (k + 1) 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.B1
    have h23 := reaches_trans h2 h3
    have h234 := reaches_trans h23 (steps_one tm _ _ h4)
    have hall := steps_succ tm _ _ _ _ h1 h234
    have ht : k + 1 + (k + 2) + 1 + 1 = 2 * (k + 1) + 3 := by omega
    rw [ht] at hall
    exact hall

theorem loop_A2_3 (n j : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) (rep n 2 (rep j 3 L)) (2 :: R))
               (mkCfgR (some 0) (rep n 2 L) (2 :: rep j 1 R)) ((2 * n + 3) * j) := by
  induction j generalizing R with
  | zero => exact reaches_zero tm _
  | succ m ih =>
    have h1 := step_A2_3 hc n (rep m 3 L) R
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    have h := reaches_trans h1 h2
    have ht : 2 * n + 3 + (2 * n + 3) * m = (2 * n + 3) * (m + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [ht] at h
    exact h

theorem bounce_A2_nil (n : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 0) (rep n 2 []) (2 :: R))
               (mkCfgR (some 0) (rep n 6 [4]) (1 :: R)) (2 * n + 2) := by
  cases n with
  | zero =>
    have h1 : step tm (mkCfgR (some 0) [] (2 :: R)) =
              some (mkCfgR (some 1) [] (0 :: 1 :: R)) :=
      step_mkCfgR_L_nil hc.A2
    have h2 : step tm (mkCfgR (some 1) [] (0 :: 1 :: R)) =
              some (mkCfgR (some 0) [4] (1 :: R)) :=
      step_mkCfgR_R hc.B0
    exact steps_succ tm 1 _ _ _ h1 (steps_one tm _ _ h2)
  | succ k =>
    have h1 : step tm (mkCfgR (some 0) (2 :: rep k 2 []) (2 :: R)) =
              some (mkCfgR (some 1) (rep k 2 []) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.A2
    have h2 := loop_B2_L_nil hc k (1 :: R)
    have h3 : step tm (mkCfgR (some 1) [] (0 :: rep (k + 1) 3 (1 :: R))) =
              some (mkCfgR (some 0) [4] (rep (k + 1) 3 (1 :: R))) :=
      step_mkCfgR_R hc.B0
    have h4 := loop_A3_R hc (k + 1) [4] (1 :: R)
    have hall := steps_succ tm _ _ _ _ h1 (reaches_trans h2 (steps_succ tm _ _ _ _ h3 h4))
    have ht : k + 1 + (k + 1 + 1) + 1 = 2 * (k + 1) + 2 := by omega
    rw [ht] at hall
    exact hall

theorem loop_A1_4 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) (4 :: L) (rep n 1 R))
               (mkCfgR (some 0) (4 :: rep n 3 L) R) (3 * n) := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 0) (4 :: L) (1 :: rep k 1 R)) =
              some (mkCfgR (some 0) L (4 :: 5 :: rep k 1 R)) :=
      step_mkCfgR_L_cons hc.A1
    have h2 : step tm (mkCfgR (some 0) L (4 :: 5 :: rep k 1 R)) =
              some (mkCfgR (some 0) (3 :: L) (5 :: rep k 1 R)) :=
      step_mkCfgR_R hc.A4
    have h3 : step tm (mkCfgR (some 0) (3 :: L) (5 :: rep k 1 R)) =
              some (mkCfgR (some 0) (4 :: 3 :: L) (rep k 1 R)) :=
      step_mkCfgR_R hc.A5
    have h4 := ih (3 :: L)
    rw [rep_snoc_one] at h4
    have hall := steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall
    exact hall

theorem kropitz2_entry {s : Nat} (hs : s = 1 ∨ s = 8) (k m : Nat) (R : List Nat) :
    Reaches tm (B2cfg k m (s :: R))
               (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (2 :: 3 :: R)) 3 := by
  have hAs : tm 0 s = some ⟨5, Dir.L, some 0⟩ := by
    rcases hs with rfl | rfl
    · exact hc.A1
    · exact hc.A8
  have h1 : step tm (B2cfg k m (s :: R)) =
            some (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: 5 :: R)) :=
    step_mkCfgR_L_cons hAs
  have h2 : step tm (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: 5 :: R)) =
            some (mkCfgR (some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) (5 :: R)) :=
    step_mkCfgR_R hc.A6
  have h3 : step tm (mkCfgR (some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) (5 :: R)) =
            some (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.B5
  exact steps_succ tm 2 _ _ _ h1 (steps_succ tm 1 _ _ _ h2 (steps_one tm _ _ h3))

theorem kropitz2_K1 {s : Nat} (hs : s = 1 ∨ s = 8) (m : Nat) (R : List Nat) :
    Reaches tm (B2cfg 0 m (s :: R)) (B2cfg 0 (m + 1) R) (12 * m + 15) := by
  have he := kropitz2_entry hc hs 0 m R
  change Reaches tm (B2cfg 0 m (s :: R)) (mkCfgR (some 0) (4 :: rep (2 * m) 3 []) (2 :: 3 :: R)) 3 at he
  have h1 : step tm (mkCfgR (some 0) (4 :: rep (2 * m) 3 []) (2 :: 3 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: 1 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.A2
  have h2 : step tm (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: 1 :: 3 :: R)) =
            some (mkCfgR (some 1) (2 :: rep (2 * m) 3 []) (1 :: 3 :: R)) :=
    step_mkCfgR_R hc.B4
  have h3 : step tm (mkCfgR (some 1) (2 :: rep (2 * m) 3 []) (1 :: 3 :: R)) =
            some (mkCfgR (some 0) (rep (2 * m) 3 []) (2 :: 1 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.B1
  have h4 := loop_A2_3 hc 0 (2 * m) [] (1 :: 3 :: R)
  have h5 := bounce_A2_nil hc 0 (rep (2 * m) 1 (1 :: 3 :: R))
  have h6 := loop_A1_4 hc (2 * m + 2) [] (3 :: R)
  have h7 : step tm (mkCfgR (some 0) (4 :: rep (2 * m + 2) 3 []) (3 :: R)) =
            some (B2cfg 0 (m + 1) R) := by
    have hm : 2 * (m + 1) = 2 * m + 2 := by omega
    unfold B2cfg; rw [hm]
    exact step_mkCfgR_R hc.A3
  have h13 := steps_succ tm 2 _ _ _ h1 (steps_succ tm 1 _ _ _ h2 (steps_one tm _ _ h3))
  have h4' : Reaches tm (mkCfgR (some 0) (rep (2 * m) 3 []) (2 :: 1 :: 3 :: R))
                        (mkCfgR (some 0) [] (2 :: rep (2 * m) 1 (1 :: 3 :: R))) ((2 * 0 + 3) * (2 * m)) := h4
  have h5' : Reaches tm (mkCfgR (some 0) [] (2 :: rep (2 * m) 1 (1 :: 3 :: R)))
                        (mkCfgR (some 0) [4] (1 :: rep (2 * m) 1 (1 :: 3 :: R))) (2 * 0 + 2) := h5
  have hrep1 : (1 :: rep (2 * m) 1 (1 :: 3 :: R)) = rep (2 * m + 2) 1 (3 :: R) := by
    rw [rep_snoc_one]; rfl
  rw [hrep1] at h5'
  have hall := reaches_trans he (reaches_trans h13 (reaches_trans h4' (reaches_trans h5' (reaches_trans h6 (steps_one tm _ _ h7)))))
  have ht : 3 + (3 + ((2 * 0 + 3) * (2 * m) + (2 * 0 + 2 + (3 * (2 * m + 2) + 1)))) = 12 * m + 15 := by omega
  rw [ht] at hall
  exact hall

theorem kropitz2_K2 {s : Nat} (hs : s = 1 ∨ s = 8) (j m : Nat) (R : List Nat) :
    Reaches tm (B2cfg (j + 1) m (s :: R))
               (B2cfg j 0 (rep (2 * m + 2) 1 (3 :: R)))
               ((2 * j + 5) * (2 * m) + 4 * j + 12) := by
  have he := kropitz2_entry hc hs (j + 1) m R
  have h1 : step tm (mkCfgR (some 0) (6 :: rep j 6 (4 :: rep (2 * m) 3 [])) (2 :: 3 :: R)) =
            some (mkCfgR (some 1) (rep j 6 (4 :: rep (2 * m) 3 [])) (6 :: 1 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.A2
  have h2 := loop_B6_L hc j 4 (rep (2 * m) 3 []) (1 :: 3 :: R)
  have h3 : step tm (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: rep (j + 1) 3 (1 :: 3 :: R))) =
            some (mkCfgR (some 1) (2 :: rep (2 * m) 3 []) (rep (j + 1) 3 (1 :: 3 :: R))) :=
    step_mkCfgR_R hc.B4
  have h4 := loop_B3_R hc (j + 1) (2 :: rep (2 * m) 3 []) (1 :: 3 :: R)
  have hrep2 : rep (j + 1) 2 (2 :: rep (2 * m) 3 []) = rep (j + 2) 2 (rep (2 * m) 3 []) := by
    rw [rep_snoc_one]; rfl
  rw [hrep2] at h4
  have h5 : step tm (mkCfgR (some 1) (2 :: rep (j + 1) 2 (rep (2 * m) 3 [])) (1 :: 3 :: R)) =
            some (mkCfgR (some 0) (rep (j + 1) 2 (rep (2 * m) 3 [])) (2 :: 1 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.B1
  have h6 := loop_A2_3 hc (j + 1) (2 * m) [] (1 :: 3 :: R)
  have h7 := bounce_A2_nil hc (j + 1) (rep (2 * m) 1 (1 :: 3 :: R))
  have hrep1 : (1 :: rep (2 * m) 1 (1 :: 3 :: R)) = rep (2 * m + 2) 1 (3 :: R) := by
    rw [rep_snoc_one]; rfl
  rw [hrep1] at h7
  have h25 := reaches_trans h2 (steps_succ tm _ _ _ _ h3 (reaches_trans h4 (steps_one tm _ _ h5)))
  have h67 := reaches_trans h6 h7
  have hall := reaches_trans he (steps_succ tm _ _ _ _ h1 (reaches_trans h25 h67))
  have hstep_eq : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hstep_eq] at hall
  have ht : 3 + (j + 1 + (j + 1 + 1 + 1) + ((2 * j + 5) * (2 * m) + (2 * (j + 1) + 2)) + 1) =
            (2 * j + 5) * (2 * m) + 4 * j + 12 := by omega
  rw [ht] at hall
  exact hall

/-- Main 2-state Kropitz `f_ω` theorem for input symbol `1` (`B2cfg k m (1 :: R) --> B2cfg k (Kfn k m) R`). -/
theorem kropitz2_step (k : Nat) :
    ∀ m R, ∃ t, Reaches tm (B2cfg k m (1 :: R)) (B2cfg k (Kfn k m) R) t ∧ Kfn k m ≤ t := by
  induction k with
  | zero =>
    intro m R
    exact ⟨12 * m + 15, kropitz2_K1 hc (Or.inl rfl) m R, by unfold Kfn; omega⟩
  | succ j ih =>
    have hiter : ∀ n m R, ∃ t, Reaches tm (B2cfg j m (rep n 1 R)) (B2cfg j (iter (Kfn j) n m) R) t ∧
                              (1 ≤ n → iter (Kfn j) n m ≤ t) := by
      intro n
      induction n with
      | zero => intro m R; exact ⟨0, reaches_zero tm _, fun h => by omega⟩
      | succ p ihp =>
        intro m R
        obtain ⟨t1, h1, hk1⟩ := ih m (rep p 1 R)
        obtain ⟨t2, h2, hle2⟩ := ihp (Kfn j m) R
        have hcomm : iter (Kfn j) p (Kfn j m) = iter (Kfn j) (p + 1) m := by
          rw [iter_add]; rfl
        rw [hcomm] at h2
        refine ⟨t1 + t2, reaches_trans h1 h2, fun _ => ?_⟩
        cases p with
        | zero =>
          rw [← hcomm]
          exact Nat.le_trans hk1 (Nat.le_add_right t1 t2)
        | succ p' =>
          rw [hcomm] at hle2
          exact Nat.le_trans (hle2 (Nat.succ_pos p')) (Nat.le_add_left t2 t1)
    intro m R
    have h1 := kropitz2_K2 hc (Or.inl rfl) j m R
    obtain ⟨t2, h2, hle2⟩ := hiter (2 * m + 2) 0 (3 :: R)
    have h3 : step tm (B2cfg j (Kfn (j + 1) m) (3 :: R)) =
              some (B2cfg (j + 1) (Kfn (j + 1) m) R) :=
      step_mkCfgR_R hc.A3
    have h123 := reaches_trans (reaches_trans h1 h2) (steps_one tm _ _ h3)
    exact ⟨_, h123, Nat.le_trans (hle2 (by omega)) (by omega)⟩

/-- Identical `f_ω` step when reading `8` instead of `1`, since `A8 = 5LA = A1`. -/
theorem kropitz2_step_8 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (B2cfg k m (8 :: R)) (B2cfg k (Kfn k m) R) t ∧ Kfn k m ≤ t := by
  cases k with
  | zero =>
    exact ⟨12 * m + 15, kropitz2_K1 hc (Or.inr rfl) m R, by unfold Kfn; omega⟩
  | succ j =>
    have h1 := kropitz2_K2 hc (Or.inr rfl) j m R
    have hloop : ∀ n m' R', ∃ t, Reaches tm (B2cfg j m' (rep n 1 R')) (B2cfg j (iter (Kfn j) n m') R') t ∧
                                (1 ≤ n → iter (Kfn j) n m' ≤ t) := by
      intro n
      induction n with
      | zero => intro m' R'; exact ⟨0, reaches_zero tm _, fun h => by omega⟩
      | succ p ihp =>
        intro m' R'
        obtain ⟨t1, hs1, hk1⟩ := kropitz2_step hc j m' (rep p 1 R')
        obtain ⟨t2, hs2, hle2⟩ := ihp (Kfn j m') R'
        have hcomm : iter (Kfn j) p (Kfn j m') = iter (Kfn j) (p + 1) m' := by
          rw [iter_add]; rfl
        rw [hcomm] at hs2
        refine ⟨t1 + t2, reaches_trans hs1 hs2, fun _ => ?_⟩
        cases p with
        | zero => rw [← hcomm]; exact Nat.le_trans hk1 (Nat.le_add_right t1 t2)
        | succ p' => rw [hcomm] at hle2; exact Nat.le_trans (hle2 (Nat.succ_pos p')) (Nat.le_add_left t2 t1)
    obtain ⟨t2, h2, hle2⟩ := hloop (2 * m + 2) 0 (3 :: R)
    have h3 : step tm (B2cfg j (Kfn (j + 1) m) (3 :: R)) =
              some (B2cfg (j + 1) (Kfn (j + 1) m) R) :=
      step_mkCfgR_R hc.A3
    have h123 := reaches_trans (reaches_trans h1 h2) (steps_one tm _ _ h3)
    exact ⟨_, h123, Nat.le_trans (hle2 (by omega)) (by omega)⟩

/-! ### Generic Reload (`s -> w`), Pass-2 Reload (`9 -> w`), and Halt (`0 -> 9 -> halt`) -/

theorem reload_bounce_loop {w' : Nat} (htBw : tm 1 (w' + 1) = some ⟨w' + 1, Dir.L, some 1⟩)
    (j : Nat) :
    ∀ m2 R, ∃ t, Reaches tm (mkCfgR (some 1) (rep (m2 + 1) 2 (rep j 3 [])) ((w' + 1) :: R))
                            (mkCfgR (some 1) (rep (m2 + j + 1) 2 []) ((w' + 1) :: R)) t := by
  induction j with
  | zero => intro m2 R; exact ⟨0, reaches_zero tm _⟩
  | succ j' ih =>
    intro m2 R
    have h1 : step tm (mkCfgR (some 1) (2 :: rep m2 2 (rep (j' + 1) 3 [])) ((w' + 1) :: R)) =
              some (mkCfgR (some 1) (rep m2 2 (3 :: rep j' 3 [])) (2 :: (w' + 1) :: R)) :=
      step_mkCfgR_L_cons htBw
    have h2 := loop_B2_L hc m2 3 (rep j' 3 []) ((w' + 1) :: R)
    have h3 := loop_B3_R hc (m2 + 2) (rep j' 3 []) ((w' + 1) :: R)
    have hrep3 : 3 :: rep (m2 + 1) 3 ((w' + 1) :: R) = rep (m2 + 2) 3 ((w' + 1) :: R) := rfl
    rw [hrep3] at h2
    have hstep := steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3)
    obtain ⟨t2, hrec⟩ := ih (m2 + 1) R
    have hidx : m2 + 1 + j' + 1 = m2 + (j' + 1) + 1 := by omega
    rw [hidx] at hrec
    have hrep2 : rep (m2 + 2) 2 (rep j' 3 []) = rep ((m2 + 1) + 1) 2 (rep j' 3 []) := rfl
    exact ⟨_, reaches_trans hstep hrec⟩

theorem reload_from_4 {w' : Nat} (htBw : tm 1 (w' + 1) = some ⟨w' + 1, Dir.L, some 1⟩)
    (k m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: rep (k + 1) 3 ((w' + 1) :: R)))
                    (B2cfg (2 * m + k + 1) 0 ((w' + 1) :: R)) t ∧ 1 ≤ t := by
  have h1 : step tm (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: rep (k + 1) 3 ((w' + 1) :: R))) =
            some (mkCfgR (some 1) (2 :: rep (2 * m) 3 []) (rep (k + 1) 3 ((w' + 1) :: R))) :=
    step_mkCfgR_R hc.B4
  have h2 := loop_B3_R hc (k + 1) (2 :: rep (2 * m) 3 []) ((w' + 1) :: R)
  have hrep2 : rep (k + 1) 2 (2 :: rep (2 * m) 3 []) = rep (k + 2) 2 (rep (2 * m) 3 []) := by
    rw [rep_snoc_one]; rfl
  rw [hrep2] at h2
  obtain ⟨t3, h3⟩ := reload_bounce_loop hc htBw (2 * m) (k + 1) R
  have heq3 : k + 1 + 2 * m + 1 = (2 * m + k + 1) + 1 := by omega
  rw [heq3] at h3
  have h4 : step tm (mkCfgR (some 1) (2 :: rep (2 * m + k + 1) 2 []) ((w' + 1) :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + k + 1) 2 []) (2 :: (w' + 1) :: R)) :=
    step_mkCfgR_L_cons htBw
  have h5 := loop_B2_L_nil hc (2 * m + k + 1) ((w' + 1) :: R)
  have h6 : step tm (mkCfgR (some 1) [] (0 :: rep (2 * m + k + 2) 3 ((w' + 1) :: R))) =
            some (mkCfgR (some 0) [4] (rep (2 * m + k + 2) 3 ((w' + 1) :: R))) :=
    step_mkCfgR_R hc.B0
  have h7 := loop_A3_R hc (2 * m + k + 2) [4] ((w' + 1) :: R)
  have hdest : mkCfgR (some 0) (rep (2 * m + k + 2) 6 [4]) ((w' + 1) :: R) =
               B2cfg (2 * m + k + 1) 0 ((w' + 1) :: R) := rfl
  rw [hdest] at h7
  have h13 := steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3)
  have h47 := steps_succ tm _ _ _ _ h4 (reaches_trans h5 (steps_succ tm _ _ _ _ h6 h7))
  exact ⟨_, reaches_trans h13 h47, by omega⟩

theorem kropitz2_reload_gen {s w' : Nat}
    (htAs : tm 0 s = some ⟨w' + 1, Dir.L, some 1⟩)
    (htBw : tm 1 (w' + 1) = some ⟨w' + 1, Dir.L, some 1⟩)
    (k m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (B2cfg k m (s :: R)) (B2cfg (2 * m + k + 1) 0 ((w' + 1) :: R)) t ∧ 1 ≤ t := by
  have h1 : step tm (B2cfg k m (s :: R)) =
            some (mkCfgR (some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: (w' + 1) :: R)) :=
    step_mkCfgR_L_cons htAs
  have h2 := loop_B6_L hc k 4 (rep (2 * m) 3 []) ((w' + 1) :: R)
  obtain ⟨t3, h3, _⟩ := reload_from_4 hc htBw k m R
  exact ⟨_, steps_succ tm _ _ _ _ h1 (reaches_trans h2 h3), by omega⟩

theorem kropitz2_pass2_reload {w' : Nat}
    (htA9 : tm 0 9 = some ⟨10, Dir.L, some 0⟩)
    (htB10 : tm 1 10 = some ⟨w' + 1, Dir.L, some 1⟩)
    (htBw : tm 1 (w' + 1) = some ⟨w' + 1, Dir.L, some 1⟩)
    (k m : Nat) :
    ∃ t, Reaches tm (B2cfg k m [9]) (B2cfg (2 * m + k + 1) 0 [w' + 1]) t ∧ 1 ≤ t := by
  have h1 : step tm (B2cfg k m [9]) =
            some (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: [10])) :=
    step_mkCfgR_L_cons htA9
  have h2 : step tm (mkCfgR (some 0) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: [10])) =
            some (mkCfgR (some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) [10]) :=
    step_mkCfgR_R hc.A6
  have h3 : step tm (mkCfgR (some 1) (2 :: rep k 6 (4 :: rep (2 * m) 3 [])) [10]) =
            some (mkCfgR (some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) (2 :: [w' + 1])) :=
    step_mkCfgR_L_cons htB10
  have h4 : ∃ t4, Reaches tm (mkCfgR (some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) (2 :: [w' + 1]))
                             (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: rep (k + 1) 3 [w' + 1])) t4 := by
    cases k with
    | zero =>
      exact ⟨1, steps_one tm _ _ (step_mkCfgR_L_cons hc.B2)⟩
    | succ k' =>
      have hs1 : step tm (mkCfgR (some 1) (6 :: rep k' 6 (4 :: rep (2 * m) 3 [])) (2 :: [w' + 1])) =
                 some (mkCfgR (some 1) (rep k' 6 (4 :: rep (2 * m) 3 [])) (6 :: 3 :: [w' + 1])) :=
        step_mkCfgR_L_cons hc.B2
      have hs2 := loop_B6_L hc k' 4 (rep (2 * m) 3 []) (3 :: [w' + 1])
      rw [rep_snoc_one] at hs2
      exact ⟨_, steps_succ tm _ _ _ _ hs1 hs2⟩
  obtain ⟨t4, h4p⟩ := h4
  obtain ⟨t5, h5, _⟩ := reload_from_4 hc htBw k m []
  exact ⟨_, steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3 (reaches_trans h4p h5))), by omega⟩

theorem kropitz2_halt
    (htA0 : tm 0 0 = some ⟨9, Dir.L, some 1⟩)
    (htB9 : tm 1 9 = some ⟨1, Dir.R, none⟩)
    (k m : Nat) :
    HaltsIn tm (B2cfg k m []) (2 * k + 5) := by
  have h1 : step tm (B2cfg k m []) =
            some (mkCfgR (some 1) (rep k 6 (4 :: rep (2 * m) 3 [])) (6 :: [9])) := by
    have hL : rep (k + 1) 6 (4 :: rep (2 * m) 3 []) = 6 :: rep k 6 (4 :: rep (2 * m) 3 []) := rfl
    unfold B2cfg mkCfgR
    rw [hL]
    simp [step, htA0, cons0]
  have h2 := loop_B6_L hc k 4 (rep (2 * m) 3 []) [9]
  have h3 : step tm (mkCfgR (some 1) (rep (2 * m) 3 []) (4 :: rep (k + 1) 3 [9])) =
            some (mkCfgR (some 1) (2 :: rep (2 * m) 3 []) (rep (k + 1) 3 [9])) :=
    step_mkCfgR_R hc.B4
  have h4 := loop_B3_R hc (k + 1) (2 :: rep (2 * m) 3 []) [9]
  have hrep2 : rep (k + 1) 2 (2 :: rep (2 * m) 3 []) = rep (k + 2) 2 (rep (2 * m) 3 []) := by
    rw [rep_snoc_one]; rfl
  rw [hrep2] at h4
  have h5 : step tm (mkCfgR (some 1) (rep (k + 2) 2 (rep (2 * m) 3 [])) [9]) =
            some { st := none, left := 1 :: rep (k + 2) 2 (rep (2 * m) 3 []), cur := 0, right := [] } := by
    simp [mkCfgR, step, htB9, cons0]
  have hall := steps_succ tm _ _ _ _ h1 (reaches_trans h2 (steps_succ tm _ _ _ _ h3 (reaches_trans h4 (steps_one tm _ _ h5))))
  have ht : k + 1 + (k + 1 + 1 + 1) + 1 = 2 * k + 5 := by omega
  rw [ht] at hall
  exact ⟨_, hall, rfl⟩

end Kropitz2Lemmas
end BB