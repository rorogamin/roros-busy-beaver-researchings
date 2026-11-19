/-
  BB/Kropitz.lean
  Reusable, axiom-free formalization of the 3-state Kropitz f_ω core
  (parameterized by the `B2` target state `dState`, so it applies uniformly
   to `fw4_8` (`dState = 2`), `fwm2_6` (`dState = 3`), and `fwp2_6` (`dState = 3`)).
-/

import BB.TM
import BB.FGH

namespace BB

/-- Build a `Config` from state, reversed left tape `L`, and right tape `R`
    (with `R = []` meaning `cur = 0, right = []` and `R = a :: r'` meaning `cur = a, right = r'`). -/
def mkCfgR (st : Option Nat) (L R : List Nat) : Config :=
  match R with
  | [] => { st := st, left := L, cur := 0, right := [] }
  | a :: r' => { st := st, left := L, cur := a, right := r' }

/-- `Reaches tm c1 c2 t` means `tm` transitions from `c1` to `c2` in exact `t` steps. -/
abbrev Reaches (tm : TM) (c1 c2 : Config) (t : Nat) : Prop :=
  steps tm t c1 = some c2

theorem reaches_zero (tm : TM) (c : Config) : Reaches tm c c 0 := rfl

theorem reaches_trans {tm : TM} {c1 c2 c3 : Config} {t1 t2 : Nat}
    (h1 : Reaches tm c1 c2 t1) (h2 : Reaches tm c2 c3 t2) :
    Reaches tm c1 c3 (t1 + t2) :=
  steps_add tm t1 t2 c1 c2 c3 h1 h2

theorem step_mkCfgR_R {tm : TM} {q w : Nat} {nx : Option Nat} {L : List Nat} {cur : Nat} {R : List Nat}
    (ht : tm q cur = some ⟨w + 1, Dir.R, nx⟩) :
    step tm (mkCfgR (some q) L (cur :: R)) = some (mkCfgR nx ((w + 1) :: L) R) := by
  cases R <;> simp [mkCfgR, step, ht, cons0]

theorem step_mkCfgR_R_nil {tm : TM} {q w : Nat} {nx : Option Nat} {L : List Nat}
    (ht : tm q 0 = some ⟨w + 1, Dir.R, nx⟩) :
    step tm (mkCfgR (some q) L []) = some (mkCfgR nx ((w + 1) :: L) []) := by
  simp [mkCfgR, step, ht, cons0]

theorem step_mkCfgR_L_cons {tm : TM} {q w a cur : Nat} {nx : Option Nat} {L R : List Nat}
    (ht : tm q cur = some ⟨w + 1, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) (a :: L) (cur :: R)) = some (mkCfgR nx L (a :: (w + 1) :: R)) := by
  simp [mkCfgR, step, ht, cons0]

theorem step_mkCfgR_L_nil {tm : TM} {q w cur : Nat} {nx : Option Nat} {R : List Nat}
    (ht : tm q cur = some ⟨w + 1, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) [] (cur :: R)) = some (mkCfgR nx [] (0 :: (w + 1) :: R)) := by
  simp [mkCfgR, step, ht, cons0]

theorem step_mkCfgR_L_nil_zero {tm : TM} {q cur a : Nat} {nx : Option Nat} {R : List Nat}
    (ht : tm q cur = some ⟨0, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) [] (cur :: a :: R)) = some (mkCfgR nx [] (0 :: 0 :: a :: R)) := by
  simp [mkCfgR, step, ht, cons0]

theorem step_mkCfgR_L_cons_zero {tm : TM} {q a cur b : Nat} {nx : Option Nat} {L R : List Nat}
    (ht : tm q cur = some ⟨0, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) (a :: L) (cur :: b :: R)) = some (mkCfgR nx L (a :: 0 :: b :: R)) := by
  simp [mkCfgR, step, ht, cons0]

theorem rep_snoc_one (n s : Nat) (xs : List Nat) :
    rep n s (s :: xs) = s :: rep n s xs := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [rep, ih]

/-! ### Kropitz Core Specification -/

/-- The 3-state Kropitz `f_ω` core transitions on states A=0, B=1, C=2,
    with `B2 = 1L dState` and `dState` agreeing with C on `{0, 2, 3}`. -/
structure KropitzCore (tm : TM) (dState : Nat) : Prop where
  A1 : tm 0 1 = some ⟨3, Dir.L, some 1⟩
  A3 : tm 0 3 = some ⟨2, Dir.R, some 0⟩
  B1 : tm 1 1 = some ⟨3, Dir.R, some 1⟩
  B2 : tm 1 2 = some ⟨1, Dir.L, some dState⟩
  B3 : tm 1 3 = some ⟨2, Dir.R, some 0⟩
  C0 : tm 2 0 = some ⟨3, Dir.R, some 1⟩
  C1 : tm 2 1 = some ⟨1, Dir.L, some 1⟩
  C2 : tm 2 2 = some ⟨3, Dir.L, some 2⟩
  C3 : tm 2 3 = some ⟨2, Dir.R, some 2⟩
  D0 : tm dState 0 = some ⟨3, Dir.R, some 1⟩
  D2 : tm dState 2 = some ⟨3, Dir.L, some 2⟩
  D3 : tm dState 3 = some ⟨2, Dir.R, some 2⟩

/-- Kropitz macro configuration `B(k+1, m) R = 0^∞ 3^(2m+1) 2^(k+1) A> R`. -/
def Bcfg (k m : Nat) (R : List Nat) : Config :=
  mkCfgR (some 0) (rep (k + 1) 2 (rep (2 * m + 1) 3 [])) R

/-- Kropitz mathematical accumulator function `K(k, m)` (0-indexed in `k`: `K 0 m = m + 1`). -/
def Kfn : Nat → Nat → Nat
  | 0, m => m + 1
  | k + 1, m => iter (Kfn k) (2 * m + 2) 0

/-! ### Mathematical Properties of `Kfn` vs Wainer FGH `fFin` -/

theorem Kfn_ge_succ (k m : Nat) : m + 1 ≤ Kfn k m := by
  induction k generalizing m with
  | zero => exact Nat.le_refl (m + 1)
  | succ j ih =>
    have h := iter_ge_add_pos (Kfn j) (fun x _ => ih x) (2 * m + 1) (Kfn j 0) (ih 0)
    have h0 : 1 ≤ Kfn j 0 := ih 0
    have h2 : iter (Kfn j) (2 * m + 2) 0 = iter (Kfn j) (2 * m + 1) (Kfn j 0) := by
      have ha : 2 * m + 2 = (2 * m + 1) + 1 := by omega
      rw [ha, iter_add]; rfl
    rw [Kfn, h2]
    omega

theorem Kfn_mono (k : Nat) {x y : Nat} (hxy : x ≤ y) : Kfn k x ≤ Kfn k y := by
  induction k generalizing x y with
  | zero => exact Nat.add_le_add_right hxy 1
  | succ j ih =>
    show iter (Kfn j) (2 * x + 2) 0 ≤ iter (Kfn j) (2 * y + 2) 0
    have hle : 2 * x + 2 ≤ 2 * y + 2 := by omega
    exact iter_mono_steps (Kfn j) (fun z => Nat.le_trans (Nat.le_succ z) (Kfn_ge_succ j z)) hle 0

theorem Kfn_ge_fFin (k m : Nat) : fFin k m ≤ Kfn k m := by
  induction k generalizing m with
  | zero => exact Nat.le_refl (m + 1)
  | succ j ih =>
    show iter (fFin j) m m ≤ iter (Kfn j) (2 * m + 2) 0
    have hsplit : 2 * m + 2 = m + (m + 2) := by omega
    rw [hsplit, iter_add]
    have hbase : m ≤ iter (Kfn j) (m + 2) 0 := by
      have hg : ∀ n, n ≤ iter (Kfn j) n 0 := by
        intro n
        induction n with
        | zero => exact Nat.le_refl 0
        | succ p ihp =>
          rw [iter_succ]
          exact Nat.le_trans (Nat.add_le_add_right ihp 1) (Kfn_ge_succ j _)
      exact Nat.le_trans (by omega : m ≤ m + 2) (hg (m + 2))
    have hfn : ∀ n x, iter (fFin j) n x ≤ iter (Kfn j) n x := by
      intro n x
      induction n with
      | zero => exact Nat.le_refl x
      | succ p ihp =>
        rw [iter_succ, iter_succ]
        exact Nat.le_trans ((fFin_props j).mono _ _ ihp) (ih _)
    exact Nat.le_trans (hfn m m) (iter_mono_arg (Kfn j) (fun _ _ h => Kfn_mono j h) m hbase)

theorem Kfn_zero_ge (k : Nat) : k + 1 ≤ Kfn k 0 := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ j ih =>
    show j + 2 ≤ Kfn j (Kfn j 0)
    have h := Kfn_ge_succ j (Kfn j 0)
    omega

theorem Kfn_step_k (k m : Nat) : Kfn k m ≤ Kfn (k + 1) m := by
  show Kfn k m ≤ iter (Kfn k) (2 * m + 2) 0
  have hsplit : 2 * m + 2 = 1 + (2 * m + 1) := by omega
  rw [hsplit, iter_add]
  have hbase : m ≤ iter (Kfn k) (2 * m + 1) 0 := by
    have hg : ∀ n, n ≤ iter (Kfn k) n 0 := by
      intro n
      induction n with
      | zero => exact Nat.le_refl 0
      | succ p ihp => rw [iter_succ]; exact Nat.le_trans (Nat.add_le_add_right ihp 1) (Kfn_ge_succ k _)
    exact Nat.le_trans (by omega : m ≤ 2 * m + 1) (hg (2 * m + 1))
  exact Kfn_mono k hbase

theorem Kfn_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (m : Nat) : Kfn k1 m ≤ Kfn k2 m := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Kfn_step_k j m)

section CoreLemmas

variable {tm : TM} {dState : Nat} (hc : KropitzCore tm dState)
include hc

theorem loop_B1 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) L (rep n 1 R)) (mkCfgR (some 1) (rep n 3 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 1) (3 :: L) (rep k 1 R)) :=
      step_mkCfgR_R hc.B1
    have h2 := ih (3 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem loop_A3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 0) L (rep n 3 R)) (mkCfgR (some 0) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 0) L (3 :: rep k 3 R)) =
              some (mkCfgR (some 0) (2 :: L) (rep k 3 R)) :=
      step_mkCfgR_R hc.A3
    have h2 := ih (2 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem loop_C3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 2) L (rep n 3 R)) (mkCfgR (some 2) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 2) L (3 :: rep k 3 R)) =
              some (mkCfgR (some 2) (2 :: L) (rep k 3 R)) :=
      step_mkCfgR_R hc.C3
    have h2 := ih (2 :: L)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem loop_C2 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 2) (rep n 2 L) (2 :: R))
               (mkCfgR (some 2) L (2 :: rep n 3 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 2) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 2) (rep k 2 L) (2 :: 3 :: R)) :=
      step_mkCfgR_L_cons hc.C2
    have h2 := ih (3 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ tm k _ _ _ h1 h2

theorem step_B2_3 (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (3 :: L) (2 :: R)) (mkCfgR (some 1) L (2 :: 1 :: R)) 3 := by
  refine steps_succ tm 2 _ _ _ (step_mkCfgR_L_cons hc.B2) ?_
  refine steps_succ tm 1 _ _ _ (step_mkCfgR_R hc.D3) ?_
  exact steps_one tm _ _ (step_mkCfgR_L_cons hc.C1)

theorem loop_B2_3 (j : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep j 3 L) (2 :: R))
               (mkCfgR (some 1) L (2 :: rep j 1 R)) (3 * j) := by
  induction j generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 := step_B2_3 hc (rep k 3 L) R
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    have h := reaches_trans h1 h2
    have ht : 3 + 3 * k = 3 * (k + 1) := by omega
    rw [ht] at h
    exact h

theorem step_B2_2k (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 (3 :: L)) (2 :: R))
               (mkCfgR (some 1) (rep (k + 1) 2 L) (2 :: 1 :: R)) (2 * k + 5) := by
  have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 (3 :: L)) (2 :: R)) =
            some (mkCfgR (some dState) (rep k 2 (3 :: L)) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons hc.B2
  cases k with
  | zero =>
    have h2 : step tm (mkCfgR (some dState) (3 :: L) (2 :: 1 :: R)) =
              some (mkCfgR (some 2) L (3 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.D2
    have h3 : Reaches tm (mkCfgR (some 2) L (rep 2 3 (1 :: R)))
                         (mkCfgR (some 2) (rep 2 2 L) (1 :: R)) 2 :=
      loop_C3 hc 2 L (1 :: R)
    have h4 : step tm (mkCfgR (some 2) (2 :: 2 :: L) (1 :: R)) =
              some (mkCfgR (some 1) (2 :: L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.C1
    have h34 := reaches_trans h3 (steps_one tm _ _ h4)
    exact steps_succ tm 4 _ _ _ h1 (steps_succ tm 3 _ _ _ h2 h34)
  | succ k' =>
    have h2 : step tm (mkCfgR (some dState) (2 :: rep k' 2 (3 :: L)) (2 :: 1 :: R)) =
              some (mkCfgR (some 2) (rep k' 2 (3 :: L)) (2 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.D2
    have h3 : Reaches tm (mkCfgR (some 2) (rep k' 2 (3 :: L)) (2 :: 3 :: 1 :: R))
                         (mkCfgR (some 2) (3 :: L) (2 :: rep k' 3 (3 :: 1 :: R))) k' :=
      loop_C2 hc k' (3 :: L) (3 :: 1 :: R)
    have h4 : step tm (mkCfgR (some 2) (3 :: L) (2 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 2) L (3 :: 3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_L_cons hc.C2
    have h5 : Reaches tm (mkCfgR (some 2) L (rep (k' + 3) 3 (1 :: R)))
                         (mkCfgR (some 2) (rep (k' + 3) 2 L) (1 :: R)) (k' + 3) :=
      loop_C3 hc (k' + 3) L (1 :: R)
    have h6 : step tm (mkCfgR (some 2) (2 :: rep (k' + 2) 2 L) (1 :: R)) =
              some (mkCfgR (some 1) (rep (k' + 2) 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.C1
    have hrep : 3 :: 3 :: rep k' 3 (3 :: 1 :: R) = rep (k' + 3) 3 (1 :: R) := by
      rw [rep_snoc_one]; rfl
    rw [hrep] at h4
    have h456 := steps_succ tm ((k' + 3) + 1) _ _ _ h4 (reaches_trans h5 (steps_one tm _ _ h6))
    have h36 := reaches_trans h3 h456
    have hall := steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 h36)
    have ht : k' + ((k' + 3) + 1 + 1) + 1 + 1 = 2 * (k' + 1) + 5 := by omega
    rw [ht] at hall
    exact hall

theorem loop_B2_2k (k j : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 (rep j 3 L)) (2 :: R))
               (mkCfgR (some 1) (rep (k + 1) 2 L) (2 :: rep j 1 R)) ((2 * k + 5) * j) := by
  induction j generalizing R with
  | zero => exact reaches_zero tm _
  | succ m ih =>
    have h1 := step_B2_2k hc k (rep m 3 L) R
    have h2 := ih (1 :: R)
    rw [rep_snoc_one] at h2
    have h := reaches_trans h1 h2
    have ht : 2 * k + 5 + (2 * k + 5) * m = (2 * k + 5) * (m + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [ht] at h
    exact h

theorem bounce_B_nil (n : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) [] (2 :: rep n 1 R))
               (mkCfgR (some 1) (rep (n + 2) 3 []) R) (n + 3) := by
  have h1 : step tm (mkCfgR (some 1) [] (2 :: rep n 1 R)) =
            some (mkCfgR (some dState) [] (0 :: 1 :: rep n 1 R)) :=
    step_mkCfgR_L_nil hc.B2
  have h2 : step tm (mkCfgR (some dState) [] (0 :: 1 :: rep n 1 R)) =
            some (mkCfgR (some 1) [3] (rep (n + 1) 1 R)) :=
    step_mkCfgR_R hc.D0
  have h3 := loop_B1 hc (n + 1) [3] R
  have hrep : rep (n + 1) 3 [3] = rep (n + 2) 3 [] := by
    rw [rep_snoc_one]; rfl
  rw [hrep] at h3
  exact steps_succ tm (n + 2) _ _ _ h1 (steps_succ tm (n + 1) _ _ _ h2 h3)

theorem bounce_B_2k_nil (k : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 []) (2 :: R))
               (mkCfgR (some 0) (rep (k + 1) 2 [3]) (1 :: R)) (2 * k + 4) := by
  have h1 : step tm (mkCfgR (some 1) (2 :: rep k 2 []) (2 :: R)) =
            some (mkCfgR (some dState) (rep k 2 []) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons hc.B2
  cases k with
  | zero =>
    have h2 : step tm (mkCfgR (some dState) [] (2 :: 1 :: R)) =
              some (mkCfgR (some 2) [] (0 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_nil hc.D2
    have h3 : step tm (mkCfgR (some 2) [] (0 :: 3 :: 1 :: R)) =
              some (mkCfgR (some 1) [3] (3 :: 1 :: R)) :=
      step_mkCfgR_R hc.C0
    have h4 : step tm (mkCfgR (some 1) [3] (3 :: 1 :: R)) =
              some (mkCfgR (some 0) [2, 3] (1 :: R)) :=
      step_mkCfgR_R hc.B3
    exact steps_succ tm 3 _ _ _ h1
      (steps_succ tm 2 _ _ _ h2 (steps_succ tm 1 _ _ _ h3 (steps_one tm _ _ h4)))
  | succ k' =>
    have h2 : step tm (mkCfgR (some dState) (2 :: rep k' 2 []) (2 :: 1 :: R)) =
              some (mkCfgR (some 2) (rep k' 2 []) (2 :: 3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hc.D2
    have h3 := loop_C2 hc k' [] (3 :: 1 :: R)
    have h4 : step tm (mkCfgR (some 2) [] (2 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 2) [] (0 :: 3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_L_nil hc.C2
    have h5 : step tm (mkCfgR (some 2) [] (0 :: 3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 1) [3] (3 :: rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_R hc.C0
    have h6 : step tm (mkCfgR (some 1) [3] (3 :: rep k' 3 (3 :: 1 :: R))) =
              some (mkCfgR (some 0) [2, 3] (rep k' 3 (3 :: 1 :: R))) :=
      step_mkCfgR_R hc.B3
    have h7 := loop_A3 hc (k' + 1) [2, 3] (1 :: R)
    have hrepR : rep k' 3 (3 :: 1 :: R) = rep (k' + 1) 3 (1 :: R) := by
      rw [rep_snoc_one]; rfl
    have hrepL : rep (k' + 1) 2 [2, 3] = rep (k' + 2) 2 [3] := by
      rw [rep_snoc_one]; rfl
    rw [hrepR] at h3 h4 h5 h6
    rw [hrepL] at h7
    have h47 := steps_succ tm _ _ _ _ h4
      (steps_succ tm _ _ _ _ h5 (steps_succ tm _ _ _ _ h6 h7))
    have h37 := reaches_trans h3 h47
    have hall := steps_succ tm _ _ _ _ h1 (steps_succ tm _ _ _ _ h2 h37)
    have ht : k' + (k' + 1 + 1 + 1 + 1) + 1 + 1 = 2 * (k' + 1) + 4 := by omega
    rw [ht] at hall
    exact hall

/-- Combined sweep + bounce for `B(1, m)` from `mkCfgR (some 1) (rep (2m+1) 3 []) (2 :: R)`. -/
theorem kropitz_level0_from_B (m : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (2 * m + 1) 3 []) (2 :: R))
               (mkCfgR (some 1) (rep (2 * m + 3) 3 []) R) (8 * m + 7) := by
  have h1 := loop_B2_3 hc (2 * m + 1) [] R
  have h2 := bounce_B_nil hc (2 * m + 1) R
  have h := reaches_trans h1 h2
  have ht : 3 * (2 * m + 1) + (2 * m + 1 + 3) = 8 * m + 7 := by omega
  have hm : 2 * m + 1 + 2 = 2 * m + 3 := by omega
  rw [ht, hm] at h
  exact h

/-- Combined sweep + bounce for `B(k+2, m)` from `mkCfgR (some 1) (rep (k+1) 2 (rep (2m+1) 3 [])) (2 :: R)`. -/
theorem kropitz_levelS_from_B (k m : Nat) (R : List Nat) :
    Reaches tm (mkCfgR (some 1) (rep (k + 1) 2 (rep (2 * m + 1) 3 [])) (2 :: R))
               (Bcfg k 0 (rep (2 * m + 2) 1 R)) ((2 * k + 5) * (2 * m + 1) + (2 * k + 4)) := by
  have h1 := loop_B2_2k hc k (2 * m + 1) [] R
  have h2 := bounce_B_2k_nil hc k (rep (2 * m + 1) 1 R)
  have h := reaches_trans h1 h2
  have hrep : 1 :: rep (2 * m + 1) 1 R = rep (2 * m + 2) 1 R := rfl
  rw [hrep] at h
  exact h

/-- Rule K1: `B(1, m) 1 R  --[8m+9]-->  B(1, m+1) R`. -/
theorem kropitz_K1 (m : Nat) (R : List Nat) :
    Reaches tm (Bcfg 0 m (1 :: R)) (Bcfg 0 (m + 1) R) (8 * m + 9) := by
  have h1 : step tm (Bcfg 0 m (1 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + 1) 3 []) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.A1
  have h2 := kropitz_level0_from_B hc m (3 :: R)
  have h3 : step tm (mkCfgR (some 1) (rep (2 * m + 3) 3 []) (3 :: R)) =
            some (Bcfg 0 (m + 1) R) := by
    have hm : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    unfold Bcfg; rw [hm]
    exact step_mkCfgR_R hc.B3
  have h23 := reaches_trans h2 (steps_one tm _ _ h3)
  exact steps_succ tm (8 * m + 8) _ _ _ h1 h23

/-- Rule K2: `B(k+2, m) 1 R  -->  B(k+1, 0) 1^(2m+2) 3 R`. -/
theorem kropitz_K2 (k m : Nat) (R : List Nat) :
    Reaches tm (Bcfg (k + 1) m (1 :: R))
               (Bcfg k 0 (rep (2 * m + 2) 1 (3 :: R)))
               ((2 * k + 5) * (2 * m + 1) + (2 * k + 5)) := by
  have h1 : step tm (Bcfg (k + 1) m (1 :: R)) =
            some (mkCfgR (some 1) (rep (k + 1) 2 (rep (2 * m + 1) 3 [])) (2 :: 3 :: R)) :=
    step_mkCfgR_L_cons hc.A1
  have h2 := kropitz_levelS_from_B hc k m (3 :: R)
  exact steps_succ tm _ _ _ _ h1 h2

/-- Main Kropitz `f_ω` Engine Theorem:
    For every level `k` and accumulator `m`, `B(k+1, m) 1 R` transitions to `B(k+1, Kfn k m) R`
    in some positive step count `t ≥ 1`. -/
theorem kropitz_step (k : Nat) :
    ∀ m R, ∃ t, Reaches tm (Bcfg k m (1 :: R)) (Bcfg k (Kfn k m) R) t ∧ 1 ≤ t := by
  induction k with
  | zero =>
    intro m R
    exact ⟨8 * m + 9, kropitz_K1 hc m R, by omega⟩
  | succ j ih =>
    have hiter : ∀ n m R, ∃ t, Reaches tm (Bcfg j m (rep n 1 R)) (Bcfg j (iter (Kfn j) n m) R) t := by
      intro n
      induction n with
      | zero => intro m R; exact ⟨0, reaches_zero tm _⟩
      | succ p ihp =>
        intro m R
        obtain ⟨t1, h1, _⟩ := ih m (rep p 1 R)
        obtain ⟨t2, h2⟩ := ihp (Kfn j m) R
        have hcomm : iter (Kfn j) p (Kfn j m) = iter (Kfn j) (p + 1) m := by
          have ha : p + 1 = p + 1 := rfl
          rw [iter_add]; rfl
        rw [hcomm] at h2
        exact ⟨t1 + t2, reaches_trans h1 h2⟩
    intro m R
    have h1 := kropitz_K2 hc j m R
    obtain ⟨t2, h2⟩ := hiter (2 * m + 2) 0 (3 :: R)
    have h3 : step tm (Bcfg j (Kfn (j + 1) m) (3 :: R)) =
              some (Bcfg (j + 1) (Kfn (j + 1) m) R) :=
      step_mkCfgR_R hc.A3
    have h12 := reaches_trans h1 h2
    have h123 := reaches_trans h12 (steps_one tm _ _ h3)
    exact ⟨_, h123, by omega⟩

theorem kropitz_rep (k n : Nat) :
    ∀ m R, ∃ t, Reaches tm (Bcfg k m (rep n 1 R)) (Bcfg k (iter (Kfn k) n m) R) t := by
  induction n with
  | zero => intro m R; exact ⟨0, reaches_zero tm _⟩
  | succ p ihp =>
    intro m R
    obtain ⟨t1, h1, _⟩ := kropitz_step hc k m (rep p 1 R)
    obtain ⟨t2, h2⟩ := ihp (Kfn k m) R
    have hcomm : iter (Kfn k) p (Kfn k m) = iter (Kfn k) (p + 1) m := by
      rw [iter_add]; rfl
    rw [hcomm] at h2
    exact ⟨t1 + t2, reaches_trans h1 h2⟩

end CoreLemmas
end BB
