/-
  BB/Jacobzheng.lean
  Reusable, axiom-free Lean 4 library for the 15-state Jacobzheng Busy Beaver
  f_{ω×2} engine (shared by BB18_2, BB19_2, and BB20_2).

  Engine states:
    A(0), B(1), C(2), D(3), E(4), F(5), G(6), H(7), I(8),
    M(12), N(13), O(14), P(15), Q(16), R(17),
    plus exit-loop transitions J1=(9,1)->0RK, K1=(10,1)->1RL, L1=(11,1)->1RJ.
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.JZMath

namespace BB
set_option linter.unusedSimpArgs false

/-- Shared 15-state Jacobzheng `f_{ω×2}` engine plus the 3 exit-loop transitions. -/
structure JZEngine (tm : TM) : Prop where
  A0 : tm 0  0 = some ⟨1, Dir.L, some 1⟩
  A1 : tm 0  1 = some ⟨0, Dir.L, some 12⟩
  B0 : tm 1  0 = some ⟨1, Dir.R, some 2⟩
  B1 : tm 1  1 = some ⟨1, Dir.R, some 13⟩
  C0 : tm 2  0 = some ⟨1, Dir.R, some 3⟩
  C1 : tm 2  1 = some ⟨1, Dir.R, some 2⟩
  D0 : tm 3  0 = some ⟨0, Dir.L, some 4⟩
  D1 : tm 3  1 = some ⟨1, Dir.R, some 16⟩
  E0 : tm 4  0 = some ⟨1, Dir.L, some 5⟩
  E1 : tm 4  1 = some ⟨1, Dir.L, some 4⟩
  F0 : tm 5  0 = some ⟨0, Dir.L, some 6⟩
  F1 : tm 5  1 = some ⟨1, Dir.L, some 4⟩
  G0 : tm 6  0 = some ⟨1, Dir.R, some 7⟩
  G1 : tm 6  1 = some ⟨1, Dir.R, some 8⟩
  H0 : tm 7  0 = some ⟨0, Dir.R, some 7⟩
  H1 : tm 7  1 = some ⟨0, Dir.R, some 2⟩
  I0 : tm 8  0 = some ⟨0, Dir.R, some 9⟩
  I1 : tm 8  1 = some ⟨1, Dir.R, some 7⟩
  J1 : tm 9  1 = some ⟨0, Dir.R, some 10⟩
  K1 : tm 10 1 = some ⟨1, Dir.R, some 11⟩
  L1 : tm 11 1 = some ⟨1, Dir.R, some 9⟩
  M0 : tm 12 0 = some ⟨1, Dir.L, some 0⟩
  M1 : tm 12 1 = some ⟨1, Dir.L, some 12⟩
  N0 : tm 13 0 = some ⟨0, Dir.L, some 0⟩
  N1 : tm 13 1 = some ⟨0, Dir.R, some 14⟩
  O0 : tm 14 0 = some ⟨0, Dir.L, some 2⟩
  O1 : tm 14 1 = some ⟨1, Dir.R, some 15⟩
  P0 : tm 15 0 = some ⟨0, Dir.L, some 0⟩
  P1 : tm 15 1 = some ⟨1, Dir.R, some 13⟩
  Q0 : tm 16 0 = some ⟨0, Dir.L, some 17⟩
  Q1 : tm 16 1 = some ⟨1, Dir.L, some 0⟩
  R0 : tm 17 0 = some ⟨0, Dir.R, some 8⟩
  R1 : tm 17 1 = some ⟨1, Dir.L, some 17⟩

/-! ### Tape Representation & Macro Configurations -/

def rep01 : Nat → List Nat → List Nat
  | 0, tail => tail
  | m + 1, tail => 0 :: 1 :: rep01 m tail

def rep10 : Nat → List Nat → List Nat
  | 0, tail => tail
  | m + 1, tail => 1 :: 0 :: rep10 m tail

def rep110 : Nat → List Nat → List Nat
  | 0, tail => tail
  | k + 1, tail => 1 :: 1 :: 0 :: rep110 k tail

def rep101 : Nat → List Nat → List Nat
  | 0, tail => tail
  | k + 1, tail => 1 :: 0 :: 1 :: rep101 k tail

def rl : List Nat → List Nat → List Nat
  | [], R => R
  | a :: xs, R => rep a 1 (cons0 0 (rl xs R))

theorem rep01_zero_unfold (m a : Nat) (tail : List Nat) :
    rep01 m (0 :: a :: tail) = 0 :: rep10 m (a :: tail) := by
  induction m with
  | zero => rfl
  | succ k ih => simp [rep01, rep10, ih]

theorem rep01_snoc (m : Nat) (R : List Nat) :
    rep01 m (0 :: 1 :: R) = rep01 (m + 1) R := by
  induction m with
  | zero => rfl
  | succ k ih => simp [rep01, ih]

theorem one_rep01_eq_rep10 (m : Nat) (R : List Nat) :
    1 :: rep01 m R = rep10 m (1 :: R) := by
  induction m with
  | zero => rfl
  | succ k ih => simp [rep01, rep10, ih]

theorem rep110_snoc (k : Nat) (L : List Nat) :
    rep110 k (1 :: 1 :: 0 :: L) = rep110 (k + 1) L := by
  induction k with
  | zero => rfl
  | succ p ih => simp [rep110, ih]

theorem rep101_snoc (k : Nat) (R : List Nat) :
    rep101 k (1 :: 0 :: 1 :: R) = rep101 (k + 1) R := by
  induction k with
  | zero => rfl
  | succ p ih => simp [rep101, ih]

theorem cons0_ne_nil (x : Nat) {ys : List Nat} (h : ys ≠ []) : cons0 x ys = x :: ys := by
  cases ys with
  | nil => contradiction
  | cons _ _ => simp [cons0]

theorem rl_ne_nil (xs : List Nat) {a : Nat} {R : List Nat} : rl xs (a :: R) ≠ [] := by
  induction xs with
  | nil => simp [rl]
  | cons b xs' ih =>
    cases b with
    | zero => rw [rl, rep, cons0_ne_nil 0 ih]; simp
    | succ k => simp [rl, rep]

theorem one_rep101_eq_rl (q a : Nat) (R : List Nat) :
    1 :: rep101 q (a :: R) = rl (rep q 2 []) (1 :: a :: R) := by
  induction q with
  | zero => rfl
  | succ k ih =>
    have hne : rl (rep k 2 []) (1 :: a :: R) ≠ [] := rl_ne_nil _
    change 1 :: 1 :: 0 :: (1 :: rep101 k (a :: R)) =
           1 :: 1 :: cons0 0 (rl (rep k 2 []) (1 :: a :: R))
    rw [ih, cons0_ne_nil 0 hne]

theorem rl_rep_one (m a : Nat) (R : List Nat) :
    rep10 m (a :: R) = rl (rep m 1 []) (a :: R) := by
  induction m generalizing a R with
  | zero => rfl
  | succ k ih =>
    change 1 :: 0 :: rep10 k (a :: R) = 1 :: cons0 0 (rl (rep k 1 []) (a :: R))
    rw [← ih a R, cons0_ne_nil 0 (by cases k <;> simp [rep10])]

theorem rl_append (xs ys : List Nat) {a : Nat} {R : List Nat} :
    rl (xs ++ ys) (a :: R) = rl xs (rl ys (a :: R)) := by
  induction xs with
  | nil => rfl
  | cons b xs' ih =>
    simp only [List.cons_append, rl, ih]

theorem rep_add_sym (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ k ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem rep_snoc_sym (k s : Nat) (L : List Nat) :
    rep k s (s :: L) = rep (k + 1) s L := by
  have h := rep_add_sym k 1 s L
  simpa [rep] using h

theorem rep_append_single (k s : Nat) : rep k s [] ++ [s] = s :: rep k s [] := by
  induction k with
  | zero => rfl
  | succ p ih => simp [rep, ih]

theorem rep_append_sym (k s : Nat) (tail : List Nat) :
    rep k s tail = rep k s [] ++ tail := by
  induction k with
  | zero => rfl
  | succ p ih => simp [rep, ih]

theorem mkCfgR_zero_eq_cons0 (st : Option Nat) (L R : List Nat) :
    mkCfgR st L (0 :: R) = mkCfgR st L (cons0 0 R) := by
  cases R <;> simp [cons0, mkCfgR]

theorem step_R_cons {tm : TM} {q cur w : Nat} {nx : Option Nat} {L R : List Nat}
    (ht : tm q cur = some ⟨w, Dir.R, nx⟩) :
    step tm (mkCfgR (some q) L (cur :: R)) = some (mkCfgR nx (cons0 w L) R) := by
  cases R <;> simp [step, mkCfgR, ht]

theorem step_R_zero {tm : TM} {q w : Nat} {nx : Option Nat} {L R : List Nat}
    (ht : tm q 0 = some ⟨w, Dir.R, nx⟩) :
    step tm (mkCfgR (some q) L (cons0 0 R)) = some (mkCfgR nx (cons0 w L) R) := by
  cases R <;> simp [step, mkCfgR, cons0, ht]

theorem step_L_cons {tm : TM} {q cur w : Nat} {nx : Option Nat} {a : Nat} {L R : List Nat}
    (ht : tm q cur = some ⟨w, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) (a :: L) (cur :: R)) = some (mkCfgR nx L (a :: cons0 w R)) := by
  simp [step, mkCfgR, ht]

theorem step_L_zero_cons {tm : TM} {q w : Nat} {nx : Option Nat} {a : Nat} {L R : List Nat}
    (ht : tm q 0 = some ⟨w, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) (a :: L) (cons0 0 R)) = some (mkCfgR nx L (a :: cons0 w R)) := by
  cases R <;> simp [step, mkCfgR, cons0, ht]

theorem step_L_nil {tm : TM} {q cur w : Nat} {nx : Option Nat} {R : List Nat}
    (ht : tm q cur = some ⟨w, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) [] (cur :: R)) = some (mkCfgR nx [] (0 :: cons0 w R)) := by
  simp [step, mkCfgR, ht]

theorem step_L_zero_nil {tm : TM} {q w : Nat} {nx : Option Nat} {R : List Nat}
    (ht : tm q 0 = some ⟨w, Dir.L, nx⟩) :
    step tm (mkCfgR (some q) [] (cons0 0 R)) = some (mkCfgR nx [] (0 :: cons0 w R)) := by
  cases R <;> simp [step, mkCfgR, cons0, ht]

/-- Macro configurations `CI`, `SW`, `CO`, `EX`. -/
def CI (n : Nat) (R : List Nat) : Config :=
  mkCfgR (some 2) (rep n 1 []) (cons0 0 R)

def SW (m n : Nat) (R : List Nat) : Config :=
  mkCfgR (some 2) (rep n 1 (rep01 m [0, 1])) (cons0 0 R)

def CO (m n : Nat) (R : List Nat) : Config :=
  mkCfgR (some 2) (rep n 1 (rep01 m [0, 0, 1])) (cons0 0 R)

def EX (n : Nat) (R : List Nat) : Config :=
  mkCfgR (some 9) [0, 1] (rep n 1 (cons0 0 R))

/-- Existential reachability helper (steps discarded for intermediate phases). -/
def CanReach (tm : TM) (c1 c2 : Config) : Prop :=
  ∃ t, Reaches tm c1 c2 t

theorem canReach_refl (tm : TM) (c : Config) : CanReach tm c c :=
  ⟨0, reaches_zero tm c⟩

theorem canReach_trans {tm : TM} {c1 c2 c3 : Config}
    (h1 : CanReach tm c1 c2) (h2 : CanReach tm c2 c3) : CanReach tm c1 c3 :=
  let ⟨t1, r1⟩ := h1
  let ⟨t2, r2⟩ := h2
  ⟨t1 + t2, reaches_trans r1 r2⟩

theorem reaches_one {tm : TM} {c1 c2 : Config} (h : step tm c1 = some c2) :
    Reaches tm c1 c2 1 := by
  show steps tm 1 c1 = some c2
  simp [steps, h]

theorem canReach_step {tm : TM} {c1 c2 c3 : Config}
    (h1 : step tm c1 = some c2) (h2 : CanReach tm c2 c3) : CanReach tm c1 c3 :=
  let ⟨t, r⟩ := h2
  ⟨1 + t, reaches_trans (reaches_one h1) r⟩

theorem iter_add_one (g : Nat → Nat) (k x : Nat) :
    iter g k (g x) = iter g (k + 1) x := by
  have h := iter_add g k 1 x
  simpa [iter] using h.symm

/-! ### Core Micro-Loops & Boot -/

section EngineLemmas

variable {tm : TM} (he : JZEngine tm)
include he

theorem jz_boot : Reaches tm initConfig (EX 5 []) 26 := by
  have h1 : Reaches tm initConfig (mkCfgR (some 2) [0, 0, 1] [1, 1, 1]) 13 := by
    show steps tm 13 initConfig = some (mkCfgR (some 2) [0, 0, 1] [1, 1, 1])
    simp [initConfig, steps, step, cons0, mkCfgR,
      he.A0, he.B0, he.C0, he.C1, he.D0, he.E0, he.E1, he.F0, he.G0, he.H0, he.H1]
  have h2 : Reaches tm (mkCfgR (some 2) [0, 0, 1] [1, 1, 1]) (EX 5 []) 13 := by
    show steps tm 13 (mkCfgR (some 2) [0, 0, 1] [1, 1, 1]) = some (EX 5 [])
    simp [EX, rep, steps, step, cons0, mkCfgR,
      he.C0, he.C1, he.D0, he.E0, he.E1, he.F0, he.G1, he.I0]
  exact reaches_trans h1 h2

theorem jz_triJKL (k a : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 9) (a :: L) (rep (3 * k) 1 R))
               (mkCfgR (some 9) (rep110 k (a :: L)) R) (3 * k) := by
  induction k generalizing a L with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have heq : 3 * (p + 1) = 3 + 3 * p := by omega
    rw [heq, ← rep_add_sym 3 (3 * p) 1 R]
    have h1 := reaches_one (step_R_cons (L := a :: L) (R := 1 :: 1 :: rep (3 * p) 1 R) he.J1)
    have h2 := reaches_one (step_R_cons (L := 0 :: a :: L) (R := 1 :: rep (3 * p) 1 R) he.K1)
    have h3 := reaches_one (step_R_cons (L := 1 :: 0 :: a :: L) (R := rep (3 * p) 1 R) he.L1)
    simp only [cons0] at h1 h2 h3
    have hstep : Reaches tm (mkCfgR (some 9) (a :: L) (rep 3 1 (rep (3 * p) 1 R)))
                            (mkCfgR (some 9) (1 :: 1 :: 0 :: a :: L) (rep (3 * p) 1 R)) 3 :=
      reaches_trans (reaches_trans h1 h2) h3
    have hrest := ih 1 (1 :: 0 :: a :: L)
    rw [rep110_snoc] at hrest
    exact reaches_trans hstep hrest

theorem loop_C1 (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 2) L (rep k 1 R))
               (mkCfgR (some 2) (rep k 1 L) R) k := by
  induction k generalizing L with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_R_cons (L := L) (R := rep p 1 R) he.C1)
    simp only [cons0_succ] at h1
    have hrest := ih (1 :: L)
    rw [rep_snoc_sym] at hrest
    simpa [rep, Nat.add_comm] using reaches_trans h1 hrest

theorem loop_E1 (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) (rep k 1 L) (1 :: R))
               (mkCfgR (some 4) L (rep k 1 (1 :: R))) k := by
  induction k generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := rep p 1 L) (R := R) he.E1)
    simp only [cons0_succ] at h1
    have hrest := ih (1 :: R)
    rw [rep_snoc_sym] at hrest
    simpa [rep, Nat.add_comm] using reaches_trans h1 hrest

theorem loop_M1 (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 12) (rep k 1 L) (1 :: R))
               (mkCfgR (some 12) L (rep k 1 (1 :: R))) k := by
  induction k generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := rep p 1 L) (R := R) he.M1)
    simp only [cons0_succ] at h1
    have hrest := ih (1 :: R)
    rw [rep_snoc_sym] at hrest
    simpa [rep, Nat.add_comm] using reaches_trans h1 hrest

theorem loop_R1 (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 17) (rep k 1 L) (1 :: R))
               (mkCfgR (some 17) L (rep k 1 (1 :: R))) k := by
  induction k generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := rep p 1 L) (R := R) he.R1)
    simp only [cons0_succ] at h1
    have hrest := ih (1 :: R)
    rw [rep_snoc_sym] at hrest
    simpa [rep, Nat.add_comm] using reaches_trans h1 hrest

theorem loop_EF_10 (m : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) (rep10 m L) (0 :: R))
               (mkCfgR (some 4) L (0 :: rep (2 * m) 1 R)) (2 * m) := by
  induction m generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := 0 :: rep10 p L) (R := R) he.E0)
    have h2 := reaches_one (step_L_cons (a := 0) (L := rep10 p L) (R := 1 :: R) he.F1)
    simp only [cons0_succ] at h1 h2
    have hstep := reaches_trans h1 h2
    have hrest := ih (1 :: 1 :: R)
    have hr : rep (2 * p) 1 (1 :: 1 :: R) = rep (2 * (p + 1)) 1 R := by
      rw [rep_snoc_sym, rep_snoc_sym, show 2 * p + 1 + 1 = 2 * (p + 1) by omega]
    rw [hr] at hrest
    simpa [rep10, Nat.mul_add, Nat.add_comm] using reaches_trans hstep hrest

theorem loop_EF_110 (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 4) (rep110 k L) (0 :: R))
               (mkCfgR (some 4) L (0 :: rep (3 * k) 1 R)) (3 * k) := by
  induction k generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 p L) (R := R) he.E0)
    have h2 := reaches_one (step_L_cons (a := 1) (L := 0 :: rep110 p L) (R := 1 :: R) he.F1)
    have h3 := reaches_one (step_L_cons (a := 0) (L := rep110 p L) (R := 1 :: 1 :: R) he.E1)
    simp only [cons0_succ] at h1 h2 h3
    have hstep := reaches_trans (reaches_trans h1 h2) h3
    have hrest := ih (1 :: 1 :: 1 :: R)
    have hr : rep (3 * p) 1 (1 :: 1 :: 1 :: R) = rep (3 * (p + 1)) 1 R := by
      rw [rep_snoc_sym, rep_snoc_sym, rep_snoc_sym, show 3 * p + 1 + 1 + 1 = 3 * (p + 1) by omega]
    rw [hr] at hrest
    simpa [rep110, Nat.mul_add, Nat.add_comm] using reaches_trans hstep hrest

theorem loop_NOP (k a : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 13) (a :: L) (rep (3 * k) 1 R))
               (mkCfgR (some 13) (rep110 k (a :: L)) R) (3 * k) := by
  induction k generalizing a L with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have heq : 3 * (p + 1) = 3 + 3 * p := by omega
    rw [heq, ← rep_add_sym 3 (3 * p) 1 R]
    have h1 := reaches_one (step_R_cons (L := a :: L) (R := 1 :: 1 :: rep (3 * p) 1 R) he.N1)
    have h2 := reaches_one (step_R_cons (L := 0 :: a :: L) (R := 1 :: rep (3 * p) 1 R) he.O1)
    have h3 := reaches_one (step_R_cons (L := 1 :: 0 :: a :: L) (R := rep (3 * p) 1 R) he.P1)
    simp only [cons0_succ, cons0_cons] at h1 h2 h3
    have hstep : Reaches tm (mkCfgR (some 13) (a :: L) (rep 3 1 (rep (3 * p) 1 R)))
                            (mkCfgR (some 13) (1 :: 1 :: 0 :: a :: L) (rep (3 * p) 1 R)) 3 :=
      reaches_trans (reaches_trans h1 h2) h3
    have hrest := ih 1 (1 :: 0 :: a :: L)
    rw [rep110_snoc] at hrest
    exact reaches_trans hstep hrest

theorem jz_M_loop (k : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 12) (rep110 k L) (0 :: R))
               (mkCfgR (some 12) L (0 :: rep101 k R)) (3 * k) := by
  induction k generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 p L) (R := R) he.M0)
    have h2 := reaches_one (step_L_cons (a := 1) (L := 0 :: rep110 p L) (R := 1 :: R) he.A1)
    have h3 := reaches_one (step_L_cons (a := 0) (L := rep110 p L) (R := 0 :: 1 :: R) he.M1)
    simp only [cons0_succ, cons0_cons] at h1 h2 h3
    have hstep := reaches_trans (reaches_trans h1 h2) h3
    have hrest := ih (1 :: 0 :: 1 :: R)
    rw [rep101_snoc] at hrest
    simpa [rep110, Nat.mul_add, Nat.add_comm] using reaches_trans hstep hrest

theorem loop_MA_10 (m : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 12) (rep10 m L) (0 :: R))
               (mkCfgR (some 12) L (0 :: rep01 m R)) (2 * m) := by
  induction m generalizing R with
  | zero => exact reaches_zero tm _
  | succ p ih =>
    have h1 := reaches_one (step_L_cons (a := 1) (L := 0 :: rep10 p L) (R := R) he.M0)
    have h2 := reaches_one (step_L_cons (a := 0) (L := rep10 p L) (R := 1 :: R) he.A1)
    simp only [cons0_succ, cons0_cons] at h1 h2
    have hstep := reaches_trans h1 h2
    have hrest := ih (0 :: 1 :: R)
    rw [rep01_snoc] at hrest
    simpa [rep10, Nat.mul_add, Nat.add_comm] using reaches_trans hstep hrest

/-- Finish from `M` at `[1]` with `0 :: R` -> `CI 3 (1 :: R)` (8 steps). -/
theorem jz_M_finish (R : List Nat) :
    CanReach tm (mkCfgR (some 12) [1] (0 :: R)) (CI 3 (1 :: R)) := by
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := R) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_nil (R := 1 :: R) he.A1)
  simp only [cons0]
  apply canReach_step (step_L_nil (R := 0 :: 1 :: R) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_nil (R := 1 :: 0 :: 1 :: R) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: 0 :: 1 :: R) he.B0)
  simp only [cons0]
  have hc := loop_C1 he 2 [1] (0 :: 1 :: R)
  exact ⟨2, by simpa [CI, rep, cons0] using hc⟩

/-! ### The 12 Core Engine Rules -/

/-- Rule 1: `CI n (cons0 0 R) -> CO 0 (n + 1) R`. -/
theorem rule_CI_0 (n : Nat) (R : List Nat) :
    CanReach tm (CI n (cons0 0 R)) (CO 0 (n + 1) R) := by
  unfold CI
  apply canReach_step (step_R_zero (L := rep n 1 []) (R := cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := rep n 1 []) (R := R) he.D0)
  apply canReach_trans ⟨n, loop_E1 he n [] (cons0 0 R)⟩
  rw [rep_snoc_sym]
  apply canReach_step (step_L_nil (R := rep n 1 (cons0 0 R)) he.E1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_nil (R := 1 :: rep n 1 (cons0 0 R)) he.E0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_nil (R := 1 :: 1 :: rep n 1 (cons0 0 R)) he.F0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := []) (R := 0 :: 1 :: 1 :: rep n 1 (cons0 0 R)) he.G0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := [1]) (R := 1 :: 1 :: rep n 1 (cons0 0 R)) he.H0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := [0, 1]) (R := 1 :: rep n 1 (cons0 0 R)) he.H1)
  simp only [cons0_succ, cons0_cons]
  have hc := loop_C1 he (n + 1) [0, 0, 1] (cons0 0 R)
  exact ⟨n + 1, by simpa [CO, rep01, rep] using hc⟩

/-- Rule 2: `SW m n (cons0 0 R) -> CO 0 (n + 2 * m + 3) R`. -/
theorem rule_SW_0 (m n : Nat) (R : List Nat) :
    CanReach tm (SW m n (cons0 0 R)) (CO 0 (n + 2 * m + 3) R) := by
  unfold SW
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 m [0, 1])) (R := cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := rep n 1 (rep01 m [0, 1])) (R := R) he.D0)
  apply canReach_trans ⟨n, loop_E1 he n (rep01 m [0, 1]) (cons0 0 R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 m [1]) (R := rep n 1 (cons0 0 R)) he.E1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_trans ⟨2 * m, loop_EF_10 he m [1] (1 :: rep n 1 (cons0 0 R))⟩
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.E0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_nil (R := 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.F1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_nil (R := 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.E0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_nil (R := 1 :: 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.F0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := []) (R := 0 :: 1 :: 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.G0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := [1]) (R := 1 :: 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.H0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := [0, 1]) (R := 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.H1)
  simp only [cons0_succ, cons0_cons]
  have hr : 1 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R)) =
            rep (n + 2 * m + 3) 1 (cons0 0 R) := by
    rw [rep_snoc_sym, rep_add_sym]
    have e : 2 * m + 1 + n + 2 = n + 2 * m + 3 := by omega
    rw [← e]; rfl
  rw [hr]
  have hc := loop_C1 he (n + 2 * m + 3) [0, 0, 1] (cons0 0 R)
  exact ⟨n + 2 * m + 3, by simpa [CO, rep01] using hc⟩

/-- Rule 3: `CO m n (cons0 0 R) -> EX (n + 2 * m + 2) R`. -/
theorem rule_CO_0 (m n : Nat) (R : List Nat) :
    CanReach tm (CO m n (cons0 0 R)) (EX (n + 2 * m + 2) R) := by
  unfold CO
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 m [0, 0, 1])) (R := cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := rep n 1 (rep01 m [0, 0, 1])) (R := R) he.D0)
  apply canReach_trans ⟨n, loop_E1 he n (rep01 m [0, 0, 1]) (cons0 0 R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 m [0, 1]) (R := rep n 1 (cons0 0 R)) he.E1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_trans ⟨2 * m, loop_EF_10 he m [0, 1] (1 :: rep n 1 (cons0 0 R))⟩
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.E0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.F0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := []) (R := 0 :: 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.G1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := [1]) (R := 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R))) he.I0)
  simp only [cons0_succ, cons0_cons]
  have hr : 1 :: rep (2 * m) 1 (1 :: rep n 1 (cons0 0 R)) =
            rep (n + 2 * m + 2) 1 (cons0 0 R) := by
    rw [rep_snoc_sym, rep_add_sym]
    have e : 2 * m + 1 + n + 1 = n + 2 * m + 2 := by omega
    rw [← e]; rfl
  rw [hr]
  exact canReach_refl tm (EX (n + 2 * m + 2) R)

/-- Rule 4: `CI n (1 :: cons0 0 R) -> SW 0 n R`. -/
theorem rule_CI_10 (n : Nat) (R : List Nat) :
    CanReach tm (CI n (1 :: cons0 0 R)) (SW 0 n R) := by
  unfold CI
  apply canReach_step (step_R_zero (L := rep n 1 []) (R := 1 :: cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 []) (R := cons0 0 R) he.D1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := 1 :: rep n 1 []) (R := R) he.Q0)
  apply canReach_trans ⟨n + 1, loop_R1 he (n + 1) [] (cons0 0 R)⟩
  rw [rep_snoc_sym]
  apply canReach_step (step_L_nil (R := rep (n + 1) 1 (cons0 0 R)) he.R1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: rep (n + 1) 1 (cons0 0 R)) he.R0)
  simp only [cons0_zero_nil]
  apply canReach_step (step_R_cons (L := []) (R := rep (n + 1) 1 (cons0 0 R)) he.I1)
  simp only [cons0_succ, cons0_cons, rep]
  apply canReach_step (step_R_cons (L := [1]) (R := rep n 1 (cons0 0 R)) he.H1)
  simp only [cons0_succ, cons0_cons]
  have hc := loop_C1 he n [0, 1] (cons0 0 R)
  exact ⟨n, by simpa [SW, rep01] using hc⟩

/-- Rule 5: `SW m n (1 :: cons0 0 R) -> SW (m + 1) n R`. -/
theorem rule_SW_10 (m n : Nat) (R : List Nat) :
    CanReach tm (SW m n (1 :: cons0 0 R)) (SW (m + 1) n R) := by
  unfold SW
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 m [0, 1])) (R := 1 :: cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 (rep01 m [0, 1])) (R := cons0 0 R) he.D1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := 1 :: rep n 1 (rep01 m [0, 1])) (R := R) he.Q0)
  apply canReach_trans ⟨n + 1, loop_R1 he (n + 1) (rep01 m [0, 1]) (cons0 0 R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 m [1]) (R := rep (n + 1) 1 (cons0 0 R)) he.R1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := rep10 m [1]) (R := 1 :: rep (n + 1) 1 (cons0 0 R)) he.R0)
  have h0 : cons0 0 (rep10 m [1]) = rep01 m [0, 1] := by
    rw [cons0_ne_nil 0 (by cases m <;> simp [rep10]), ← rep01_zero_unfold]
  rw [h0]
  apply canReach_step (step_R_cons (L := rep01 m [0, 1]) (R := rep (n + 1) 1 (cons0 0 R)) he.I1)
  simp only [cons0_succ, cons0_cons, rep]
  apply canReach_step (step_R_cons (L := 1 :: rep01 m [0, 1]) (R := rep n 1 (cons0 0 R)) he.H1)
  simp only [cons0_succ, cons0_cons]
  have hc := loop_C1 he n (0 :: 1 :: rep01 m [0, 1]) (cons0 0 R)
  exact ⟨n, by simpa [rep01] using hc⟩

/-- Rule 6: `CO m n (1 :: cons0 0 R) -> CO (m + 1) n R`. -/
theorem rule_CO_10 (m n : Nat) (R : List Nat) :
    CanReach tm (CO m n (1 :: cons0 0 R)) (CO (m + 1) n R) := by
  unfold CO
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 m [0, 0, 1])) (R := 1 :: cons0 0 R) he.C0)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 (rep01 m [0, 0, 1])) (R := cons0 0 R) he.D1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_L_zero_cons (a := 1) (L := 1 :: rep n 1 (rep01 m [0, 0, 1])) (R := R) he.Q0)
  apply canReach_trans ⟨n + 1, loop_R1 he (n + 1) (rep01 m [0, 0, 1]) (cons0 0 R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 m [0, 1]) (R := rep (n + 1) 1 (cons0 0 R)) he.R1)
  simp only [cons0_succ, cons0_cons]
  apply canReach_step (step_R_cons (L := rep10 m [0, 1]) (R := 1 :: rep (n + 1) 1 (cons0 0 R)) he.R0)
  have h0 : cons0 0 (rep10 m [0, 1]) = rep01 m [0, 0, 1] := by
    rw [cons0_ne_nil 0 (by cases m <;> simp [rep10]), ← rep01_zero_unfold]
  rw [h0]
  apply canReach_step (step_R_cons (L := rep01 m [0, 0, 1]) (R := rep (n + 1) 1 (cons0 0 R)) he.I1)
  simp only [cons0_succ, cons0_cons, rep]
  apply canReach_step (step_R_cons (L := 1 :: rep01 m [0, 0, 1]) (R := rep n 1 (cons0 0 R)) he.H1)
  simp only [cons0_succ, cons0_cons]
  have hc := loop_C1 he n (0 :: 1 :: rep01 m [0, 0, 1]) (cons0 0 R)
  exact ⟨n, by simpa [rep01] using hc⟩

/-- Rule 7: `CI n (1 :: 1 :: R) -> CI (n + 4) (1 :: R)`. -/
theorem rule_CI_11 (n : Nat) (R : List Nat) :
    CanReach tm (CI n (1 :: 1 :: R)) (CI (n + 4) (1 :: R)) := by
  unfold CI
  apply canReach_step (step_R_zero (L := rep n 1 []) (R := 1 :: 1 :: R) he.C0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 []) (R := 1 :: R) he.D1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: rep n 1 []) (R := R) he.Q1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := rep n 1 []) (R := 1 :: R) he.A1)
  simp only [cons0]
  apply canReach_trans ⟨n, loop_M1 he n [] (0 :: 1 :: R)⟩
  rw [rep_snoc_sym]
  apply canReach_step (step_L_nil (R := rep n 1 (0 :: 1 :: R)) he.M1)
  simp only [cons0]
  apply canReach_step (step_L_nil (R := 1 :: rep n 1 (0 :: 1 :: R)) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_nil (R := 1 :: 1 :: rep n 1 (0 :: 1 :: R)) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: 1 :: rep n 1 (0 :: 1 :: R)) he.B0)
  simp only [cons0]
  have hc := loop_C1 he (n + 3) [1] (0 :: 1 :: R)
  have hr : 1 :: 1 :: 1 :: rep n 1 (0 :: 1 :: R) = rep (n + 3) 1 (0 :: 1 :: R) := by
    have e : 3 + n = n + 3 := by omega
    rw [← e, ← rep_add_sym]; rfl
  rw [hr]
  have hl : rep (n + 3) 1 [1] = rep (n + 4) 1 [] := by
    rw [rep_snoc_sym]
  rw [hl] at hc
  exact ⟨n + 3, by simpa [cons0] using hc⟩

/-- Iterated Rule 7: `CI a (rep (k + 1) 1 R) -> CI (a + 4 * k) (1 :: R)`. -/
theorem rule_CI_11_iter (k a : Nat) (R : List Nat) :
    CanReach tm (CI a (rep (k + 1) 1 R)) (CI (a + 4 * k) (1 :: R)) := by
  induction k generalizing a with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    have h1 : CanReach tm (CI a (1 :: 1 :: rep p 1 R)) (CI (a + 4) (1 :: rep p 1 R)) :=
      rule_CI_11 he a (rep p 1 R)
    have h2 := ih (a + 4)
    have heq : a + 4 + 4 * p = a + 4 * (p + 1) := by omega
    rw [heq] at h2
    exact canReach_trans h1 h2

/-- Iterated Rule 5: `SW m n (rl (rep k 1 []) (a :: R)) -> SW (m + k) n (a :: R)`. -/
theorem rule_SW_10_iter (k m n a : Nat) (R : List Nat) :
    CanReach tm (SW m n (rl (rep k 1 []) (a :: R))) (SW (m + k) n (a :: R)) := by
  induction k generalizing m with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    have h1 : CanReach tm (SW m n (1 :: cons0 0 (rl (rep p 1 []) (a :: R))))
                          (SW (m + 1) n (rl (rep p 1 []) (a :: R))) :=
      rule_SW_10 he m n _
    have h2 := ih (m + 1)
    have heq : m + 1 + p = m + (p + 1) := by omega
    rw [heq] at h2
    exact canReach_trans h1 h2

/-- Iterated Rule 6: `CO m n (rl (rep k 1 []) (a :: R)) -> CO (m + k) n (a :: R)`. -/
theorem rule_CO_10_iter (k m n a : Nat) (R : List Nat) :
    CanReach tm (CO m n (rl (rep k 1 []) (a :: R))) (CO (m + k) n (a :: R)) := by
  induction k generalizing m with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    have h1 : CanReach tm (CO m n (1 :: cons0 0 (rl (rep p 1 []) (a :: R))))
                          (CO (m + 1) n (rl (rep p 1 []) (a :: R))) :=
      rule_CO_10 he m n _
    have h2 := ih (m + 1)
    have heq : m + 1 + p = m + (p + 1) := by omega
    rw [heq] at h2
    exact canReach_trans h1 h2

/-- Rule 8: `SW m n (1 :: 1 :: R) -> CI 3 (rl (rep m 1 []) (rep (n + 2) 1 (0 :: 1 :: R)))`. -/
theorem rule_SW_11_raw (m n : Nat) (R : List Nat) :
    CanReach tm (SW m n (1 :: 1 :: R))
                (CI 3 (rl (rep m 1 []) (rep (n + 2) 1 (0 :: 1 :: R)))) := by
  unfold SW
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 m [0, 1])) (R := 1 :: 1 :: R) he.C0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 (rep01 m [0, 1])) (R := 1 :: R) he.D1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: rep n 1 (rep01 m [0, 1])) (R := R) he.Q1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := rep n 1 (rep01 m [0, 1])) (R := 1 :: R) he.A1)
  simp only [cons0]
  apply canReach_trans ⟨n, loop_M1 he n (rep01 m [0, 1]) (0 :: 1 :: R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 m [1]) (R := rep n 1 (0 :: 1 :: R)) he.M1)
  simp only [cons0]
  apply canReach_trans ⟨2 * m, loop_MA_10 he m [1] (1 :: rep n 1 (0 :: 1 :: R))⟩
  apply canReach_trans (jz_M_finish he (rep01 m (1 :: rep n 1 (0 :: 1 :: R))))
  have hr : 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R)) =
            rl (rep m 1 []) (rep (n + 2) 1 (0 :: 1 :: R)) := by
    rw [one_rep01_eq_rep10, rl_rep_one]
    rfl
  rw [hr]
  exact canReach_refl tm _

/-- `SW` single step: `SW m n (1 :: 1 :: R) -> SW m (h m n) (1 :: R)`. -/
theorem SW_step (m : Nat) :
    ∀ n R, CanReach tm (SW m n (1 :: 1 :: R)) (SW m (h m n) (1 :: R)) := by
  induction m with
  | zero =>
    intro n R
    apply canReach_trans (rule_SW_11_raw he 0 n R)
    simp only [rep, rl]
    apply canReach_trans (rule_CI_11_iter he (n + 1) 3 (0 :: 1 :: R))
    have h4 : 3 + 4 * (n + 1) = h 0 n := by simp [h]; omega
    rw [h4]
    exact rule_CI_10 he (h 0 n) (1 :: R)
  | succ m' ih =>
    intro n R
    apply canReach_trans (rule_SW_11_raw he (m' + 1) n R)
    have hstep1 : CanReach tm
        (CI 3 (1 :: cons0 0 (rl (rep m' 1 []) (rep (n + 2) 1 (0 :: 1 :: R)))))
        (SW 0 3 (rl (rep m' 1 []) (rep (n + 2) 1 (0 :: 1 :: R)))) :=
      rule_CI_10 he 3 _
    apply canReach_trans hstep1
    apply canReach_trans (rule_SW_10_iter he m' 0 3 1 (rep (n + 1) 1 (0 :: 1 :: R)))
    rw [Nat.zero_add]
    have hiter : ∀ k a T,
        CanReach tm (SW m' a (rep (k + 1) 1 T)) (SW m' (iter (h m') k a) (1 :: T)) := by
      intro k
      induction k with
      | zero => intro a T; exact canReach_refl tm _
      | succ p ihp =>
        intro a T
        apply canReach_trans (ih a (rep p 1 T))
        have hrest := ihp (h m' a) T
        have heq : iter (h m') p (h m' a) = iter (h m') (p + 1) a := by
          rw [show p + 1 = p + 1 from rfl, iter_add_one]
        rw [heq] at hrest
        exact hrest
    apply canReach_trans (hiter (n + 1) 3 (0 :: 1 :: R))
    exact rule_SW_10 he m' (h (m' + 1) n) (1 :: R)

/-- `SW` chain over `rep k 2 []`: `SW m n (rl (rep k 2 []) R) -> SW (m + k) (hc m k n) R`. -/
theorem SW_chain (k m n : Nat) (R : List Nat) :
    CanReach tm (SW m n (rl (rep k 2 []) R)) (SW (m + k) (hc m k n) R) := by
  induction k generalizing m n with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    change CanReach tm (SW m n (1 :: 1 :: cons0 0 (rl (rep p 2 []) R)))
                       (SW (m + (p + 1)) (hc (m + 1) p (h m n)) R)
    apply canReach_trans (SW_step he m n (cons0 0 (rl (rep p 2 []) R)))
    apply canReach_trans (rule_SW_10 he m (h m n) (rl (rep p 2 []) R))
    have hrest := ih (m + 1) (h m n)
    have heq : m + 1 + p = m + (p + 1) := by omega
    rw [heq] at hrest
    exact hrest

/-- Rule 9: `CO 0 n (1 :: 1 :: R) -> CO 0 (ho 0 n) (1 :: R)`. -/
theorem rule_CO_0_11 (n : Nat) (R : List Nat) :
    CanReach tm (CO 0 n (1 :: 1 :: R)) (CO 0 (ho 0 n) (1 :: R)) := by
  unfold CO
  simp only [rep01]
  apply canReach_step (step_R_zero (L := rep n 1 [0, 0, 1]) (R := 1 :: 1 :: R) he.C0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 [0, 0, 1]) (R := 1 :: R) he.D1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: rep n 1 [0, 0, 1]) (R := R) he.Q1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := rep n 1 [0, 0, 1]) (R := 1 :: R) he.A1)
  simp only [cons0]
  apply canReach_trans ⟨n, loop_M1 he n [0, 0, 1] (0 :: 1 :: R)⟩
  rw [rep_snoc_sym]
  apply canReach_step (step_L_cons (a := 0) (L := [0, 1]) (R := rep n 1 (0 :: 1 :: R)) he.M1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := 1 :: rep n 1 (0 :: 1 :: R)) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: 1 :: rep n 1 (0 :: 1 :: R)) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: 1 :: rep n 1 (0 :: 1 :: R)) he.B1)
  simp only [cons0]
  rcases mod3_cases n with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · -- n = 3 * q
    rw [ho0_mod0]
    have hr : 1 :: 1 :: 1 :: rep (3 * q) 1 (0 :: 1 :: R) =
              rep (3 * (q + 1)) 1 (0 :: 1 :: R) := by
      have e : 3 + 3 * q = 3 * (q + 1) := by omega
      rw [← e, ← rep_add_sym]; rfl
    rw [hr]
    apply canReach_trans ⟨3 * (q + 1), loop_NOP he (q + 1) 1 [] (0 :: 1 :: R)⟩
    change CanReach tm (mkCfgR (some 13) (1 :: 1 :: 0 :: rep110 q [1]) (0 :: 1 :: R)) _
    apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 q [1]) (R := 1 :: R) he.N0)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 q [1]) (R := 0 :: 1 :: R) he.A1)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 0) (L := rep110 q [1]) (R := 0 :: 0 :: 1 :: R) he.M1)
    simp only [cons0]
    apply canReach_trans ⟨3 * q, jz_M_loop he q [1] (1 :: 0 :: 0 :: 1 :: R)⟩
    apply canReach_trans (jz_M_finish he (rep101 q (1 :: 0 :: 0 :: 1 :: R)))
    rw [one_rep101_eq_rl]
    have hrl : rl (rep q 2 []) (1 :: 1 :: 0 :: 0 :: 1 :: R) =
               1 :: 1 :: cons0 0 (rl (rep q 2 []) (0 :: 1 :: R)) := by
      have e := rl_append (rep q 2 []) [2] (a := 0) (R := 1 :: R)
      rw [rep_append_single] at e
      simpa [rl, rep, cons0] using e.symm
    rw [hrl]
    apply canReach_trans (rule_CI_11 he 3 (cons0 0 (rl (rep q 2 []) (0 :: 1 :: R))))
    apply canReach_trans (rule_CI_10 he 7 (rl (rep q 2 []) (0 :: 1 :: R)))
    apply canReach_trans (SW_chain he q 0 7 (0 :: 1 :: R))
    rw [Nat.zero_add]
    exact rule_SW_0 he q (hc 0 q 7) (1 :: R)
  · -- n = 3 * q + 1
    rw [ho0_mod1]
    have hr : 1 :: 1 :: 1 :: rep (3 * q + 1) 1 (0 :: 1 :: R) =
              rep (3 * (q + 1)) 1 (1 :: 0 :: 1 :: R) := by
      rw [show 3 * q + 1 = 3 * q + 1 from rfl, ← rep_add_sym (3 * q) 1 1 (0 :: 1 :: R)]
      have e : 3 + 3 * q = 3 * (q + 1) := by omega
      rw [← e, ← rep_add_sym]; rfl
    rw [hr]
    apply canReach_trans ⟨3 * (q + 1), loop_NOP he (q + 1) 1 [] (1 :: 0 :: 1 :: R)⟩
    apply canReach_step (step_R_cons (L := rep110 (q + 1) [1]) (R := 0 :: 1 :: R) he.N1)
    rw [cons0_ne_nil 0 (by simp [rep110])]
    apply canReach_step (step_L_cons (a := 0) (L := rep110 (q + 1) [1]) (R := 1 :: R) he.O0)
    simp only [cons0]
    apply canReach_step (step_R_cons (L := rep110 (q + 1) [1]) (R := 0 :: 1 :: R) he.C0)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 1) (L := rep110 (q + 1) [1]) (R := 1 :: R) he.D0)
    simp only [cons0]
    change CanReach tm (mkCfgR (some 4) (1 :: 1 :: 0 :: rep110 q [1]) (1 :: 0 :: 1 :: R)) _
    apply canReach_step (step_L_cons (a := 1) (L := 1 :: 0 :: rep110 q [1]) (R := 0 :: 1 :: R) he.E1)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 q [1]) (R := 1 :: 0 :: 1 :: R) he.E1)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 0) (L := rep110 q [1]) (R := 1 :: 1 :: 0 :: 1 :: R) he.E1)
    simp only [cons0]
    apply canReach_trans ⟨3 * q, loop_EF_110 he q [1] (1 :: 1 :: 1 :: 0 :: 1 :: R)⟩
    apply canReach_step (step_L_cons (a := 1) (L := []) (R := rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.E0)
    simp only [cons0]
    apply canReach_step (step_L_nil (R := 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.F1)
    simp only [cons0]
    apply canReach_step (step_L_nil (R := 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.E0)
    simp only [cons0]
    apply canReach_step (step_L_nil (R := 1 :: 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.F0)
    simp only [cons0]
    apply canReach_step (step_R_cons (L := []) (R := 0 :: 1 :: 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.G0)
    simp only [cons0]
    apply canReach_step (step_R_cons (L := [1]) (R := 1 :: 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.H0)
    simp only [cons0]
    apply canReach_step (step_R_cons (L := [0, 1]) (R := 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R)) he.H1)
    simp only [cons0]
    have hrr : 1 :: 1 :: rep (3 * q) 1 (1 :: 1 :: 1 :: 0 :: 1 :: R) =
               rep (3 * q + 5) 1 (0 :: 1 :: R) := by
      rw [rep_snoc_sym, rep_snoc_sym, rep_snoc_sym]
      have e : 3 * q + 1 + 1 + 1 + 1 + 1 = 3 * q + 5 := by omega
      rw [← e]; rfl
    rw [hrr]
    have hc := loop_C1 he (3 * q + 5) [0, 0, 1] (0 :: 1 :: R)
    exact ⟨3 * q + 5, by simpa [CO, rep01, cons0] using hc⟩
  · -- n = 3 * q + 2
    rw [ho0_mod2]
    have hr : 1 :: 1 :: 1 :: rep (3 * q + 2) 1 (0 :: 1 :: R) =
              rep (3 * (q + 1)) 1 (1 :: 1 :: 0 :: 1 :: R) := by
      rw [← rep_add_sym (3 * q) 2 1 (0 :: 1 :: R)]
      have e : 3 + 3 * q = 3 * (q + 1) := by omega
      rw [← e, ← rep_add_sym]; rfl
    rw [hr]
    apply canReach_trans ⟨3 * (q + 1), loop_NOP he (q + 1) 1 [] (1 :: 1 :: 0 :: 1 :: R)⟩
    apply canReach_step (step_R_cons (L := rep110 (q + 1) [1]) (R := 1 :: 0 :: 1 :: R) he.N1)
    rw [cons0_ne_nil 0 (by simp [rep110])]
    apply canReach_step (step_R_cons (L := 0 :: rep110 (q + 1) [1]) (R := 0 :: 1 :: R) he.O1)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 1) (L := 0 :: rep110 (q + 1) [1]) (R := 1 :: R) he.P0)
    simp only [cons0]
    apply canReach_step (step_L_cons (a := 0) (L := rep110 (q + 1) [1]) (R := 0 :: 1 :: R) he.A1)
    simp only [cons0]
    apply canReach_trans ⟨3 * (q + 1), jz_M_loop he (q + 1) [1] (0 :: 0 :: 1 :: R)⟩
    apply canReach_trans (jz_M_finish he (rep101 (q + 1) (0 :: 0 :: 1 :: R)))
    rw [one_rep101_eq_rl]
    change CanReach tm (CI 3 (1 :: 1 :: cons0 0 (rl (rep q 2 []) (1 :: 0 :: 0 :: 1 :: R)))) _
    apply canReach_trans (rule_CI_11 he 3 (cons0 0 (rl (rep q 2 []) (1 :: 0 :: 0 :: 1 :: R))))
    apply canReach_trans (rule_CI_10 he 7 (rl (rep q 2 []) (1 :: 0 :: 0 :: 1 :: R)))
    apply canReach_trans (SW_chain he q 0 7 (1 :: 0 :: 0 :: 1 :: R))
    rw [Nat.zero_add]
    apply canReach_trans (rule_SW_10 he q (hc 0 q 7) (0 :: 1 :: R))
    exact rule_SW_0 he (q + 1) (hc 0 q 7) (1 :: R)

/-- Rule 10: `CO (m + 1) n (1 :: 1 :: R) -> CO m 6 (rep (n + 2) 1 (0 :: 1 :: R))`. -/
theorem rule_CO_succ_11_raw (m n : Nat) (R : List Nat) :
    CanReach tm (CO (m + 1) n (1 :: 1 :: R))
                (CO m 6 (rep (n + 2) 1 (0 :: 1 :: R))) := by
  unfold CO
  apply canReach_step (step_R_zero (L := rep n 1 (rep01 (m + 1) [0, 0, 1])) (R := 1 :: 1 :: R) he.C0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := 1 :: rep n 1 (rep01 (m + 1) [0, 0, 1])) (R := 1 :: R) he.D1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := 1 :: rep n 1 (rep01 (m + 1) [0, 0, 1])) (R := R) he.Q1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := rep n 1 (rep01 (m + 1) [0, 0, 1])) (R := 1 :: R) he.A1)
  simp only [cons0]
  apply canReach_trans ⟨n, loop_M1 he n (rep01 (m + 1) [0, 0, 1]) (0 :: 1 :: R)⟩
  rw [rep_snoc_sym, rep01_zero_unfold]
  apply canReach_step (step_L_cons (a := 0) (L := rep10 (m + 1) [0, 1]) (R := rep n 1 (0 :: 1 :: R)) he.M1)
  simp only [cons0]
  apply canReach_trans ⟨2 * (m + 1), loop_MA_10 he (m + 1) [0, 1] (1 :: rep n 1 (0 :: 1 :: R))⟩
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := rep01 (m + 1) (1 :: rep n 1 (0 :: 1 :: R))) he.M0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := []) (R := 1 :: rep01 (m + 1) (1 :: rep n 1 (0 :: 1 :: R))) he.A0)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := []) (R := 1 :: 1 :: rep01 (m + 1) (1 :: rep n 1 (0 :: 1 :: R))) he.B1)
  simp only [cons0, rep01]
  apply canReach_step (step_R_cons (L := [1]) (R := 1 :: 0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))) he.N1)
  simp only [cons0]
  apply canReach_step (step_R_cons (L := [0, 1]) (R := 0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))) he.O1)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 1) (L := [0, 1]) (R := 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))) he.P0)
  simp only [cons0]
  apply canReach_step (step_L_cons (a := 0) (L := [1]) (R := 0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))) he.A1)
  simp only [cons0]
  apply canReach_trans (jz_M_finish he (0 :: 0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))))
  apply canReach_trans (rule_CI_10 he 3 (0 :: 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))))
  apply canReach_trans (rule_SW_0 he 0 3 (1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R))))
  have hr : 1 :: rep01 m (1 :: rep n 1 (0 :: 1 :: R)) =
            rl (rep m 1 []) (rep (n + 2) 1 (0 :: 1 :: R)) := by
    rw [one_rep01_eq_rep10, rl_rep_one]; rfl
  rw [hr]
  have h10 := rule_CO_10_iter he m 0 6 1 (rep (n + 1) 1 (0 :: 1 :: R))
  rw [Nat.zero_add] at h10
  exact h10

/-- `CO` single step: `CO m n (1 :: 1 :: R) -> CO m (ho m n) (1 :: R)`. -/
theorem CO_step (m : Nat) :
    ∀ n R, CanReach tm (CO m n (1 :: 1 :: R)) (CO m (ho m n) (1 :: R)) := by
  induction m with
  | zero => exact rule_CO_0_11 he
  | succ m' ih =>
    intro n R
    apply canReach_trans (rule_CO_succ_11_raw he m' n R)
    have hiter : ∀ k a T,
        CanReach tm (CO m' a (rep (k + 1) 1 T)) (CO m' (iter (ho m') k a) (1 :: T)) := by
      intro k
      induction k with
      | zero => intro a T; exact canReach_refl tm _
      | succ p ihp =>
        intro a T
        apply canReach_trans (ih a (rep p 1 T))
        have hrest := ihp (ho m' a) T
        have heq : iter (ho m') p (ho m' a) = iter (ho m') (p + 1) a := by
          rw [iter_add_one]
        rw [heq] at hrest
        exact hrest
    apply canReach_trans (hiter (n + 1) 6 (0 :: 1 :: R))
    exact rule_CO_10 he m' (ho (m' + 1) n) (1 :: R)

/-- `CO` iterated step on `rep (k + 1) 1 R`:
    `CO m n (rep (k + 1) 1 R) -> CO m (iter (ho m) k n) (1 :: R)`. -/
theorem CO_iter (k m n : Nat) (R : List Nat) :
    CanReach tm (CO m n (rep (k + 1) 1 R)) (CO m (iter (ho m) k n) (1 :: R)) := by
  induction k generalizing n with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    apply canReach_trans (CO_step he m n (rep p 1 R))
    have hrest := ih (ho m n)
    rw [iter_add_one] at hrest
    exact hrest

/-- `CO` chain over `rep k 2 []`:
    `CO m n (rl (rep k 2 []) R) -> CO (m + k) (hoc m k n) R`. -/
theorem CO_chain (k m n : Nat) (R : List Nat) :
    CanReach tm (CO m n (rl (rep k 2 []) R)) (CO (m + k) (hoc m k n) R) := by
  induction k generalizing m n with
  | zero => exact canReach_refl tm _
  | succ p ih =>
    change CanReach tm (CO m n (1 :: 1 :: cons0 0 (rl (rep p 2 []) R)))
                       (CO (m + (p + 1)) (hoc (m + 1) p (ho m n)) R)
    apply canReach_trans (CO_step he m n (cons0 0 (rl (rep p 2 []) R)))
    apply canReach_trans (rule_CO_10 he m (ho m n) (rl (rep p 2 []) R))
    have hrest := ih (m + 1) (ho m n)
    have heq : m + 1 + p = m + (p + 1) := by omega
    rw [heq] at hrest
    exact hrest

end EngineLemmas

end BB
