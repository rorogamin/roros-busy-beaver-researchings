/-
  BB/BB4_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(4, 8):
    TM: 5LC3LB7LA2RA4LB1LB4LB6LA_1RZ3RB1LC2RA3RD3RA4LC0RD_3RB1LB3LC2RC4LC7LC5LD7RA_3RB3LA6LC4LD4LC4LD6LC7LA
    Domain: BB(4, 8) (4 states, 8 symbols)
    Previous best dominated bound: BB(4, 7) > f_{ω+3}(34)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω+4}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz

namespace BB
namespace BB4_8

/-- The 4-state, 8-symbol Turing machine `bb48`:
    5LC3LB7LA2RA4LB1LB4LB6LA_1RZ3RB1LC2RA3RD3RA4LC0RD_3RB1LB3LC2RC4LC7LC5LD7RA_3RB3LA6LC4LD4LC4LD6LC7LA -/
def bb48 : TM
  -- State A (0): 5LC 3LB 7LA 2RA 4LB 1LB 4LB 6LA
  | 0, 0 => some ⟨5, Dir.L, some 2⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨7, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨1, Dir.L, some 1⟩
  | 0, 6 => some ⟨4, Dir.L, some 1⟩
  | 0, 7 => some ⟨6, Dir.L, some 0⟩
  -- State B (1): 1RZ 3RB 1LC 2RA 3RD 3RA 4LC 0RD
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 2⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.R, some 3⟩
  | 1, 5 => some ⟨3, Dir.R, some 0⟩
  | 1, 6 => some ⟨4, Dir.L, some 2⟩
  | 1, 7 => some ⟨0, Dir.R, some 3⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 7LC 5LD 7RA
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨7, Dir.L, some 2⟩
  | 2, 6 => some ⟨5, Dir.L, some 3⟩
  | 2, 7 => some ⟨7, Dir.R, some 0⟩
  -- State D (3): 3RB 3LA 6LC 4LD 4LC 4LD 6LC 7LA
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.L, some 0⟩
  | 3, 2 => some ⟨6, Dir.L, some 2⟩
  | 3, 3 => some ⟨4, Dir.L, some 3⟩
  | 3, 4 => some ⟨4, Dir.L, some 2⟩
  | 3, 5 => some ⟨4, Dir.L, some 3⟩
  | 3, 6 => some ⟨6, Dir.L, some 2⟩
  | 3, 7 => some ⟨7, Dir.L, some 0⟩
  | _, _ => none

/-- Certificate that `bb48` is a valid 4-state, 8-symbol Turing machine. -/
theorem bb48_valid : ValidTM 4 8 bb48 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 =>
      simp [bb48]
    | s + 4, _ => omega
    | _, sym + 8 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 =>
      omega
    | s + 4, _ => rfl
    | 0, _ + 8 | 1, _ + 8 | 2, _ + 8 | 3, _ + 8 => rfl

theorem bb48_kropitz : KropitzCore bb48 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Macro configuration `Dcfg N R = 0^∞ 3^N D> R`. -/
def Dcfg (N : Nat) (R : List Nat) : Config :=
  mkCfgR (some 3) (rep N 3 []) R

/-! ### Mathematical Growth Functions `G4`, `G5`, `G6`, `G7` -/

def Gexit : Nat → Nat → Nat
  | 0, m => 2 * m + 4
  | k + 1, m => Gexit k (Kfn (k + 1) m)

def G4 (N : Nat) : Nat := Gexit (N - 1) 0
def G5 (N : Nat) : Nat := iter G4 N 2
def G6 (N : Nat) : Nat := iter G5 N 4
def G7 (N : Nat) : Nat := iter G6 N 4

/-! ### Rule D0: Halting on blank right tape -/

theorem rule_D0 (N : Nat) :
    ∃ t, HaltsIn bb48 (Dcfg N []) t ∧ t = 2 := by
  refine ⟨2, ⟨mkCfgR none (1 :: 3 :: rep N 3 []) [], ?_, rfl⟩, rfl⟩
  have h1 : step bb48 (Dcfg N []) = some (mkCfgR (some 1) (3 :: rep N 3 []) []) :=
    step_mkCfgR_R_nil (tm := bb48) (q := 3) (w := 2) (nx := some 1) rfl
  have h2 : step bb48 (mkCfgR (some 1) (3 :: rep N 3 []) []) =
            some (mkCfgR none (1 :: 3 :: rep N 3 []) []) :=
    step_mkCfgR_R_nil (tm := bb48) (q := 1) (w := 0) (nx := none) rfl
  exact steps_succ bb48 1 _ _ _ h1 (steps_one bb48 _ _ h2)

/-! ### Rule D4: `0^∞ 3^N D> 4 R  -->  0^∞ 3^(G4 N) D> R` (for `N ≥ 2`) -/

private theorem loop_C_4 (n : Nat) :
    ∀ j L R, ∃ t, Reaches bb48 (mkCfgR (some 2) (rep n 3 L) (2 :: rep j 3 (4 :: R)))
                               (mkCfgR (some 2) L (2 :: rep (j + n) 3 (4 :: R))) t := by
  induction n with
  | zero => intro j L R; exact ⟨0, reaches_zero bb48 _⟩
  | succ k ih =>
    intro j L R
    have h1 : step bb48 (mkCfgR (some 2) (3 :: rep k 3 L) (2 :: rep j 3 (4 :: R))) =
              some (mkCfgR (some 2) (rep k 3 L) (3 :: 3 :: rep j 3 (4 :: R))) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 2) (cur := 2) rfl
    have h2 := loop_C3 bb48_kropitz (j + 2) (rep k 3 L) (4 :: R)
    have h3 : step bb48 (mkCfgR (some 2) (2 :: rep (j + 1) 2 (rep k 3 L)) (4 :: R)) =
              some (mkCfgR (some 2) (rep (j + 1) 2 (rep k 3 L)) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 3) (cur := 4) rfl
    have h4 := loop_C2 bb48_kropitz (j + 1) (rep k 3 L) (4 :: R)
    have h12 := steps_succ bb48 _ _ _ _ h1 h2
    have h34 := steps_succ bb48 _ _ _ _ h3 h4
    have hstep := reaches_trans h12 h34
    obtain ⟨t2, hrest⟩ := ih (j + 1) L R
    have hadd : j + 1 + k = j + (k + 1) := by omega
    rw [hadd] at hrest
    exact ⟨_, reaches_trans hstep hrest⟩

private theorem d4_entry (k : Nat) (R : List Nat) :
    ∃ t, Reaches bb48 (Dcfg (k + 2) (4 :: R)) (Bcfg (k + 1) 0 (4 :: R)) t := by
  have h1 : step bb48 (Dcfg (k + 2) (4 :: R)) =
            some (mkCfgR (some 2) (rep (k + 1) 3 []) (3 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 3) (cur := 4) rfl
  have h2 : step bb48 (mkCfgR (some 2) (rep (k + 1) 3 []) (3 :: 4 :: R)) =
            some (mkCfgR (some 2) (2 :: rep (k + 1) 3 []) (4 :: R)) :=
    step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl
  have h3 : step bb48 (mkCfgR (some 2) (2 :: rep (k + 1) 3 []) (4 :: R)) =
            some (mkCfgR (some 2) (rep (k + 1) 3 []) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 3) (cur := 4) rfl
  obtain ⟨tl, hl⟩ := loop_C_4 (k + 1) 0 [] R
  simp only [Nat.zero_add] at hl
  have h4 : step bb48 (mkCfgR (some 2) [] (2 :: rep (k + 1) 3 (4 :: R))) =
            some (mkCfgR (some 2) [] (0 :: 3 :: rep (k + 1) 3 (4 :: R))) :=
    step_mkCfgR_L_nil (tm := bb48) (q := 2) (w := 2) (cur := 2) rfl
  have h5 : step bb48 (mkCfgR (some 2) [] (0 :: 3 :: rep (k + 1) 3 (4 :: R))) =
            some (mkCfgR (some 1) [3] (3 :: rep (k + 1) 3 (4 :: R))) :=
    step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl
  have h6 : step bb48 (mkCfgR (some 1) [3] (3 :: rep (k + 1) 3 (4 :: R))) =
            some (mkCfgR (some 0) [2, 3] (rep (k + 1) 3 (4 :: R))) :=
    step_mkCfgR_R (tm := bb48) (q := 1) (w := 1) (cur := 3) rfl
  have h7 := loop_A3 bb48_kropitz (k + 1) [2, 3] (4 :: R)
  have hrep : rep (k + 1) 2 [2, 3] = rep (k + 2) 2 [3] := by rw [rep_snoc_one]; rfl
  rw [hrep] at h7
  have h47 := steps_succ bb48 _ _ _ _ h4 (steps_succ bb48 _ _ _ _ h5 (steps_succ bb48 _ _ _ _ h6 h7))
  have h13 := steps_succ bb48 _ _ _ _ h1 (steps_succ bb48 _ _ _ _ h2 (steps_succ bb48 _ _ _ _ h3 (reaches_trans hl h47)))
  exact ⟨_, h13⟩

private theorem b4_exit (k : Nat) :
    ∀ m R, ∃ t, Reaches bb48 (Bcfg k m (4 :: R)) (Dcfg (Gexit k m) R) t ∧ Gexit k m ≤ t := by
  induction k with
  | zero =>
    intro m R
    have h1 : step bb48 (Bcfg 0 m (4 :: R)) =
              some (mkCfgR (some 1) (rep (2 * m + 1) 3 []) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 3) (cur := 4) rfl
    have h2 := kropitz_level0_from_B bb48_kropitz m (4 :: R)
    have h3 : step bb48 (mkCfgR (some 1) (rep (2 * m + 3) 3 []) (4 :: R)) =
              some (Dcfg (2 * m + 4) R) :=
      step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 4) rfl
    have hall := steps_succ bb48 _ _ _ _ h1 (reaches_trans h2 (steps_one bb48 _ _ h3))
    exact ⟨_, hall, by unfold Gexit; omega⟩
  | succ j ih =>
    intro m R
    have h1 : step bb48 (Bcfg (j + 1) m (4 :: R)) =
              some (mkCfgR (some 1) (rep (j + 1) 2 (rep (2 * m + 1) 3 [])) (2 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 3) (cur := 4) rfl
    have h2 := kropitz_levelS_from_B bb48_kropitz j m (4 :: R)
    obtain ⟨t3, h3⟩ := kropitz_rep bb48_kropitz j (2 * m + 2) 0 (4 :: R)
    obtain ⟨t4, h4, hle4⟩ := ih (Kfn (j + 1) m) R
    have h12 := steps_succ bb48 _ _ _ _ h1 h2
    have h123 := reaches_trans h12 h3
    have hall := reaches_trans h123 h4
    exact ⟨_, hall, Nat.le_trans hle4 (Nat.le_add_left _ _)⟩

theorem rule_D4 (N : Nat) (hN : 2 ≤ N) (R : List Nat) :
    ∃ t, Reaches bb48 (Dcfg N (4 :: R)) (Dcfg (G4 N) R) t ∧ G4 N ≤ t := by
  cases N with
  | zero => omega
  | succ N1 =>
    cases N1 with
    | zero => omega
    | succ k =>
      obtain ⟨t1, h1⟩ := d4_entry k R
      obtain ⟨t2, h2, hle⟩ := b4_exit (k + 1) 0 R
      have hG : G4 (k + 2) = Gexit (k + 1) 0 := rfl
      rw [hG]
      exact ⟨t1 + t2, reaches_trans h1 h2, Nat.le_trans hle (Nat.le_add_left _ _)⟩

theorem rule_D4_rep (n : Nat) :
    ∀ N R, 2 ≤ N →
      ∃ t, Reaches bb48 (Dcfg N (rep n 4 R)) (Dcfg (iter G4 n N) R) t ∧
           (1 ≤ n → iter G4 n N ≤ t) := by
  -- Helper: G4 N ≥ 2 for N ≥ 2
  have hG4_ge2 : ∀ x, 2 ≤ x → 2 ≤ G4 x := by
    intro x hx
    have hge : ∀ k m, 2 * m + 4 ≤ Gexit k m := by
      intro k
      induction k with
      | zero => intro m; exact Nat.le_refl _
      | succ j ih =>
        intro m
        have h1 := ih (Kfn (j + 1) m)
        have h2 := Kfn_ge_succ (j + 1) m
        change 2 * m + 4 ≤ Gexit j (Kfn (j + 1) m)
        omega
    have := hge (x - 1) 0
    unfold G4; omega
  induction n with
  | zero => intro N R _; exact ⟨0, reaches_zero bb48 _, fun h => by cases h⟩
  | succ k ih =>
    intro N R hN
    obtain ⟨t1, h1, hle1⟩ := rule_D4 N hN (rep k 4 R)
    obtain ⟨t2, h2, hle2⟩ := ih (G4 N) R (hG4_ge2 N hN)
    have hcomm : iter G4 k (G4 N) = iter G4 (k + 1) N := by rw [iter_add]; rfl
    rw [hcomm] at h2 hle2
    refine ⟨t1 + t2, reaches_trans h1 h2, fun _ => ?_⟩
    cases k with
    | zero =>
      simp only [iter] at hle1 ⊢
      exact Nat.le_trans hle1 (Nat.le_add_right _ _)
    | succ k' =>
      exact Nat.le_trans (hle2 (Nat.succ_pos k')) (Nat.le_add_left _ _)

/-! ### Rule D5: `0^∞ 3^N D> 5 R  -->  0^∞ 3^2 D> 4^N R  -->  0^∞ 3^(G5 N) D> R` -/

private theorem loop_D3 (n : Nat) :
    ∀ L R, Reaches bb48 (mkCfgR (some 3) (rep n 3 L) (3 :: R))
                        (mkCfgR (some 3) L (3 :: rep n 4 R)) n := by
  induction n with
  | zero => intro L R; exact reaches_zero bb48 _
  | succ k ih =>
    intro L R
    have h1 : step bb48 (mkCfgR (some 3) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 3) (rep k 3 L) (3 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 3) (cur := 3) rfl
    have h2 := ih L (4 :: R)
    rw [rep_snoc_one] at h2
    exact steps_succ bb48 k _ _ _ h1 h2

theorem rule_D5_expand (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    Reaches bb48 (Dcfg N (5 :: R)) (Dcfg 2 (rep N 4 R)) (N + 3) := by
  cases N with
  | zero => cases hN
  | succ k =>
    have h1 : step bb48 (Dcfg (k + 1) (5 :: R)) =
              some (mkCfgR (some 3) (rep k 3 []) (3 :: 4 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 3) (cur := 5) rfl
    have h2 := loop_D3 k [] (4 :: R)
    rw [rep_snoc_one] at h2
    have h3 : step bb48 (mkCfgR (some 3) [] (3 :: rep (k + 1) 4 R)) =
              some (mkCfgR (some 3) [] (0 :: 4 :: rep (k + 1) 4 R)) :=
      step_mkCfgR_L_nil (tm := bb48) (q := 3) (w := 3) (cur := 3) rfl
    have h4 : step bb48 (mkCfgR (some 3) [] (0 :: 4 :: rep (k + 1) 4 R)) =
              some (mkCfgR (some 1) [3] (4 :: rep (k + 1) 4 R)) :=
      step_mkCfgR_R (tm := bb48) (q := 3) (w := 2) (cur := 0) rfl
    have h5 : step bb48 (mkCfgR (some 1) [3] (4 :: rep (k + 1) 4 R)) =
              some (Dcfg 2 (rep (k + 1) 4 R)) :=
      step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 4) rfl
    have h35 := steps_succ bb48 2 _ _ _ h3 (steps_succ bb48 1 _ _ _ h4 (steps_one bb48 _ _ h5))
    have hall := steps_succ bb48 _ _ _ _ h1 (reaches_trans h2 h35)
    have ht : k + 3 + 1 = k + 1 + 3 := by omega
    rw [ht] at hall
    exact hall

theorem rule_D5 (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    ∃ t, Reaches bb48 (Dcfg N (5 :: R)) (Dcfg (G5 N) R) t ∧ G5 N ≤ t := by
  have h1 := rule_D5_expand N hN R
  obtain ⟨t2, h2, hle2⟩ := rule_D4_rep N 2 R (Nat.le_refl 2)
  exact ⟨(N + 3) + t2, reaches_trans h1 h2, Nat.le_trans (hle2 hN) (Nat.le_add_left _ _)⟩

/-! ### Rule D6: `0^∞ 3^N D> 6 R  -->  0^∞ 3^4 D> 5^N R  -->  0^∞ 3^(G6 N) D> R` -/

private theorem loop_D6_shuttle (n : Nat) :
    ∀ R, Reaches bb48 (mkCfgR (some 2) (rep n 3 []) (3 :: 6 :: R))
                      (mkCfgR (some 2) [] (0 :: 6 :: rep (n + 1) 5 R)) (3 * n + 3) := by
  induction n with
  | zero =>
    intro R
    have h1 : step bb48 (mkCfgR (some 2) [] (3 :: 6 :: R)) =
              some (mkCfgR (some 2) [2] (6 :: R)) :=
      step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl
    have h2 : step bb48 (mkCfgR (some 2) [2] (6 :: R)) =
              some (mkCfgR (some 3) [] (2 :: 5 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 4) (cur := 6) rfl
    have h3 : step bb48 (mkCfgR (some 3) [] (2 :: 5 :: R)) =
              some (mkCfgR (some 2) [] (0 :: 6 :: 5 :: R)) :=
      step_mkCfgR_L_nil (tm := bb48) (q := 3) (w := 5) (cur := 2) rfl
    exact steps_succ bb48 2 _ _ _ h1 (steps_succ bb48 1 _ _ _ h2 (steps_one bb48 _ _ h3))
  | succ k ih =>
    intro R
    have h1 : step bb48 (mkCfgR (some 2) (3 :: rep k 3 []) (3 :: 6 :: R)) =
              some (mkCfgR (some 2) (2 :: 3 :: rep k 3 []) (6 :: R)) :=
      step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl
    have h2 : step bb48 (mkCfgR (some 2) (2 :: 3 :: rep k 3 []) (6 :: R)) =
              some (mkCfgR (some 3) (3 :: rep k 3 []) (2 :: 5 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 4) (cur := 6) rfl
    have h3 : step bb48 (mkCfgR (some 3) (3 :: rep k 3 []) (2 :: 5 :: R)) =
              some (mkCfgR (some 2) (rep k 3 []) (3 :: 6 :: 5 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 5) (cur := 2) rfl
    have h4 := ih (5 :: R)
    rw [rep_snoc_one] at h4
    have hall := steps_succ bb48 _ _ _ _ h1 (steps_succ bb48 _ _ _ _ h2 (steps_succ bb48 _ _ _ _ h3 h4))
    have ht : 3 * k + 3 + 1 + 1 + 1 = 3 * (k + 1) + 3 := by omega
    rw [ht] at hall
    exact hall

private theorem d6_exit_16 (R : List Nat) :
    Reaches bb48 (mkCfgR (some 2) [] (0 :: 6 :: R)) (Dcfg 4 R) 16 := by
  refine steps_succ bb48 15 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl) ?_
  refine steps_succ bb48 14 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 1) (w := 3) (cur := 6) rfl) ?_
  refine steps_succ bb48 13 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl) ?_
  refine steps_succ bb48 12 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 3) (cur := 4) rfl) ?_
  refine steps_succ bb48 11 _ _ _ (step_mkCfgR_L_nil (tm := bb48) (q := 2) (w := 2) (cur := 2) rfl) ?_
  refine steps_succ bb48 10 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl) ?_
  refine steps_succ bb48 9 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 1) (cur := 3) rfl) ?_
  refine steps_succ bb48 8 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 3) (cur := 4) rfl) ?_
  refine steps_succ bb48 7 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 1) (w := 0) (cur := 2) rfl) ?_
  refine steps_succ bb48 6 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl) ?_
  refine steps_succ bb48 5 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 0) (cur := 1) rfl) ?_
  refine steps_succ bb48 4 _ _ _ (step_mkCfgR_L_nil (tm := bb48) (q := 1) (w := 0) (cur := 2) rfl) ?_
  refine steps_succ bb48 3 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl) ?_
  refine steps_succ bb48 2 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 1) rfl) ?_
  refine steps_succ bb48 1 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 1) rfl) ?_
  exact steps_one bb48 _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 4) rfl)

theorem rule_D6_expand (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    Reaches bb48 (Dcfg N (6 :: R)) (Dcfg 4 (rep N 5 R)) (3 * N + 17) := by
  cases N with
  | zero => cases hN
  | succ k =>
    have h1 : step bb48 (Dcfg (k + 1) (6 :: R)) =
              some (mkCfgR (some 2) (rep k 3 []) (3 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 5) (cur := 6) rfl
    have h2 := loop_D6_shuttle k R
    have h3 := d6_exit_16 (rep (k + 1) 5 R)
    have hall := steps_succ bb48 _ _ _ _ h1 (reaches_trans h2 h3)
    have ht : 3 * k + 3 + 16 + 1 = 3 * (k + 1) + 17 := by omega
    rw [ht] at hall
    exact hall

/-! ### Rule D7: `0^∞ 3^N D> 7 R  -->  0^∞ 3^4 D> 6^N R  -->  0^∞ 3^(G7 N) D> R` -/

private theorem loop_D7_shuttle (n : Nat) :
    ∀ R, Reaches bb48 (mkCfgR (some 0) (rep n 3 []) (3 :: 7 :: R))
                      (mkCfgR (some 0) [] (0 :: 7 :: rep (n + 1) 6 R)) (3 * n + 3) := by
  induction n with
  | zero =>
    intro R
    have h1 : step bb48 (mkCfgR (some 0) [] (3 :: 7 :: R)) =
              some (mkCfgR (some 0) [2] (7 :: R)) :=
      step_mkCfgR_R (tm := bb48) (q := 0) (w := 1) (cur := 3) rfl
    have h2 : step bb48 (mkCfgR (some 0) [2] (7 :: R)) =
              some (mkCfgR (some 0) [] (2 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 5) (cur := 7) rfl
    have h3 : step bb48 (mkCfgR (some 0) [] (2 :: 6 :: R)) =
              some (mkCfgR (some 0) [] (0 :: 7 :: 6 :: R)) :=
      step_mkCfgR_L_nil (tm := bb48) (q := 0) (w := 6) (cur := 2) rfl
    exact steps_succ bb48 2 _ _ _ h1 (steps_succ bb48 1 _ _ _ h2 (steps_one bb48 _ _ h3))
  | succ k ih =>
    intro R
    have h1 : step bb48 (mkCfgR (some 0) (3 :: rep k 3 []) (3 :: 7 :: R)) =
              some (mkCfgR (some 0) (2 :: 3 :: rep k 3 []) (7 :: R)) :=
      step_mkCfgR_R (tm := bb48) (q := 0) (w := 1) (cur := 3) rfl
    have h2 : step bb48 (mkCfgR (some 0) (2 :: 3 :: rep k 3 []) (7 :: R)) =
              some (mkCfgR (some 0) (3 :: rep k 3 []) (2 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 5) (cur := 7) rfl
    have h3 : step bb48 (mkCfgR (some 0) (3 :: rep k 3 []) (2 :: 6 :: R)) =
              some (mkCfgR (some 0) (rep k 3 []) (3 :: 7 :: 6 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 6) (cur := 2) rfl
    have h4 := ih (6 :: R)
    rw [rep_snoc_one] at h4
    have hall := steps_succ bb48 _ _ _ _ h1 (steps_succ bb48 _ _ _ _ h2 (steps_succ bb48 _ _ _ _ h3 h4))
    have ht : 3 * k + 3 + 1 + 1 + 1 = 3 * (k + 1) + 3 := by omega
    rw [ht] at hall
    exact hall

private theorem d7_exit_14 (R : List Nat) :
    Reaches bb48 (mkCfgR (some 0) [] (0 :: 7 :: R)) (Dcfg 4 R) 14 := by
  refine steps_succ bb48 13 _ _ _ (step_mkCfgR_L_nil (tm := bb48) (q := 0) (w := 4) (cur := 0) rfl) ?_
  refine steps_succ bb48 12 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl) ?_
  refine steps_succ bb48 11 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 5) rfl) ?_
  refine steps_succ bb48 10 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 5) (cur := 7) rfl) ?_
  refine steps_succ bb48 9 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 0) (w := 1) (cur := 3) rfl) ?_
  refine steps_succ bb48 8 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 0) (w := 3) (cur := 6) rfl) ?_
  refine steps_succ bb48 7 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 1) (w := 0) (cur := 2) rfl) ?_
  refine steps_succ bb48 6 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 1) (cur := 3) rfl) ?_
  refine steps_succ bb48 5 _ _ _ (step_mkCfgR_L_cons (tm := bb48) (q := 2) (w := 0) (cur := 1) rfl) ?_
  refine steps_succ bb48 4 _ _ _ (step_mkCfgR_L_nil (tm := bb48) (q := 1) (w := 0) (cur := 2) rfl) ?_
  refine steps_succ bb48 3 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 2) (w := 2) (cur := 0) rfl) ?_
  refine steps_succ bb48 2 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 1) rfl) ?_
  refine steps_succ bb48 1 _ _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 1) rfl) ?_
  exact steps_one bb48 _ _ (step_mkCfgR_R (tm := bb48) (q := 1) (w := 2) (cur := 4) rfl)

theorem rule_D7_expand (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    Reaches bb48 (Dcfg N (7 :: R)) (Dcfg 4 (rep N 6 R)) (3 * N + 15) := by
  cases N with
  | zero => cases hN
  | succ k =>
    have h1 : step bb48 (Dcfg (k + 1) (7 :: R)) =
              some (mkCfgR (some 0) (rep k 3 []) (3 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb48) (q := 3) (w := 6) (cur := 7) rfl
    have h2 := loop_D7_shuttle k R
    have h3 := d7_exit_14 (rep (k + 1) 6 R)
    have hall := steps_succ bb48 _ _ _ _ h1 (reaches_trans h2 h3)
    have ht : 3 * k + 3 + 14 + 1 = 3 * (k + 1) + 15 := by omega
    rw [ht] at hall
    exact hall

/-! ### Growth Bounds: `G4^2 > f_ω`, `G5^2 > f_{ω+1}`, `G6^2 > f_{ω+2}`, `G7^2 > f_{ω+3}` -/

private theorem Kfn_zero_ge (k : Nat) : k + 1 ≤ Kfn k 0 := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ j ih =>
    show j + 2 ≤ Kfn j (Kfn j 0)
    have h := Kfn_ge_succ j (Kfn j 0)
    omega

private theorem Kfn_step_k (k m : Nat) : Kfn k m ≤ Kfn (k + 1) m := by
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

private theorem Kfn_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (m : Nat) : Kfn k1 m ≤ Kfn k2 m := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Kfn_step_k j m)

private theorem Gexit_ge (k m : Nat) : 2 * m + 4 ≤ Gexit k m := by
  induction k generalizing m with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    have h1 := ih (Kfn (j + 1) m)
    have h2 := Kfn_ge_succ (j + 1) m
    change 2 * m + 4 ≤ Gexit j (Kfn (j + 1) m)
    omega

private theorem Gexit_mono_m (k : Nat) {x y : Nat} (hxy : x ≤ y) : Gexit k x ≤ Gexit k y := by
  induction k generalizing x y with
  | zero => unfold Gexit; omega
  | succ j ih => exact ih (Kfn_mono (j + 1) hxy)

private theorem Gexit_step_k (k m : Nat) : Gexit k m ≤ Gexit (k + 1) m :=
  Gexit_mono_m k (Nat.le_trans (Nat.le_succ m) (Kfn_ge_succ (k + 1) m))

private theorem Gexit_mono_k {k1 k2 : Nat} (hk : k1 ≤ k2) (m : Nat) : Gexit k1 m ≤ Gexit k2 m := by
  induction hk with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Gexit_step_k j m)

theorem G4_mono {x y : Nat} (hxy : x ≤ y) : G4 x ≤ G4 y :=
  Gexit_mono_k (by omega) 0

theorem G4_ge_2x_plus_4 (n : Nat) (hn : 2 ≤ n) : 2 * n + 4 ≤ G4 n := by
  cases n with
  | zero => omega
  | succ n1 =>
    cases n1 with
    | zero => omega
    | succ k =>
      have h2 := Gexit_ge k (Kfn (k + 1) 0)
      have h3 := Kfn_zero_ge (k + 1)
      change 2 * (k + 2) + 4 ≤ Gexit k (Kfn (k + 1) 0)
      omega

theorem G4_inc (n : Nat) (hn : 2 ≤ n) : n + 1 ≤ G4 n := by
  have := G4_ge_2x_plus_4 n hn; omega

theorem G4_sq_gt_f_omega (n : Nat) (hn : 2 ≤ n) : f_omega n < G4 (G4 n) := by
  have hM : 2 * n + 4 ≤ G4 n := G4_ge_2x_plus_4 n hn
  generalize G4 n = M at hM ⊢
  cases M with
  | zero => omega
  | succ m1 =>
    cases m1 with
    | zero => omega
    | succ j =>
      have hj : n ≤ j := by omega
      have hge1 : 2 * Kfn (j + 1) 0 + 4 ≤ G4 (j + 1 + 1) := Gexit_ge j (Kfn (j + 1) 0)
      have hK1 : Kfn (j + 1) 0 = Kfn j (Kfn j 0) := rfl
      have hK2 : n ≤ Kfn j 0 := Nat.le_trans (by omega : n ≤ j + 1) (Kfn_zero_ge j)
      have hK3 : Kfn j n ≤ Kfn (j + 1) 0 := by
        rw [hK1]; exact Kfn_mono j hK2
      have hK4 : fFin n n ≤ Kfn j n :=
        Nat.le_trans (Kfn_ge_fFin n n) (Kfn_mono_k hj n)
      have hK5 : f_omega n ≤ Kfn (j + 1) 0 := Nat.le_trans hK4 hK3
      omega

theorem G5_ge_3x (x : Nat) (_hx : 2 ≤ x) : 3 * x ≤ G5 x := by
  have hstep : ∀ k, 2 + 4 * k ≤ iter G4 k 2 := by
    intro k
    induction k with
    | zero => exact Nat.le_refl 2
    | succ m ih =>
      rw [iter_succ]
      have h2 : 2 ≤ iter G4 m 2 := by omega
      have hg := G4_ge_2x_plus_4 (iter G4 m 2) h2
      omega
  have := hstep x; unfold G5; omega

theorem G5_mono {x y : Nat} (hxy : x ≤ y) : G5 x ≤ G5 y :=
  iter_mono_steps G4 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z1 =>
      cases z1 with
      | zero => exact Nat.le_trans (by omega : 1 ≤ 4) (Gexit_ge 0 0)
      | succ k => exact Nat.le_trans (Nat.le_succ _) (G4_inc (k + 2) (by omega))) hxy 2

theorem G5_inc (x : Nat) (hx : 2 ≤ x) : x + 1 ≤ G5 x := by
  have := G5_ge_3x x hx; omega

theorem G5_sq_gt (x : Nat) (hx : 2 ≤ x) : f_omega_plus 1 x < G5 (G5 x) :=
  climb_level G4 f_omega 2 (Nat.le_refl 2)
    (fun _ _ h => G4_mono h) G4_inc G4_sq_gt_f_omega G5_ge_3x (fOmegaMul_props 1 0) x hx

theorem G6_ge_3x (x : Nat) (_hx : 2 ≤ x) : 3 * x ≤ G6 x := by
  have hstep : ∀ k, 4 + 4 * k ≤ iter G5 k 4 := by
    intro k
    induction k with
    | zero => exact Nat.le_refl 4
    | succ m ih =>
      rw [iter_succ]
      have h2 : 2 ≤ iter G5 m 4 := by omega
      have hg := G5_ge_3x (iter G5 m 4) h2
      omega
  have := hstep x; unfold G6; omega

theorem G6_mono {x y : Nat} (hxy : x ≤ y) : G6 x ≤ G6 y :=
  iter_mono_steps G5 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z1 =>
      cases z1 with
      | zero =>
        rw [G5, iter_succ, iter_zero]
        have h2 := G4_ge_2x_plus_4 2 (Nat.le_refl 2)
        omega
      | succ k => exact Nat.le_trans (Nat.le_succ _) (G5_inc (k + 2) (by omega))) hxy 4

theorem G6_inc (x : Nat) (hx : 2 ≤ x) : x + 1 ≤ G6 x := by
  have := G6_ge_3x x hx; omega

theorem G6_sq_gt (x : Nat) (hx : 2 ≤ x) : f_omega_plus 2 x < G6 (G6 x) :=
  climb_level G5 (f_omega_plus 1) 4 (by omega)
    (fun _ _ h => G5_mono h) G5_inc G5_sq_gt G6_ge_3x (fOmegaMul_props 1 1) x hx

theorem G7_ge_3x (x : Nat) (_hx : 2 ≤ x) : 3 * x ≤ G7 x := by
  have hstep : ∀ k, 4 + 4 * k ≤ iter G6 k 4 := by
    intro k
    induction k with
    | zero => exact Nat.le_refl 4
    | succ m ih =>
      rw [iter_succ]
      have h2 : 2 ≤ iter G6 m 4 := by omega
      have hg := G6_ge_3x (iter G6 m 4) h2
      omega
  have := hstep x; unfold G7; omega

theorem G7_mono {x y : Nat} (hxy : x ≤ y) : G7 x ≤ G7 y :=
  iter_mono_steps G6 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z1 =>
      cases z1 with
      | zero =>
        rw [G6, iter_succ, iter_zero]
        have h2 := G5_ge_3x 4 (by omega)
        omega
      | succ k => exact Nat.le_trans (Nat.le_succ _) (G6_inc (k + 2) (by omega))) hxy 4

theorem G7_inc (x : Nat) (hx : 2 ≤ x) : x + 1 ≤ G7 x := by
  have := G7_ge_3x x hx; omega

theorem G7_sq_gt (x : Nat) (hx : 2 ≤ x) : f_omega_plus 3 x < G7 (G7 x) :=
  climb_level G6 (f_omega_plus 2) 4 (by omega)
    (fun _ _ h => G6_mono h) G6_inc G6_sq_gt G7_ge_3x (fOmegaMul_props 1 2) x hx

/-! ### Complete Execution Rules for `5^n`, `6`, `6^n`, `7`, `7^n` -/

theorem rule_D5_rep (n : Nat) :
    ∀ N R, 2 ≤ N →
      ∃ t, Reaches bb48 (Dcfg N (rep n 5 R)) (Dcfg (iter G5 n N) R) t ∧
           (1 ≤ n → iter G5 n N ≤ t) := by
  induction n with
  | zero => intro N R _; exact ⟨0, reaches_zero bb48 _, fun h => by cases h⟩
  | succ k ih =>
    intro N R hN
    obtain ⟨t1, h1, hle1⟩ := rule_D5 N (by omega) (rep k 5 R)
    have h2 : 2 ≤ G5 N := by have := G5_inc N hN; omega
    obtain ⟨t2, h2', hle2⟩ := ih (G5 N) R h2
    have hcomm : iter G5 k (G5 N) = iter G5 (k + 1) N := by rw [iter_add]; rfl
    rw [hcomm] at h2' hle2
    refine ⟨t1 + t2, reaches_trans h1 h2', fun _ => ?_⟩
    cases k with
    | zero => exact Nat.le_trans hle1 (Nat.le_add_right _ _)
    | succ k' => exact Nat.le_trans (hle2 (Nat.succ_pos k')) (Nat.le_add_left _ _)

theorem rule_D6 (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    ∃ t, Reaches bb48 (Dcfg N (6 :: R)) (Dcfg (G6 N) R) t ∧ G6 N ≤ t := by
  have h1 := rule_D6_expand N hN R
  obtain ⟨t2, h2, hle2⟩ := rule_D5_rep N 4 R (by omega)
  exact ⟨(3 * N + 17) + t2, reaches_trans h1 h2, Nat.le_trans (hle2 hN) (Nat.le_add_left _ _)⟩

theorem rule_D6_rep (n : Nat) :
    ∀ N R, 2 ≤ N →
      ∃ t, Reaches bb48 (Dcfg N (rep n 6 R)) (Dcfg (iter G6 n N) R) t ∧
           (1 ≤ n → iter G6 n N ≤ t) := by
  induction n with
  | zero => intro N R _; exact ⟨0, reaches_zero bb48 _, fun h => by cases h⟩
  | succ k ih =>
    intro N R hN
    obtain ⟨t1, h1, hle1⟩ := rule_D6 N (by omega) (rep k 6 R)
    have h2 : 2 ≤ G6 N := by have := G6_inc N hN; omega
    obtain ⟨t2, h2', hle2⟩ := ih (G6 N) R h2
    have hcomm : iter G6 k (G6 N) = iter G6 (k + 1) N := by rw [iter_add]; rfl
    rw [hcomm] at h2' hle2
    refine ⟨t1 + t2, reaches_trans h1 h2', fun _ => ?_⟩
    cases k with
    | zero => exact Nat.le_trans hle1 (Nat.le_add_right _ _)
    | succ k' => exact Nat.le_trans (hle2 (Nat.succ_pos k')) (Nat.le_add_left _ _)

theorem rule_D7 (N : Nat) (hN : 1 ≤ N) (R : List Nat) :
    ∃ t, Reaches bb48 (Dcfg N (7 :: R)) (Dcfg (G7 N) R) t ∧ G7 N ≤ t := by
  have h1 := rule_D7_expand N hN R
  obtain ⟨t2, h2, hle2⟩ := rule_D6_rep N 4 R (by omega)
  exact ⟨(3 * N + 15) + t2, reaches_trans h1 h2, Nat.le_trans (hle2 hN) (Nat.le_add_left _ _)⟩

theorem rule_D7_rep (n : Nat) :
    ∀ N R, 2 ≤ N →
      ∃ t, Reaches bb48 (Dcfg N (rep n 7 R)) (Dcfg (iter G7 n N) R) t ∧
           (1 ≤ n → iter G7 n N ≤ t) := by
  induction n with
  | zero => intro N R _; exact ⟨0, reaches_zero bb48 _, fun h => by cases h⟩
  | succ k ih =>
    intro N R hN
    obtain ⟨t1, h1, hle1⟩ := rule_D7 N (by omega) (rep k 7 R)
    have h2 : 2 ≤ G7 N := by have := G7_inc N hN; omega
    obtain ⟨t2, h2', hle2⟩ := ih (G7 N) R h2
    have hcomm : iter G7 k (G7 N) = iter G7 (k + 1) N := by rw [iter_add]; rfl
    rw [hcomm] at h2' hle2
    refine ⟨t1 + t2, reaches_trans h1 h2', fun _ => ?_⟩
    cases k with
    | zero => exact Nat.le_trans hle1 (Nat.le_add_right _ _)
    | succ k' => exact Nat.le_trans (hle2 (Nat.succ_pos k')) (Nat.le_add_left _ _)

/-! ### Bootstrap from Blank Tape & Main Champion Theorem -/

/-- Helper to evaluate `steps` in small chunks without hitting recursion depth limits. -/
private theorem steps_chunk_eval {c1 c2 c3 : Config} {t1 t2 : Nat}
    (h1 : Reaches bb48 c1 c2 t1) (h2 : Reaches bb48 c2 c3 t2) :
    Reaches bb48 c1 c3 (t1 + t2) :=
  reaches_trans h1 h2

set_option maxRecDepth 2000 in
/-- Verified 308-step bootstrap from blank tape to `0^∞ 3^4 D> 6 7^14 6 0^∞`. -/
theorem bb48_bootstrap :
    Reaches bb48 initConfig (Dcfg 4 (6 :: rep 14 7 [6])) 308 := rfl

/-- MAIN THEOREM (BB(4, 8) Champion):
    `bb48` is a valid 4-state, 8-symbol Turing machine that halts from the blank tape
    in exact `t` steps with `t > f_{ω+4}(7)` (strictly surpassing `BB(4,7) > f_{ω+3}(34)`
    by an entire FGH ordinal level). -/
theorem bb48_halts_gt_f_omega_plus_4_7 :
    ValidTM 4 8 bb48 ∧ ∃ t, HaltsIn bb48 initConfig t ∧ f_omega_plus 4 7 < t := by
  refine ⟨bb48_valid, ?_⟩
  have hb := bb48_bootstrap
  obtain ⟨t1, h1, _⟩ := rule_D6 4 (by omega) (rep 14 7 [6])
  have hN1_ge7 : 7 ≤ G6 4 := by have := G6_ge_3x 4 (by omega); omega
  obtain ⟨t2, h2, hle2⟩ := rule_D7_rep 14 (G6 4) [6] (by omega)
  have hN2_ge2 : 2 ≤ iter G7 14 (G6 4) := by
    have h := iter_ge_self G7 (fun z => by
      cases z with
      | zero => exact Nat.zero_le _
      | succ z1 =>
        cases z1 with
        | zero =>
          rw [G7, iter_succ, iter_zero]
          omega
        | succ k => exact Nat.le_trans (Nat.le_succ _) (G7_inc (k + 2) (by omega))) 14 (G6 4)
    omega
  obtain ⟨t3, h3, _⟩ := rule_D6 (iter G7 14 (G6 4)) (by omega) []
  obtain ⟨t4, ⟨cf, h4, hst⟩, _⟩ := rule_D0 (G6 (iter G7 14 (G6 4)))
  have hall := reaches_trans (reaches_trans (reaches_trans (reaches_trans hb h1) h2) h3) h4
  have hf_bound : f_omega_plus 4 7 < iter G7 14 (G6 4) := by
    have h14 : iter G7 14 (G6 4) = iter (fun y => G7 (G7 y)) 7 (G6 4) := by
      rw [iter_two_mul]
    rw [h14]
    have harg : iter (fun y => G7 (G7 y)) 7 7 ≤ iter (fun y => G7 (G7 y)) 7 (G6 4) :=
      iter_mono_arg (fun y => G7 (G7 y)) (fun _ _ h => G7_mono (G7_mono h)) 7 hN1_ge7
    have hstrict : ∀ k, 1 ≤ k → iter (f_omega_plus 3) k 7 < iter (fun y => G7 (G7 y)) k 7 := by
      intro k hk
      cases k with
      | zero => cases hk
      | succ m =>
        have hle : ∀ j, 2 ≤ iter (f_omega_plus 3) j 7 ∧
                        iter (f_omega_plus 3) j 7 ≤ iter (fun y => G7 (G7 y)) j 7 := by
          intro j
          induction j with
          | zero => exact ⟨Nat.le_trans (by omega : 2 ≤ 7) (Nat.le_refl 7), Nat.le_refl 7⟩
          | succ j' ihj =>
            refine ⟨Nat.le_trans ihj.1 ((fOmegaMul_props 1 3).ge_self _), ?_⟩
            exact Nat.le_trans ((fOmegaMul_props 1 3).mono _ _ ihj.2)
              (Nat.le_of_lt (G7_sq_gt _ (Nat.le_trans ihj.1 ihj.2)))
        have hm := hle m
        exact Nat.lt_of_le_of_lt ((fOmegaMul_props 1 3).mono _ _ hm.2)
          (G7_sq_gt _ (Nat.le_trans hm.1 hm.2))
    exact Nat.lt_of_lt_of_le (hstrict 7 (by omega)) harg
  have hle_tot : iter G7 14 (G6 4) ≤ 308 + t1 + t2 + t3 + t4 := by
    have ht2 := hle2 (by omega)
    omega
  exact ⟨308 + t1 + t2 + t3 + t4, ⟨cf, hall, hst⟩, Nat.lt_of_lt_of_le hf_bound hle_tot⟩

end BB4_8
end BB

#print axioms BB.BB4_8.bb48_halts_gt_f_omega_plus_4_7
