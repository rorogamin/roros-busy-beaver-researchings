/-
  BB/BB7_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 9):
    TM: 8RG3LB6LA2RA4LB5RC5LA2LG7LE_1RZ3RB1LD2RA3LF5RB6LD1RZ5LD_3RB1LB3LC2RC4LC1LE5RB3RF3RD_3RB3RE3LC2RC7LF3RD1LA2RA8LE_5RB3RE8LA4LC3LG5LE1RZ1RZ3LA_5RB5RB2RA1LF8LF5LF1RZ1RF8LC_5LF4RG7LA1LG8RC5LG1LC4RF8RG
    Domain: BB(7, 9) (7 states, 9 symbols)
    Previous best dominated bounds: BB(7, 8) > f_{ω^2+2}(7), BB(6, 9) > f_{ω×2+3}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_9

def bb79 : TM
  -- State A (0): 8RG 3LB 6LA 2RA 4LB 5RC 5LA 2LG 7LE
  | 0, 0 => some ⟨8, Dir.R, some 6⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨6, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.R, some 2⟩
  | 0, 6 => some ⟨5, Dir.L, some 0⟩
  | 0, 7 => some ⟨2, Dir.L, some 6⟩
  | 0, 8 => some ⟨7, Dir.L, some 4⟩
  -- State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD 1RZ 5LD
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨6, Dir.L, some 3⟩
  | 1, 7 => some ⟨1, Dir.R, none⟩
  | 1, 8 => some ⟨5, Dir.L, some 3⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB 3RF 3RD
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 7 => some ⟨3, Dir.R, some 5⟩
  | 2, 8 => some ⟨3, Dir.R, some 3⟩
  -- State D (3): 3RB 3RE 3LC 2RC 7LF 3RD 1LA 2RA 8LE
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨7, Dir.L, some 5⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨1, Dir.L, some 0⟩
  | 3, 7 => some ⟨2, Dir.R, some 0⟩
  | 3, 8 => some ⟨8, Dir.L, some 4⟩
  -- State E (4): 5RB 3RE 8LA 4LC 3LG 5LE 1RZ 1RZ 3LA
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨8, Dir.L, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨1, Dir.R, none⟩
  | 4, 7 => some ⟨1, Dir.R, none⟩
  | 4, 8 => some ⟨3, Dir.L, some 0⟩
  -- State F (5): 5RB 5RB 2RA 1LF 8LF 5LF 1RZ 1RF 8LC
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨2, Dir.R, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨8, Dir.L, some 5⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨1, Dir.R, none⟩
  | 5, 7 => some ⟨1, Dir.R, some 5⟩
  | 5, 8 => some ⟨8, Dir.L, some 2⟩
  -- State G (6): 5LF 4RG 7LA 1LG 8RC 5LG 1LC 4RF 8RG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨4, Dir.R, some 6⟩
  | 6, 2 => some ⟨7, Dir.L, some 0⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨8, Dir.R, some 2⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨1, Dir.L, some 2⟩
  | 6, 7 => some ⟨4, Dir.R, some 5⟩
  | 6, 8 => some ⟨8, Dir.R, some 6⟩
  | _, _ => none

theorem bb79_valid : ValidTM 7 9 bb79 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 | 0, 8
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 | 3, 8
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7 | 4, 8
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 | 5, 8
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 | 6, 7 | 6, 8 => simp [bb79]
    | _ + 7, _ => omega
    | _, _ + 9 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 | 0, 8
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 | 3, 8
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7 | 4, 8
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 | 5, 8
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 | 6, 7 | 6, 8 => omega
    | _ + 7, _ => rfl
    | 0, _ + 9 | 1, _ + 9 | 2, _ + 9 | 3, _ + 9 | 4, _ + 9 | 5, _ + 9 | 6, _ + 9 => rfl

theorem bb79_core : Fwp2_7Core bb79 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_G_7 (n : Nat) (L R : List Nat) :
    Reaches bb79 (mkCfgR (some 6) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 6) L (2 :: rep n 2 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb79 _
  | succ k ih =>
    have h1 : step bb79 (mkCfgR (some 6) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 6) (w := 6) (cur := 2) rfl
    have h2 : step bb79 (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) :=
      step_mkCfgR_R (tm := bb79) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb79 (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) =
              some (mkCfgR (some 6) (rep k 3 L) (2 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 1) (cur := 7) rfl
    have h4 := ih (2 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb79 _ _ _ _ h1 (steps_succ bb79 _ _ _ _ h2 (steps_succ bb79 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

private theorem loop_E_8 (n : Nat) (L R : List Nat) :
    Reaches bb79 (mkCfgR (some 4) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 4) L (2 :: rep n 7 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb79 _
  | succ k ih =>
    have h1 : step bb79 (mkCfgR (some 4) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 8 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 4) (w := 7) (cur := 2) rfl
    have h2 : step bb79 (mkCfgR (some 0) (rep k 3 L) (3 :: 8 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (8 :: R)) :=
      step_mkCfgR_R (tm := bb79) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb79 (mkCfgR (some 0) (2 :: rep k 3 L) (8 :: R)) =
              some (mkCfgR (some 4) (rep k 3 L) (2 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 6) (cur := 8) rfl
    have h4 := ih (7 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb79 _ _ _ _ h1 (steps_succ bb79 _ _ _ _ h2 (steps_succ bb79 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb79 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) t := by
  have h1 : step bb79 (Scfg (r + 1) 0 m (7 :: R)) =
            some (mkCfgR (some 6) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 1) (cur := 7) rfl
  have h2 := loop_G_7 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb79 (mkCfgR (some 6) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 6) (w := 6) (cur := 2) rfl
  have h4 : step bb79 (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb79 (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 2) (w := 2) (cur := 7) rfl
  have h6 : step bb79 (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (2 :: rep (2 * m + 1) 2 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 5) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb79 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb79 _ _ _ _ h3 (steps_succ bb79 _ _ _ _ h4
      (steps_succ bb79 _ _ _ _ h5 (steps_one bb79 _ _ h6)))))⟩

theorem reload_8 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb79 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 7 R)) t := by
  have h1 : step bb79 (Scfg (r + 1) 0 m (8 :: R)) =
            some (mkCfgR (some 4) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 0) (w := 6) (cur := 8) rfl
  have h2 := loop_E_8 (2 * m + 1) (rep (r + 1) 5 []) (7 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb79 (mkCfgR (some 4) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 8 :: rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_L_cons (tm := bb79) (q := 4) (w := 7) (cur := 2) rfl
  have h4 : step bb79 (mkCfgR (some 0) (rep r 5 []) (5 :: 8 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (8 :: rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb79 (mkCfgR (some 2) (5 :: rep r 5 []) (8 :: rep (2 * m + 2) 7 R)) =
            some (mkCfgR (some 3) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 2) (w := 2) (cur := 8) rfl
  have h6 : step bb79 (mkCfgR (some 3) (3 :: 5 :: rep r 5 []) (7 :: rep (2 * m + 1) 7 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 7 R)) :=
    step_mkCfgR_R (tm := bb79) (q := 3) (w := 1) (cur := 7) rfl
  exact ⟨_, steps_succ bb79 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb79 _ _ _ _ h3 (steps_succ bb79 _ _ _ _ h4
      (steps_succ bb79 _ _ _ _ h5 (steps_one bb79 _ _ h6)))))⟩

def H7 (m : Nat) : Nat := iter H2_7 (2 * m) 17
def H8 (m : Nat) : Nat := iter H7 (2 * m) 17

theorem H7_mono {x y : Nat} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H2_7 (fun z => by have := Pempty_ge (2 * z + 1); unfold H2_7; omega) (by omega) 17
theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 1 m < H7 m :=
  climb_double H2_7 f_omega2 17 (by omega) (fun _ _ h => H2_7_mono h) H2_7_inc H2_7_gt
    (fOmega2_props 1 0 0) m hm
theorem H7_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H7 m := by
  have h1 := H7_gt m hm; have h2 : m ≤ f_omega2_plus 1 m := (fOmega2_props 1 0 1).ge_self m; omega

theorem H8_mono {x y : Nat} (hxy : x ≤ y) : H8 x ≤ H8 y :=
  iter_mono_steps H7 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H7_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 17
theorem H8_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 2 m < H8 m :=
  climb_double H7 (f_omega2_plus 1) 17 (by omega) (fun _ _ h => H7_mono h) H7_inc H7_gt
    (fOmega2_props 1 0 1) m hm

theorem rule_7 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_7 bb79_core r 0 (rep (2 * m) 2 R)
  have hm1_17 : 17 ≤ m1 := Nat.le_trans H2_7_0_ge hm1
  cases m with
  | zero =>
    have hH7 : H7 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb79_core (2 * (m' + 1)) r1 m1 R
    have harg := iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (rep n 7 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb79 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 r m (rep (p' + 1) 7 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H7 (p' + 1) (H7 m) = iter H7 (p' + 2) m := (iter_add H7 (p' + 1) 1 m).symm
      have hmb : iter H7 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H7 (fun _ _ h => H7_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_8 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (8 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H8 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_8 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_7 r 0 (rep (2 * m) 7 R)
  have hm1_17 : 17 ≤ m1 := by have : H7 0 = 17 := rfl; omega
  cases m with
  | zero =>
    have hH8 : H8 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_7_rep (2 * (m' + 1)) r1 m1 R
    have harg := iter_mono_arg H7 (fun _ _ h => H7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_8_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb79 (Scfg (r + 1) 0 m (rep n 8 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H8 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb79 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_8 r m R
      exact ⟨r1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8 r m (rep (p' + 1) 8 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih r1 m1 R
      have hcomm : iter H8 (p' + 1) (H8 m) = iter H8 (p' + 2) m := (iter_add H8 (p' + 1) 1 m).symm
      have hmb : iter H8 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H8 (fun _ _ h => H8_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem bb79_bootstrap :
    Reaches bb79 initConfig (Scfg 1 0 0 (rep 8 8 [5])) 74 := rfl

theorem bb79_halts_gt_f_omega2_plus_3_7 :
    ValidTM 7 9 bb79 ∧ ∃ t, HaltsIn bb79 initConfig t ∧ f_omega2_plus 3 7 < t := by
  refine ⟨bb79_valid, ?_⟩
  have hboot := bb79_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_8 0 0 (rep 7 8 [5])
  have hm1_7 : 7 ≤ m1 := by have : H8 0 = 17 := rfl; omega
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_8_rep 7 r1 m1 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb79_core r2 m2
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2_plus 3 7 < iter H8 7 7 :=
    iter_strict_dom H8 (f_omega2_plus 2) 1 H8_gt (fOmega2_props 1 0 2) 7 7 (by omega) (by omega)
  have hlt2 : iter H8 7 7 ≤ iter H8 7 m1 := iter_mono_arg H8 (fun _ _ h => H8_mono h) 7 hm1_7
  have hlt_m2 : f_omega2_plus 3 7 < m2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm2
  have hle_t : m2 ≤ t2 := ht2 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb79_halts_gt_f_omega2_plus_3_7

end BB7_9
end BB
