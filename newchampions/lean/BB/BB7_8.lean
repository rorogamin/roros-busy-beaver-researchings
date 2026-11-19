/-
  BB/BB7_8.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 8):
    TM: 7LD3LB6LA2RA4LB5RC5LA2LG_1RZ3RB1LD2RA3LF5RB6LD4RG_3RB1LB3LC2RC4LC1LE5RB3RF_3RB3RE3LC2RC7RB3RD1LA7LD_5RB3RE7RD4LC3LG5LE0LA1LG_5RB5RB2RA1LF2LA5LF5RD7LF_5LF3LA7LA1LG7LA5LG7RD0RG
    Domain: BB(7, 8) (7 states, 8 symbols)
    Previous best dominated bounds: BB(7, 7) > f_{ω^2+1}(3), BB(6, 8) > f_{ω×2+2}(11)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(7)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_8

def bb78 : TM
  -- State A (0): 7LD 3LB 6LA 2RA 4LB 5RC 5LA 2LG
  | 0, 0 => some ⟨7, Dir.L, some 3⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨6, Dir.L, some 0⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨5, Dir.R, some 2⟩
  | 0, 6 => some ⟨5, Dir.L, some 0⟩
  | 0, 7 => some ⟨2, Dir.L, some 6⟩
  -- State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD 4RG
  | 1, 0 => some ⟨1, Dir.R, none⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨5, Dir.R, some 1⟩
  | 1, 6 => some ⟨6, Dir.L, some 3⟩
  | 1, 7 => some ⟨4, Dir.R, some 6⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB 3RF
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨1, Dir.L, some 4⟩
  | 2, 6 => some ⟨5, Dir.R, some 1⟩
  | 2, 7 => some ⟨3, Dir.R, some 5⟩
  -- State D (3): 3RB 3RE 3LC 2RC 7RB 3RD 1LA 7LD
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨3, Dir.R, some 4⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨7, Dir.R, some 1⟩
  | 3, 5 => some ⟨3, Dir.R, some 3⟩
  | 3, 6 => some ⟨1, Dir.L, some 0⟩
  | 3, 7 => some ⟨7, Dir.L, some 3⟩
  -- State E (4): 5RB 3RE 7RD 4LC 3LG 5LE 0LA 1LG
  | 4, 0 => some ⟨5, Dir.R, some 1⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨7, Dir.R, some 3⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨3, Dir.L, some 6⟩
  | 4, 5 => some ⟨5, Dir.L, some 4⟩
  | 4, 6 => some ⟨0, Dir.L, some 0⟩
  | 4, 7 => some ⟨1, Dir.L, some 6⟩
  -- State F (5): 5RB 5RB 2RA 1LF 2LA 5LF 5RD 7LF
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨5, Dir.R, some 1⟩
  | 5, 2 => some ⟨2, Dir.R, some 0⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨2, Dir.L, some 0⟩
  | 5, 5 => some ⟨5, Dir.L, some 5⟩
  | 5, 6 => some ⟨5, Dir.R, some 3⟩
  | 5, 7 => some ⟨7, Dir.L, some 5⟩
  -- State G (6): 5LF 3LA 7LA 1LG 7LA 5LG 7RD 0RG
  | 6, 0 => some ⟨5, Dir.L, some 5⟩
  | 6, 1 => some ⟨3, Dir.L, some 0⟩
  | 6, 2 => some ⟨7, Dir.L, some 0⟩
  | 6, 3 => some ⟨1, Dir.L, some 6⟩
  | 6, 4 => some ⟨7, Dir.L, some 0⟩
  | 6, 5 => some ⟨5, Dir.L, some 6⟩
  | 6, 6 => some ⟨7, Dir.R, some 3⟩
  | 6, 7 => some ⟨0, Dir.R, some 6⟩
  | _, _ => none

theorem bb78_valid : ValidTM 7 8 bb78 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 | 6, 7 => simp [bb78]
    | _ + 7, _ => omega
    | _, _ + 8 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7
    | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 | 6, 7 => omega
    | _ + 7, _ => rfl
    | 0, _ + 8 | 1, _ + 8 | 2, _ + 8 | 3, _ + 8 | 4, _ + 8 | 5, _ + 8 | 6, _ + 8 => rfl

theorem bb78_core : Fwp2_7Core bb78 :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Symbol `7` Reload: `Scfg (r+1) 0 m (7 :: R) --> Scfg (r+1) 0 0 (rep (2*m + 1) 2 R)` -/

private theorem loop_G_7 (n : Nat) (L R : List Nat) :
    Reaches bb78 (mkCfgR (some 6) (rep n 3 L) (2 :: R))
                 (mkCfgR (some 6) L (2 :: rep n 2 R)) (3 * n) := by
  induction n generalizing R with
  | zero => exact reaches_zero bb78 _
  | succ k ih =>
    have h1 : step bb78 (mkCfgR (some 6) (3 :: rep k 3 L) (2 :: R)) =
              some (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) :=
      step_mkCfgR_L_cons (tm := bb78) (q := 6) (w := 6) (cur := 2) rfl
    have h2 : step bb78 (mkCfgR (some 0) (rep k 3 L) (3 :: 7 :: R)) =
              some (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) :=
      step_mkCfgR_R (tm := bb78) (q := 0) (w := 1) (cur := 3) rfl
    have h3 : step bb78 (mkCfgR (some 0) (2 :: rep k 3 L) (7 :: R)) =
              some (mkCfgR (some 6) (rep k 3 L) (2 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb78) (q := 0) (w := 1) (cur := 7) rfl
    have h4 := ih (2 :: R); rw [rep_snoc_one] at h4
    have hall := steps_succ bb78 _ _ _ _ h1 (steps_succ bb78 _ _ _ _ h2 (steps_succ bb78 _ _ _ _ h3 h4))
    have ht : 3 * k + 1 + 1 + 1 = 3 * (k + 1) := by omega
    rw [ht] at hall; exact hall

theorem reload_7 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb78 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) t := by
  have h1 : step bb78 (Scfg (r + 1) 0 m (7 :: R)) =
            some (mkCfgR (some 6) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb78) (q := 0) (w := 1) (cur := 7) rfl
  have h2 := loop_G_7 (2 * m + 1) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_snoc_one] at h2
  have h3 : step bb78 (mkCfgR (some 6) (5 :: rep r 5 []) (2 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb78) (q := 6) (w := 6) (cur := 2) rfl
  have h4 : step bb78 (mkCfgR (some 0) (rep r 5 []) (5 :: 7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 0) (w := 4) (cur := 5) rfl
  have h5 : step bb78 (mkCfgR (some 2) (5 :: rep r 5 []) (7 :: rep (2 * m + 2) 2 R)) =
            some (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (rep (2 * m + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 2) (w := 2) (cur := 7) rfl
  have h6 : step bb78 (mkCfgR (some 5) (3 :: 5 :: rep r 5 []) (2 :: rep (2 * m + 1) 2 R)) =
            some (Scfg (r + 1) 0 0 (rep (2 * m + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb78) (q := 5) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb78 _ _ _ _ h1 (reaches_trans h2
    (steps_succ bb78 _ _ _ _ h3 (steps_succ bb78 _ _ _ _ h4
      (steps_succ bb78 _ _ _ _ h5 (steps_one bb78 _ _ h6)))))⟩

def H7 (m : Nat) : Nat := iter H2_7 (2 * m) 17

theorem H7_mono {x y : Nat} (hxy : x ≤ y) : H7 x ≤ H7 y :=
  iter_mono_steps H2_7 (fun z => by have := Pempty_ge (2 * z + 1); unfold H2_7; omega) (by omega) 17

theorem H7_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 1 m < H7 m :=
  climb_double H2_7 f_omega2 17 (by omega) (fun _ _ h => H2_7_mono h) H2_7_inc H2_7_gt
    (fOmega2_props 1 0 0) m hm

theorem rule_7 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb78 (Scfg (r + 1) 0 m (7 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_7 r m R
  obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_7 bb78_core r 0 (rep (2 * m) 2 R)
  have hm1_17 : 17 ≤ m1 := Nat.le_trans H2_7_0_ge hm1
  cases m with
  | zero =>
    have hH7 : H7 0 = 17 := rfl
    exact ⟨r1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ m' =>
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_7_rep bb78_core (2 * (m' + 1)) r1 m1 R
    have harg : iter H2_7 (2 * (m' + 1)) 17 ≤ iter H2_7 (2 * (m' + 1)) m1 :=
      iter_mono_arg H2_7 (fun _ _ h => H2_7_mono h) (2 * (m' + 1)) hm1_17
    exact ⟨r2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans harg hm2, Nat.le_trans (ht2 (by omega)) (Nat.le_add_left _ _)⟩

theorem rule_7_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches bb78 (Scfg (r + 1) 0 m (rep n 7 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H7 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero bb78 _, Nat.le_refl m, fun h => by cases h⟩
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

set_option maxRecDepth 2000 in
theorem bb78_bootstrap :
    Reaches bb78 initConfig (Scfg 1 0 0 (7 :: 2 :: rep 7 7 [2, 1, 5])) 268 := rfl

theorem bb78_halts_gt_f_omega2_plus_2_7 :
    ValidTM 7 8 bb78 ∧ ∃ t, HaltsIn bb78 initConfig t ∧ f_omega2_plus 2 7 < t := by
  refine ⟨bb78_valid, ?_⟩
  have hboot := bb78_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_7 0 0 (2 :: rep 7 7 [2, 1, 5])
  obtain ⟨r2, m2, t2, h2, hm2, _⟩ := rule_2_7 bb78_core r1 m1 (rep 7 7 [2, 1, 5])
  have hm2_7 : 7 ≤ m2 := by
    have h17 : 17 ≤ m1 := by have : H7 0 = 17 := rfl; omega
    have hinc := Pempty_ge (2 * m1 + 1)
    unfold H2_7 at hm2; omega
  obtain ⟨r3, m3, t3, h3, hm3, ht3⟩ := rule_7_rep 7 r2 m2 [2, 1, 5]
  obtain ⟨r4, m4, t4, h4, _, _⟩ := rule_2_7 bb78_core r3 m3 [1, 5]
  obtain ⟨t5, h5, _⟩ := fwp2_step bb78_core.fp (r4 + 1) 0 m4 [5]
  obtain ⟨cf, hhalt, hst⟩ := rule_halt_5_7 bb78_core r4 (Pfn (r4 + 1) 0 m4)
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans (reaches_trans hboot h1) h2) h3) h4) h5) hhalt
  have hlt1 : f_omega2_plus 2 7 < iter H7 7 7 :=
    iter_strict_dom H7 (f_omega2_plus 1) 1 H7_gt (fOmega2_props 1 0 1) 7 7 (by omega) (by omega)
  have hlt2 : iter H7 7 7 ≤ iter H7 7 m2 := iter_mono_arg H7 (fun _ _ h => H7_mono h) 7 hm2_7
  have hlt_m3 : f_omega2_plus 2 7 < m3 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt1 hlt2) hm3
  have hle_t : m3 ≤ t3 := ht3 (by omega)
  refine ⟨_, ⟨cf, hreach, hst⟩, Nat.lt_of_lt_of_le hlt_m3 (Nat.le_trans hle_t (by omega))⟩

#print axioms bb78_halts_gt_f_omega2_plus_2_7

end BB7_8
end BB
