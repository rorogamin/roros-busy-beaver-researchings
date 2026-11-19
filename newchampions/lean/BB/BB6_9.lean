/-
  BB/BB6_9.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(6, 9):
    TM: 8LE3LB7LF2RA4LB6LF1RZ1LC8LF_6LE3RB1LD2RA3LF2RA3LB3RA8RD_3RB1LB3LC2RC4LC0LE5LC3RB6RE_3RB6RD3LC2RC5LC3RE2LE1LB5LC_5RC3RE2RA4LC8LE8RE2LE3RE1RB_5RB7RD1LF1LF8LE5RF8RE1RZ8RB
    Domain: BB(6, 9) (6 states, 9 symbols)
    Previous best dominated bounds: BB(6, 8) > f_{ω×2+2}(11), BB(3, 9) > f_{ω+2}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+3}(6)
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwm2

namespace BB
namespace BB6_9

/-- The 6-state, 9-symbol Turing machine `bb69`:
    8LE3LB7LF2RA4LB6LF1RZ1LC8LF_6LE3RB1LD2RA3LF2RA3LB3RA8RD_3RB1LB3LC2RC4LC0LE5LC3RB6RE_3RB6RD3LC2RC5LC3RE2LE1LB5LC_5RC3RE2RA4LC8LE8RE2LE3RE1RB_5RB7RD1LF1LF8LE5RF8RE1RZ8RB -/
def bb69 : TM
  -- State A (0): 8LE 3LB 7LF 2RA 4LB 6LF 1RZ 1LC 8LF
  | 0, 0 => some ⟨8, Dir.L, some 4⟩
  | 0, 1 => some ⟨3, Dir.L, some 1⟩
  | 0, 2 => some ⟨7, Dir.L, some 5⟩
  | 0, 3 => some ⟨2, Dir.R, some 0⟩
  | 0, 4 => some ⟨4, Dir.L, some 1⟩
  | 0, 5 => some ⟨6, Dir.L, some 5⟩
  | 0, 6 => some ⟨1, Dir.R, none⟩
  | 0, 7 => some ⟨1, Dir.L, some 2⟩
  | 0, 8 => some ⟨8, Dir.L, some 5⟩
  -- State B (1): 6LE 3RB 1LD 2RA 3LF 2RA 3LB 3RA 8RD
  | 1, 0 => some ⟨6, Dir.L, some 4⟩
  | 1, 1 => some ⟨3, Dir.R, some 1⟩
  | 1, 2 => some ⟨1, Dir.L, some 3⟩
  | 1, 3 => some ⟨2, Dir.R, some 0⟩
  | 1, 4 => some ⟨3, Dir.L, some 5⟩
  | 1, 5 => some ⟨2, Dir.R, some 0⟩
  | 1, 6 => some ⟨3, Dir.L, some 1⟩
  | 1, 7 => some ⟨3, Dir.R, some 0⟩
  | 1, 8 => some ⟨8, Dir.R, some 3⟩
  -- State C (2): 3RB 1LB 3LC 2RC 4LC 0LE 5LC 3RB 6RE
  | 2, 0 => some ⟨3, Dir.R, some 1⟩
  | 2, 1 => some ⟨1, Dir.L, some 1⟩
  | 2, 2 => some ⟨3, Dir.L, some 2⟩
  | 2, 3 => some ⟨2, Dir.R, some 2⟩
  | 2, 4 => some ⟨4, Dir.L, some 2⟩
  | 2, 5 => some ⟨0, Dir.L, some 4⟩
  | 2, 6 => some ⟨5, Dir.L, some 2⟩
  | 2, 7 => some ⟨3, Dir.R, some 1⟩
  | 2, 8 => some ⟨6, Dir.R, some 4⟩
  -- State D (3): 3RB 6RD 3LC 2RC 5LC 3RE 2LE 1LB 5LC
  | 3, 0 => some ⟨3, Dir.R, some 1⟩
  | 3, 1 => some ⟨6, Dir.R, some 3⟩
  | 3, 2 => some ⟨3, Dir.L, some 2⟩
  | 3, 3 => some ⟨2, Dir.R, some 2⟩
  | 3, 4 => some ⟨5, Dir.L, some 2⟩
  | 3, 5 => some ⟨3, Dir.R, some 4⟩
  | 3, 6 => some ⟨2, Dir.L, some 4⟩
  | 3, 7 => some ⟨1, Dir.L, some 1⟩
  | 3, 8 => some ⟨5, Dir.L, some 2⟩
  -- State E (4): 5RC 3RE 2RA 4LC 8LE 8RE 2LE 3RE 1RB
  | 4, 0 => some ⟨5, Dir.R, some 2⟩
  | 4, 1 => some ⟨3, Dir.R, some 4⟩
  | 4, 2 => some ⟨2, Dir.R, some 0⟩
  | 4, 3 => some ⟨4, Dir.L, some 2⟩
  | 4, 4 => some ⟨8, Dir.L, some 4⟩
  | 4, 5 => some ⟨8, Dir.R, some 4⟩
  | 4, 6 => some ⟨2, Dir.L, some 4⟩
  | 4, 7 => some ⟨3, Dir.R, some 4⟩
  | 4, 8 => some ⟨1, Dir.R, some 1⟩
  -- State F (5): 5RB 7RD 1LF 1LF 8LE 5RF 8RE 1RZ 8RB
  | 5, 0 => some ⟨5, Dir.R, some 1⟩
  | 5, 1 => some ⟨7, Dir.R, some 3⟩
  | 5, 2 => some ⟨1, Dir.L, some 5⟩
  | 5, 3 => some ⟨1, Dir.L, some 5⟩
  | 5, 4 => some ⟨8, Dir.L, some 4⟩
  | 5, 5 => some ⟨5, Dir.R, some 5⟩
  | 5, 6 => some ⟨8, Dir.R, some 4⟩
  | 5, 7 => some ⟨1, Dir.R, none⟩
  | 5, 8 => some ⟨8, Dir.R, some 1⟩
  | _, _ => none

theorem bb69_valid : ValidTM 6 9 bb69 := by
  constructor
  · intro s sym hs hsym
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 | 0, 8
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 | 3, 8
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7 | 4, 8
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 | 5, 8 => simp [bb69]
    | _ + 6, _ => omega
    | _, _ + 9 => omega
  · intro s sym h
    match s, sym with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 | 0, 8
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5 | 3, 6 | 3, 7 | 3, 8
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5 | 4, 6 | 4, 7 | 4, 8
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 | 5, 7 | 5, 8 => omega
    | _ + 6, _ => rfl
    | 0, _ + 9 | 1, _ + 9 | 2, _ + 9 | 3, _ + 9 | 4, _ + 9 | 5, _ + 9 => rfl

theorem bb69_fwm2 : Fwm2Core bb69 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem rep_add (a b s : Nat) (R : List Nat) :
    rep a s (rep b s R) = rep (a + b) s R := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

private theorem loop_F2 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 5) (rep n 2 L) (2 :: R))
                 (mkCfgR (some 5) L (2 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 5) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 5) (rep k 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb69) (q := 5) (w := 0) (cur := 2) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb69) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem loop_D1 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 3) L (rep n 1 R))
                 (mkCfgR (some 3) (rep n 6 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 3) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 3) (6 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb69) (q := 3) (w := 5) (cur := 1) rfl
    have h2 := ih (6 :: L); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem loop_B6 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 1) (rep n 6 L) (6 :: R))
                 (mkCfgR (some 1) L (6 :: rep n 3 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 1) (6 :: rep k 6 L) (6 :: R)) =
              some (mkCfgR (some 1) (rep k 6 L) (6 :: 3 :: R)) :=
      step_mkCfgR_L_cons (tm := bb69) (q := 1) (w := 2) (cur := 6) rfl
    have h2 := ih (3 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem loop_E6 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 4) (rep n 6 L) (6 :: R))
                 (mkCfgR (some 4) L (6 :: rep n 2 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 4) (6 :: rep k 6 L) (6 :: R)) =
              some (mkCfgR (some 4) (rep k 6 L) (6 :: 2 :: R)) :=
      step_mkCfgR_L_cons (tm := bb69) (q := 4) (w := 1) (cur := 6) rfl
    have h2 := ih (2 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem loop_C6 (n : Nat) (L R : List Nat) :
    Reaches bb69 (mkCfgR (some 2) (rep n 6 L) (6 :: R))
                 (mkCfgR (some 2) L (6 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb69 _
  | succ k ih =>
    have h1 : step bb69 (mkCfgR (some 2) (6 :: rep k 6 L) (6 :: R)) =
              some (mkCfgR (some 2) (rep k 6 L) (6 :: 5 :: R)) :=
      step_mkCfgR_L_cons (tm := bb69) (q := 2) (w := 4) (cur := 6) rfl
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb69 k _ _ _ h1 h2

private theorem sweep_FD (k m mark : Nat) (R : List Nat) :
    ∃ t, Reaches bb69
      (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: mark :: R))
      (mkCfgR (some 3) (rep (2 * m + k + 1) 6 [7, 5]) (mark :: R)) t := by
  have h2 := loop_F2 k (rep (2 * m + 1) 3 [5]) (mark :: R)
  have h3 : step bb69 (mkCfgR (some 5) (3 :: rep (2 * m) 3 [5]) (2 :: rep k 1 (mark :: R))) =
            some (mkCfgR (some 5) (rep (2 * m) 3 [5]) (3 :: rep (k + 1) 1 (mark :: R))) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 5) (w := 0) (cur := 2) rfl
  have h4 := loop_F3 (2 * m) [5] (rep (k + 1) 1 (mark :: R))
  rw [rep_add] at h4
  have hrep1 : 2 * m + (k + 1) = 2 * m + k + 1 := by omega
  rw [hrep1] at h4
  have h5 : step bb69 (mkCfgR (some 5) [5] (3 :: rep (2 * m + k + 1) 1 (mark :: R))) =
            some (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (mark :: R))) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 5) (w := 0) (cur := 3) rfl
  have h6 : step bb69 (mkCfgR (some 5) [] (5 :: rep (2 * m + k + 2) 1 (mark :: R))) =
            some (mkCfgR (some 5) [5] (rep (2 * m + k + 2) 1 (mark :: R))) :=
    step_mkCfgR_R (tm := bb69) (q := 5) (w := 4) (cur := 5) rfl
  have h7 : step bb69 (mkCfgR (some 5) [5] (1 :: rep (2 * m + k + 1) 1 (mark :: R))) =
            some (mkCfgR (some 3) [7, 5] (rep (2 * m + k + 1) 1 (mark :: R))) :=
    step_mkCfgR_R (tm := bb69) (q := 5) (w := 6) (cur := 1) rfl
  have h8 := loop_D1 (2 * m + k + 1) [7, 5] (mark :: R)
  exact ⟨_, reaches_trans (reaches_trans h2 (steps_succ bb69 _ _ _ _ h3 h4))
    (steps_succ bb69 _ _ _ _ h5 (steps_succ bb69 _ _ _ _ h6 (steps_succ bb69 _ _ _ _ h7 h8)))⟩

theorem reload_2 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb69 (B5cfg k m (2 :: R)) (B5cfg (2 * m + k) 0 (1 :: R)) t := by
  have h1 : step bb69 (B5cfg k m (2 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 7 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 0) (w := 6) (cur := 2) rfl
  obtain ⟨ts, hs⟩ := sweep_FD k m 7 R
  have h9 : step bb69 (mkCfgR (some 3) (6 :: rep (2 * m + k) 6 [7, 5]) (7 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + k) 6 [7, 5]) (6 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 3) (w := 0) (cur := 7) rfl
  have h10 := loop_B6 (2 * m + k) [7, 5] (1 :: R)
  have h11 : step bb69 (mkCfgR (some 1) [7, 5] (6 :: rep (2 * m + k) 3 (1 :: R))) =
             some (mkCfgR (some 1) [5] (7 :: rep (2 * m + k + 1) 3 (1 :: R))) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 1) (w := 2) (cur := 6) rfl
  have h12 : step bb69 (mkCfgR (some 1) [5] (7 :: rep (2 * m + k + 1) 3 (1 :: R))) =
             some (mkCfgR (some 0) [3, 5] (rep (2 * m + k + 1) 3 (1 :: R))) :=
    step_mkCfgR_R (tm := bb69) (q := 1) (w := 2) (cur := 7) rfl
  have h13 := loop_A3 bb69_fwm2.kc (2 * m + k + 1) [3, 5] (1 :: R)
  exact ⟨_, steps_succ bb69 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb69 _ _ _ _ h9 (reaches_trans h10
      (steps_succ bb69 _ _ _ _ h11 (steps_succ bb69 _ _ _ _ h12 h13)))))⟩

theorem reload_5 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb69 (B5cfg k m (5 :: R)) (B5cfg 0 0 (rep (2 * m + k + 1) 2 R)) t := by
  have h1 : step bb69 (B5cfg k m (5 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 6 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 0) (w := 5) (cur := 5) rfl
  obtain ⟨ts, hs⟩ := sweep_FD k m 6 R
  have h9 : step bb69 (mkCfgR (some 3) (6 :: rep (2 * m + k) 6 [7, 5]) (6 :: R)) =
            some (mkCfgR (some 4) (rep (2 * m + k) 6 [7, 5]) (6 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 3) (w := 1) (cur := 6) rfl
  have h10 := loop_E6 (2 * m + k) [7, 5] (2 :: R)
  rw [rep_snoc_one] at h10
  have h11 : step bb69 (mkCfgR (some 4) [7, 5] (6 :: rep (2 * m + k + 1) 2 R)) =
             some (mkCfgR (some 4) [5] (7 :: rep (2 * m + k + 2) 2 R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 4) (w := 1) (cur := 6) rfl
  have h12 : step bb69 (mkCfgR (some 4) [5] (7 :: rep (2 * m + k + 2) 2 R)) =
             some (mkCfgR (some 4) [3, 5] (rep (2 * m + k + 2) 2 R)) :=
    step_mkCfgR_R (tm := bb69) (q := 4) (w := 2) (cur := 7) rfl
  have h13 : step bb69 (mkCfgR (some 4) [3, 5] (2 :: rep (2 * m + k + 1) 2 R)) =
             some (B5cfg 0 0 (rep (2 * m + k + 1) 2 R)) :=
    step_mkCfgR_R (tm := bb69) (q := 4) (w := 1) (cur := 2) rfl
  exact ⟨_, steps_succ bb69 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb69 _ _ _ _ h9 (reaches_trans h10
      (steps_succ bb69 _ _ _ _ h11 (steps_succ bb69 _ _ _ _ h12 (steps_one bb69 _ _ h13))))))⟩

theorem reload_8 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb69 (B5cfg k m (8 :: R)) (B5cfg 0 0 (rep (2 * m + k + 1) 5 R)) t := by
  have h1 : step bb69 (B5cfg k m (8 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 8 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 0) (w := 7) (cur := 8) rfl
  obtain ⟨ts, hs⟩ := sweep_FD k m 8 R
  have h9 : step bb69 (mkCfgR (some 3) (6 :: rep (2 * m + k) 6 [7, 5]) (8 :: R)) =
            some (mkCfgR (some 2) (rep (2 * m + k) 6 [7, 5]) (6 :: 5 :: R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 3) (w := 4) (cur := 8) rfl
  have h10 := loop_C6 (2 * m + k) [7, 5] (5 :: R)
  rw [rep_snoc_one] at h10
  have h11 : step bb69 (mkCfgR (some 2) [7, 5] (6 :: rep (2 * m + k + 1) 5 R)) =
             some (mkCfgR (some 2) [5] (7 :: rep (2 * m + k + 2) 5 R)) :=
    step_mkCfgR_L_cons (tm := bb69) (q := 2) (w := 4) (cur := 6) rfl
  have h12 : step bb69 (mkCfgR (some 2) [5] (7 :: rep (2 * m + k + 2) 5 R)) =
             some (mkCfgR (some 1) [3, 5] (rep (2 * m + k + 2) 5 R)) :=
    step_mkCfgR_R (tm := bb69) (q := 2) (w := 2) (cur := 7) rfl
  have h13 : step bb69 (mkCfgR (some 1) [3, 5] (5 :: rep (2 * m + k + 1) 5 R)) =
             some (B5cfg 0 0 (rep (2 * m + k + 1) 5 R)) :=
    step_mkCfgR_R (tm := bb69) (q := 1) (w := 1) (cur := 5) rfl
  exact ⟨_, steps_succ bb69 _ _ _ _ h1 (reaches_trans hs
    (steps_succ bb69 _ _ _ _ h9 (reaches_trans h10
      (steps_succ bb69 _ _ _ _ h11 (steps_succ bb69 _ _ _ _ h12 (steps_one bb69 _ _ h13))))))⟩

/-! ### Growth Functions `H2` (`> f_{ω×2}`), `H5` (`> f_{ω×2+1}`), `H8` (`> f_{ω×2+2}`) -/

def H2 (m : Nat) : Nat := Wfn (2 * m) 0
def H5 (m : Nat) : Nat := iter H2 (2 * m) 15
def H8 (m : Nat) : Nat := iter H5 (2 * m) 15

theorem H2_mono {x y : Nat} (hxy : x ≤ y) : H2 x ≤ H2 y := Wfn_mono_k (by omega) 0
theorem H2_inc (m : Nat) (_hm : 1 ≤ m) : m + 1 ≤ H2 m := by
  have h := Wfn_zero_ge (2 * m); unfold H2; omega
theorem H2_gt (m : Nat) (hm : 1 ≤ m) : f_omega_mul2 m < H2 m :=
  Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 m) (Wfn_mono_k (by omega) 0)

theorem H5_mono {x y : Nat} (hxy : x ≤ y) : H5 x ≤ H5 y :=
  iter_mono_steps H2 (fun z => by have := Wfn_zero_ge (2 * z); unfold H2; omega) (by omega) 15
theorem H5_gt (m : Nat) (hm : 1 ≤ m) : f_omega_mul2_plus 1 m < H5 m :=
  climb_double H2 f_omega_mul2 15 (by omega) (fun _ _ h => H2_mono h) H2_inc H2_gt
    (fOmegaMul_props 2 0) m hm
theorem H5_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H5 m := by
  have h1 := H5_gt m hm
  have h2 : m ≤ f_omega_mul2_plus 1 m := (fOmegaMul_props 2 1).ge_self m
  omega

theorem H8_mono {x y : Nat} (hxy : x ≤ y) : H8 x ≤ H8 y :=
  iter_mono_steps H5 (fun z => by
    cases z with
    | zero => exact Nat.zero_le _
    | succ z' => exact Nat.le_trans (Nat.le_succ _) (H5_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 15
theorem H8_gt (m : Nat) (hm : 1 ≤ m) : f_omega_mul2_plus 2 m < H8 m :=
  climb_double H5 (f_omega_mul2_plus 1) 15 (by omega) (fun _ _ h => H5_mono h) H5_inc H5_gt
    (fOmegaMul_props 2 1) m hm

theorem rule_2 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb69 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧ H2 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 k m R
  obtain ⟨t2, h2, hle2⟩ := fwm2_step bb69_fwm2 (2 * m + k) 0 R
  exact ⟨2 * m + k, Wfn (2 * m + k) 0, t1 + t2, reaches_trans h1 h2,
    Wfn_mono_k (by omega) 0, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem rule_2_rep (n : Nat) :
    ∀ k m R, ∃ k' m' t, Reaches bb69 (B5cfg k m (rep n 2 R)) (B5cfg k' m' R) t ∧
      iter H2 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro k m R; exact ⟨k, m, 0, reaches_zero bb69 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro k m R
    cases p with
    | zero =>
      obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_2 k m R
      exact ⟨k1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_2 k m (rep (p' + 1) 2 R)
      obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := ih k1 m1 R
      have hcomm : iter H2 (p' + 1) (H2 m) = iter H2 (p' + 2) m := (iter_add H2 (p' + 1) 1 m).symm
      have hmb : iter H2 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H2 (fun _ _ h => H2_mono h) (p' + 1) hm1) hm2
      exact ⟨k2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_5 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb69 (B5cfg k m (5 :: R)) (B5cfg k' m' R) t ∧ H5 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_5 k m R
  obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_2 0 0 (rep (2 * m + k) 2 R)
  have hm1_15 : 15 ≤ m1 := by have : H2 0 = 15 := rfl; omega
  cases hmk : 2 * m + k with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    have hH5 : H5 0 = 15 := rfl
    rw [hmk] at h0 h1
    exact ⟨k1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ r =>
    rw [hmk] at h0 h1
    obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := rule_2_rep (r + 1) k1 m1 R
    have hstep : iter H2 (2 * m) 15 ≤ iter H2 (r + 1) 15 :=
      iter_mono_steps H2 (fun z => by have := Wfn_zero_ge (2 * z); unfold H2; omega) (by omega) 15
    have harg : iter H2 (r + 1) 15 ≤ iter H2 (r + 1) m1 :=
      iter_mono_arg H2 (fun _ _ h => H2_mono h) (r + 1) hm1_15
    exact ⟨k2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans (Nat.le_trans hstep harg) hm2,
      Nat.le_trans (ht2 (Nat.succ_pos r)) (Nat.le_add_left _ _)⟩

theorem rule_5_rep (n : Nat) :
    ∀ k m R, ∃ k' m' t, Reaches bb69 (B5cfg k m (rep n 5 R)) (B5cfg k' m' R) t ∧
      iter H5 n m ≤ m' ∧ (1 ≤ n → m' ≤ t) := by
  induction n with
  | zero => intro k m R; exact ⟨k, m, 0, reaches_zero bb69 _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro k m R
    cases p with
    | zero =>
      obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_5 k m R
      exact ⟨k1, m1, t1, h1, hm1, fun _ => ht1⟩
    | succ p' =>
      obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_5 k m (rep (p' + 1) 5 R)
      obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := ih k1 m1 R
      have hcomm : iter H5 (p' + 1) (H5 m) = iter H5 (p' + 2) m := (iter_add H5 (p' + 1) 1 m).symm
      have hmb : iter H5 (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H5 (fun _ _ h => H5_mono h) (p' + 1) hm1) hm2
      exact ⟨k2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        Nat.le_trans (ht2 (Nat.succ_pos p')) (Nat.le_add_left _ _)⟩

theorem rule_8 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb69 (B5cfg k m (8 :: R)) (B5cfg k' m' R) t ∧ H8 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t0, h0⟩ := reload_8 k m R
  obtain ⟨k1, m1, t1, h1, hm1, ht1⟩ := rule_5 0 0 (rep (2 * m + k) 5 R)
  have hm1_15 : 15 ≤ m1 := by have : H5 0 = 15 := rfl; omega
  cases hmk : 2 * m + k with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    have hH8 : H8 0 = 15 := rfl
    rw [hmk] at h0 h1
    exact ⟨k1, m1, t0 + t1, reaches_trans h0 h1, by omega, Nat.le_trans ht1 (Nat.le_add_left _ _)⟩
  | succ r =>
    rw [hmk] at h0 h1
    obtain ⟨k2, m2, t2, h2, hm2, ht2⟩ := rule_5_rep (r + 1) k1 m1 R
    have hstep : iter H5 (2 * m) 15 ≤ iter H5 (r + 1) 15 :=
      iter_mono_steps H5 (fun z => by
        cases z with
        | zero => exact Nat.zero_le _
        | succ z' => exact Nat.le_trans (Nat.le_succ _) (H5_inc (z' + 1) (Nat.succ_pos z'))) (by omega) 15
    have harg : iter H5 (r + 1) 15 ≤ iter H5 (r + 1) m1 :=
      iter_mono_arg H5 (fun _ _ h => H5_mono h) (r + 1) hm1_15
    exact ⟨k2, m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
      Nat.le_trans (Nat.le_trans hstep harg) hm2,
      Nat.le_trans (ht2 (Nat.succ_pos r)) (Nat.le_add_left _ _)⟩

/-- Helper: consuming any `2` never decreases `m`. -/
private theorem rule_2_ge (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb69 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧ m ≤ m' := by
  obtain ⟨k', m', t, h, hm, _⟩ := rule_2 k m R
  have hge := Wfn_zero_ge (2 * m)
  exact ⟨k', m', t, h, by unfold H2 at hm; omega⟩

/-! ### Exact 304-Step Bootstrap & Main Theorem -/

set_option maxRecDepth 2000 in
theorem bb69_bootstrap :
    Reaches bb69 initConfig (B5cfg 0 0 [8, 2, 8, 2, 8, 2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]) 304 := rfl

theorem bb69_halts_gt_f_omega_mul2_plus_3_6 :
    ValidTM 6 9 bb69 ∧ ∃ t, HaltsIn bb69 initConfig t ∧ f_omega_mul2_plus 3 6 < t := by
  refine ⟨bb69_valid, ?_⟩
  have hboot := bb69_bootstrap
  -- 1st `8`: m1 ≥ 15 ≥ 6
  obtain ⟨k1, m1, t1, h1, hm1, _⟩ := rule_8 0 0 [2, 8, 2, 8, 2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  have hm1_6 : 6 ≤ m1 := by have : H8 0 = 15 := rfl; omega
  obtain ⟨k2, m2, t2, h2, hm2⟩ := rule_2_ge k1 m1 [8, 2, 8, 2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  -- 2nd `8`: ≥ H8 6
  obtain ⟨k3, m3, t3, h3, hm3, _⟩ := rule_8 k2 m2 [2, 8, 2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  have h3b : iter H8 1 6 ≤ m3 := by
    rw [iter_succ, iter_zero]; exact Nat.le_trans (H8_mono (Nat.le_trans hm1_6 hm2)) hm3
  obtain ⟨k4, m4, t4, h4, hm4⟩ := rule_2_ge k3 m3 [8, 2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  -- 3rd `8`: ≥ H8^2 6
  obtain ⟨k5, m5, t5, h5, hm5, _⟩ := rule_8 k4 m4 [2, 2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  have h5b : iter H8 2 6 ≤ m5 := by
    rw [iter_succ]; exact Nat.le_trans (H8_mono (Nat.le_trans h3b hm4)) hm5
  obtain ⟨k6, m6, t6, h6, hm6⟩ := rule_2_ge k5 m5 [2, 2, 2, 8, 2, 8, 2, 8, 8, 6]
  obtain ⟨k7, m7, t7, h7, hm7⟩ := rule_2_ge k6 m6 [2, 2, 8, 2, 8, 2, 8, 8, 6]
  obtain ⟨k8, m8, t8, h8, hm8⟩ := rule_2_ge k7 m7 [2, 8, 2, 8, 2, 8, 8, 6]
  obtain ⟨k9, m9, t9, h9, hm9⟩ := rule_2_ge k8 m8 [8, 2, 8, 2, 8, 8, 6]
  -- 4th `8`: ≥ H8^3 6
  obtain ⟨k10, m10, t10, h10, hm10, _⟩ := rule_8 k9 m9 [2, 8, 2, 8, 8, 6]
  have h59 : iter H8 2 6 ≤ m9 := Nat.le_trans h5b (Nat.le_trans hm6 (Nat.le_trans hm7 (Nat.le_trans hm8 hm9)))
  have h10b : iter H8 3 6 ≤ m10 := by
    rw [iter_succ]; exact Nat.le_trans (H8_mono h59) hm10
  obtain ⟨k11, m11, t11, h11, hm11⟩ := rule_2_ge k10 m10 [8, 2, 8, 8, 6]
  -- 5th `8`: ≥ H8^4 6
  obtain ⟨k12, m12, t12, h12, hm12, _⟩ := rule_8 k11 m11 [2, 8, 8, 6]
  have h12b : iter H8 4 6 ≤ m12 := by
    rw [iter_succ]; exact Nat.le_trans (H8_mono (Nat.le_trans h10b hm11)) hm12
  obtain ⟨k13, m13, t13, h13, hm13⟩ := rule_2_ge k12 m12 [8, 8, 6]
  -- 6th `8`: ≥ H8^5 6
  obtain ⟨k14, m14, t14, h14, hm14, _⟩ := rule_8 k13 m13 [8, 6]
  have h14b : iter H8 5 6 ≤ m14 := by
    rw [iter_succ]; exact Nat.le_trans (H8_mono (Nat.le_trans h12b hm13)) hm14
  -- 7th `8`: ≥ H8^6 6 AND m15 ≤ t15
  obtain ⟨k15, m15, t15, h15, hm15, ht15⟩ := rule_8 k14 m14 [6]
  have h15b : iter H8 6 6 ≤ m15 := by
    rw [iter_succ]; exact Nat.le_trans (H8_mono h14b) hm15
  have hhalt : step bb69 (B5cfg k15 m15 [6]) =
               some (mkCfgR none (1 :: rep (k15 + 1) 2 (rep (2 * m15 + 1) 3 [5])) []) :=
    step_mkCfgR_R (tm := bb69) (q := 0) (w := 0) (cur := 6) rfl
  have hreach :=
    reaches_trans (reaches_trans (reaches_trans (reaches_trans
      (reaches_trans (reaches_trans (reaches_trans (reaches_trans
        (reaches_trans (reaches_trans (reaches_trans (reaches_trans
          (reaches_trans (reaches_trans (reaches_trans (reaches_trans
            hboot h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15)
      (steps_one bb69 _ _ hhalt)
  have hlt : f_omega_mul2_plus 3 6 < iter H8 6 6 :=
    iter_strict_dom H8 (f_omega_mul2_plus 2) 1 H8_gt (fOmegaMul_props 2 2) 6 6 (by omega) (by omega)
  have hlt_m15 : f_omega_mul2_plus 3 6 < m15 := Nat.lt_of_lt_of_le hlt h15b
  refine ⟨_, ⟨_, hreach, rfl⟩, ?_⟩
  exact Nat.lt_of_lt_of_le hlt_m15 (Nat.le_trans ht15 (by omega))

#print axioms bb69_halts_gt_f_omega_mul2_plus_3_6

end BB6_9
end BB
