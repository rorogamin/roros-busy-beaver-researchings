/-
  BB/Fwp2_H.lean
  Shared 8-state `Fwp2_H` layer on top of `Fwp2Core`:
    - `sweep_HG`: common `H -> G` left-right sweep (`5^(r+1) 3^(2m+1) 2 -> 5^(r+1) 4^(2m+2) G> mark`)
    - `rule_2_H`, `rule_2_H_rep`: `f_{ω^2}` reload on symbol `2` (`H2_H m = Pempty (2*m + 2)`)
    - `bounce_G2_2s`, `rule_plus2_from_G2`: shared 23-step bounce + `H_plus2 m = iter H2_H (2*m - 1) 17 > f_{ω^2+1}(m)`
  Powers ALL `BB(8..11, 7..9)` and `BB(9..11, 6)` champions!
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2

namespace BB

/-- Shared 8-state `Fwp2_H` transitions (extending `Fwp2Core`). -/
structure Fwp2_HCore (tm : TM) : Prop where
  fp : Fwp2Core tm
  A2 : tm 0 2 = some ⟨2, Dir.L, some 7⟩
  E2 : tm 4 2 = some ⟨4, Dir.R, some 6⟩
  F4 : tm 5 4 = some ⟨5, Dir.L, some 5⟩
  F5 : tm 5 5 = some ⟨5, Dir.L, some 5⟩
  G1 : tm 6 1 = some ⟨4, Dir.R, some 6⟩
  G2 : tm 6 2 = some ⟨1, Dir.L, some 1⟩
  H2 : tm 7 2 = some ⟨1, Dir.L, some 7⟩
  H3 : tm 7 3 = some ⟨1, Dir.L, some 7⟩
  H5 : tm 7 5 = some ⟨5, Dir.R, some 6⟩

/-- Growth function `H2_H m = Pempty (2 * m + 2) > f_{ω^2}(m)`. -/
def H2_H (m : Nat) : Nat := Pempty (2 * m + 2)

/-- Growth function `H_plus2 m = iter H2_H (2 * m - 1) 17 > f_{ω^2+1}(m)` (for `m ≥ 1`). -/
def H_plus2 (m : Nat) : Nat := iter H2_H (2 * m - 1) 17

theorem H2_H_mono {x y : Nat} (hxy : x ≤ y) : H2_H x ≤ H2_H y := Pempty_mono (by omega)

theorem H2_H_0_ge : 17 ≤ H2_H 0 := by
  have hgen : ∀ r, Pfn (r + 1) 1 0 = Pfn (r + 1) 0 (Pfn (r + 1) 0 0) := fun _ => rfl
  have h1 : Pfn 1 1 0 = Pfn 1 0 (Pfn 1 0 0) := hgen 0
  have h2 : Pfn 1 0 0 + 1 ≤ Pfn 1 0 (Pfn 1 0 0) := Pfn_ge_succ 1 0 (Pfn 1 0 0)
  have h0 : Pfn 1 0 0 = 15 := rfl
  have hpe : ∀ r, Pempty r = Pfn r 1 0 + 1 := fun _ => rfl
  have h17 : 17 ≤ Pempty 1 := by rw [hpe, h1]; omega
  exact Nat.le_trans h17 (Pempty_mono (by omega : 1 ≤ 2 * 0 + 2))

theorem H2_H_inc (m : Nat) (_hm : 1 ≤ m) : m + 1 ≤ H2_H m := by
  have h := Pempty_ge (2 * m + 2); unfold H2_H; omega

theorem H2_H_gt (m : Nat) (_hm : 1 ≤ m) : f_omega2 m < H2_H m :=
  Nat.lt_of_lt_of_le (Pempty_gt_f_omega2 m) (Pempty_mono (by omega))

theorem H_plus2_mono {x y : Nat} (hxy : x ≤ y) : H_plus2 x ≤ H_plus2 y :=
  iter_mono_steps H2_H (fun z => by have := Pempty_ge (2 * z + 2); unfold H2_H; omega) (by omega) 17

theorem H_plus2_gt (m : Nat) (hm : 1 ≤ m) : f_omega2_plus 1 m < H_plus2 m := by
  cases m with
  | zero => cases hm
  | succ m' =>
    have hsplit : 2 * (m' + 1) - 1 = (m' + 1) + m' := by omega
    unfold H_plus2
    rw [hsplit, iter_add]
    have hbase : m' + 1 ≤ iter H2_H m' 17 := by
      have h := iter_ge_add_pos H2_H H2_H_inc m' 17 (by omega)
      omega
    have harg := iter_mono_arg H2_H (fun _ _ h => H2_H_mono h) (m' + 1) hbase
    have hlt : iter f_omega2 (m' + 1) (m' + 1) < iter H2_H (m' + 1) (m' + 1) :=
      iter_strict_dom H2_H f_omega2 1 H2_H_gt (fOmega2_props 1 0 0) (m' + 1) (m' + 1)
        (Nat.succ_pos m') (Nat.succ_pos m')
    exact Nat.lt_of_lt_of_le hlt harg

theorem H_plus2_inc (m : Nat) (hm : 1 ≤ m) : m + 1 ≤ H_plus2 m := by
  have h1 := H_plus2_gt m hm
  have h2 : m ≤ f_omega2_plus 1 m := (fOmega2_props 1 0 1).ge_self m
  omega

theorem H_plus2_ge_17 (m : Nat) : 17 ≤ H_plus2 m :=
  iter_ge_self H2_H (fun z => by have := Pempty_ge (2 * z + 2); unfold H2_H; omega) (2 * m - 1) 17

/-- Reusable `2*m - 1` level-climbing lemma starting from any `c ≥ 1` (including `c = 1`!). -/
theorem climb_2m_minus_1 (H f : Nat → Nat) (c : Nat) (hc : 1 ≤ c)
    (hmono : ∀ x y, x ≤ y → H x ≤ H y)
    (hinc : ∀ x, 1 ≤ x → x + 1 ≤ H x)
    (hdom : ∀ x, 1 ≤ x → f x < H x)
    (hf : FGHProps f) :
    ∀ m, 1 ≤ m → fNext f m < iter H (2 * m - 1) c := by
  intro m hm
  cases m with
  | zero => cases hm
  | succ m' =>
    have hsplit : 2 * (m' + 1) - 1 = (m' + 1) + m' := by omega
    rw [hsplit, iter_add]
    have hbase : m' + 1 ≤ iter H m' c := by
      have h := iter_ge_add_pos H hinc m' c hc; omega
    have harg := iter_mono_arg H hmono (m' + 1) hbase
    have hlt := iter_strict_dom H f 1 hdom hf (m' + 1) (m' + 1) (Nat.succ_pos m') (Nat.succ_pos m')
    exact Nat.lt_of_lt_of_le hlt harg

private theorem rep_add_H (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

section Fwp2_HLemmas

variable {tm : TM} (hh : Fwp2_HCore tm)
include hh

theorem loop_H3 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 7) (rep n 3 L) (3 :: R))
               (mkCfgR (some 7) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 7) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 7) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons hh.H3
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem loop_G1 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 6) L (rep n 1 R))
               (mkCfgR (some 6) (rep n 4 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 6) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 6) (4 :: L) (rep k 1 R)) :=
      step_mkCfgR_R hh.G1
    have h2 := ih (4 :: L); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem loop_F4 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 5) (rep n 4 L) (4 :: R))
               (mkCfgR (some 5) L (4 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 5) (4 :: rep k 4 L) (4 :: R)) =
              some (mkCfgR (some 5) (rep k 4 L) (4 :: 5 :: R)) :=
      step_mkCfgR_L_cons hh.F4
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem loop_F5 (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 5) (rep n 5 L) (5 :: R))
               (mkCfgR (some 5) L (5 :: rep n 5 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 5) (5 :: rep k 5 L) (5 :: R)) =
              some (mkCfgR (some 5) (rep k 5 L) (5 :: 5 :: R)) :=
      step_mkCfgR_L_cons hh.F5
    have h2 := ih (5 :: R); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

theorem loop_B5_H (n : Nat) (L R : List Nat) :
    Reaches tm (mkCfgR (some 1) L (rep n 5 R))
               (mkCfgR (some 1) (rep n 5 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero tm _
  | succ k ih =>
    have h1 : step tm (mkCfgR (some 1) L (5 :: rep k 5 R)) =
              some (mkCfgR (some 1) (5 :: L) (rep k 5 R)) :=
      step_mkCfgR_R hh.fp.B5
    have h2 := ih (5 :: L); rw [rep_snoc_one] at h2; exact steps_succ tm k _ _ _ h1 h2

/-- Common `H -> G` sweep:
    `5^(r+1) 3^(2m+1) H> 2 mark R  -->  5^(r+1) 4^(2m+2) G> mark R`. -/
theorem sweep_HG (r m mark : Nat) (R : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: mark :: R))
                    (mkCfgR (some 6) (rep (2 * m + 2) 4 (rep (r + 1) 5 [])) (mark :: R)) t := by
  have h1 : step tm (mkCfgR (some 7) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: mark :: R)) =
            some (mkCfgR (some 7) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 1 :: mark :: R)) :=
    step_mkCfgR_L_cons hh.H2
  have h2 := loop_H3 hh (2 * m) (rep (r + 1) 5 []) (1 :: mark :: R)
  rw [rep_snoc_one] at h2
  have h3 : step tm (mkCfgR (some 7) (5 :: rep r 5 []) (3 :: rep (2 * m + 1) 1 (mark :: R))) =
            some (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (mark :: R))) :=
    step_mkCfgR_L_cons hh.H3
  have h4 : step tm (mkCfgR (some 7) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (mark :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 2) 1 (mark :: R))) :=
    step_mkCfgR_R hh.H5
  have h5 := loop_G1 hh (2 * m + 2) (rep (r + 1) 5 []) (mark :: R)
  exact ⟨_, steps_succ tm _ _ _ _ h1 (reaches_trans h2
    (steps_succ tm _ _ _ _ h3 (steps_succ tm _ _ _ _ h4 h5)))⟩

/-- Reload on symbol `2`: `Scfg (r+1) 0 m (2 :: R) --> 5^(r + 2m + 3) 2 A> 1 R`. -/
theorem reload_2_H (r m : Nat) (R : List Nat) :
    ∃ t, Reaches tm (Scfg (r + 1) 0 m (2 :: R))
                    (mkCfgR (some 0) (2 :: rep (r + 2 * m + 3) 5 []) (1 :: R)) t := by
  have h1 : step tm (Scfg (r + 1) 0 m (2 :: R)) =
            some (mkCfgR (some 7) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons hh.A2
  obtain ⟨ts, hs⟩ := sweep_HG hh r m 2 R
  have h2 : step tm (mkCfgR (some 6) (4 :: rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (2 :: R)) =
            some (mkCfgR (some 1) (rep (2 * m + 1) 4 (rep (r + 1) 5 [])) (4 :: 1 :: R)) :=
    step_mkCfgR_L_cons hh.G2
  have h3 : step tm (mkCfgR (some 1) (4 :: rep (2 * m) 4 (rep (r + 1) 5 [])) (4 :: 1 :: R)) =
            some (mkCfgR (some 5) (rep (2 * m) 4 (rep (r + 1) 5 [])) (4 :: 3 :: 1 :: R)) :=
    step_mkCfgR_L_cons hh.fp.B4
  have h4 := loop_F4 hh (2 * m) (rep (r + 1) 5 []) (3 :: 1 :: R)
  have h5 : step tm (mkCfgR (some 5) (5 :: rep r 5 []) (4 :: rep (2 * m) 5 (3 :: 1 :: R))) =
            some (mkCfgR (some 5) (rep r 5 []) (5 :: rep (2 * m + 1) 5 (3 :: 1 :: R))) :=
    step_mkCfgR_L_cons hh.F4
  have h6 := loop_F5 hh r [] (rep (2 * m + 1) 5 (3 :: 1 :: R))
  rw [rep_add_H] at h6
  have h7 : step tm (mkCfgR (some 5) [] (5 :: rep (r + (2 * m + 1)) 5 (3 :: 1 :: R))) =
            some (mkCfgR (some 5) [] (0 :: rep (r + 2 * m + 2) 5 (3 :: 1 :: R))) := by
    have ha : (r + (2 * m + 1)) + 1 = r + 2 * m + 2 := by omega
    rw [← ha]; exact step_mkCfgR_L_nil hh.F5
  have h8 : step tm (mkCfgR (some 5) [] (0 :: rep (r + 2 * m + 2) 5 (3 :: 1 :: R))) =
            some (mkCfgR (some 1) [5] (rep (r + 2 * m + 2) 5 (3 :: 1 :: R))) :=
    step_mkCfgR_R hh.fp.F0
  have h9 := loop_B5_H hh (r + 2 * m + 2) [5] (3 :: 1 :: R)
  have hrep5 : rep (r + 2 * m + 2) 5 [5] = rep (r + 2 * m + 3) 5 [] := by rw [rep_snoc_one]; rfl
  rw [hrep5] at h9
  have h10 : step tm (mkCfgR (some 1) (rep (r + 2 * m + 3) 5 []) (3 :: 1 :: R)) =
             some (mkCfgR (some 0) (2 :: rep (r + 2 * m + 3) 5 []) (1 :: R)) :=
    step_mkCfgR_R hh.fp.kc.B3
  have ha := steps_succ tm _ _ _ _ h1 (reaches_trans hs
    (steps_succ tm _ _ _ _ h2 (steps_succ tm _ _ _ _ h3 h4)))
  have hb := steps_succ tm _ _ _ _ h5 (reaches_trans h6
    (steps_succ tm _ _ _ _ h7 (steps_succ tm _ _ _ _ h8 (reaches_trans h9 (steps_one tm _ _ h10)))))
  exact ⟨_, reaches_trans ha hb⟩

theorem rule_2_H (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (2 :: R)) (Scfg (r' + 2) 0 m' R) t ∧
      H2_H m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2_H hh r m R
  obtain ⟨t2, h2, hle2⟩ := fwp2_empty3 hh.fp (r + 2 * m + 2) R
  exact ⟨r + 2 * m + 1, Pempty (r + 2 * m + 2), t1 + t2, reaches_trans h1 h2,
    Pempty_mono (by omega), Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem rule_2_H_rep (n : Nat) :
    ∀ r m R, ∃ r' m' t, Reaches tm (Scfg (r + 1) 0 m (rep n 2 R)) (Scfg (r' + 1) 0 m' R) t ∧
      iter H2_H n m ≤ m' ∧ (1 ≤ n → m' ≤ t ∧ 1 ≤ r') := by
  induction n with
  | zero => intro r m R; exact ⟨r, m, 0, reaches_zero tm _, Nat.le_refl m, fun h => by cases h⟩
  | succ p ih =>
    intro r m R
    cases p with
    | zero =>
      obtain ⟨r1, m1, t1, h1, hm1, ht1⟩ := rule_2_H hh r m R
      exact ⟨r1 + 1, m1, t1, h1, hm1, fun _ => ⟨ht1, by omega⟩⟩
    | succ p' =>
      obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2_H hh r m (rep (p' + 1) 2 R)
      obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := ih (r1 + 1) m1 R
      have hcomm : iter H2_H (p' + 1) (H2_H m) = iter H2_H (p' + 2) m := (iter_add H2_H (p' + 1) 1 m).symm
      have hmb : iter H2_H (p' + 2) m ≤ m2 := by
        rw [← hcomm]; exact Nat.le_trans (iter_mono_arg H2_H (fun _ _ h => H2_H_mono h) (p' + 1) hm1) hm2
      exact ⟨r2, m2, t1 + t2, reaches_trans h1 h2, hmb, fun _ =>
        ⟨Nat.le_trans (ht2 (Nat.succ_pos p')).1 (Nat.le_add_left _ _), (ht2 (Nat.succ_pos p')).2⟩⟩

/-- Shared 23-step bounce:
    `5^(r+1) G> 2 2 2 2 R'  -->  Scfg (r+1) 0 1 (1 :: R')`. -/
theorem bounce_G2_2s (r : Nat) (R' : List Nat) :
    ∃ t, Reaches tm (mkCfgR (some 6) (rep (r + 1) 5 []) (2 :: 2 :: 2 :: 2 :: R'))
                    (Scfg (r + 1) 0 1 (1 :: R')) t := by
  have h0 : Reaches tm
      (mkCfgR (some 6) (5 :: rep r 5 []) (2 :: 2 :: 2 :: 2 :: R'))
      (mkCfgR (some 5) (rep r 5 []) (3 :: 1 :: 1 :: 3 :: 1 :: R')) 15 := by
    refine steps_succ tm 14 _ _ _ (step_mkCfgR_L_cons hh.G2) ?_
    refine steps_succ tm 13 _ _ _ (step_mkCfgR_R hh.fp.B5) ?_
    refine steps_succ tm 12 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
    refine steps_succ tm 11 _ _ _ (step_mkCfgR_L_cons hh.fp.kc.B2) ?_
    refine steps_succ tm 10 _ _ _ (step_mkCfgR_R hh.fp.kc.D3) ?_
    refine steps_succ tm 9 _ _ _ (step_mkCfgR_L_cons hh.fp.kc.C1) ?_
    refine steps_succ tm 8 _ _ _ (step_mkCfgR_L_cons hh.fp.kc.B2) ?_
    refine steps_succ tm 7 _ _ _ (step_mkCfgR_R hh.fp.D5) ?_
    refine steps_succ tm 6 _ _ _ (step_mkCfgR_R hh.fp.D1) ?_
    refine steps_succ tm 5 _ _ _ (step_mkCfgR_R hh.fp.E1) ?_
    refine steps_succ tm 4 _ _ _ (step_mkCfgR_R hh.E2) ?_
    refine steps_succ tm 3 _ _ _ (step_mkCfgR_L_cons hh.G2) ?_
    refine steps_succ tm 2 _ _ _ (step_mkCfgR_L_cons hh.fp.B4) ?_
    refine steps_succ tm 1 _ _ _ (step_mkCfgR_L_cons hh.fp.F3) ?_
    exact steps_one tm _ _ (step_mkCfgR_L_cons hh.fp.F3)
  have htail : ∃ tt, Reaches tm
      (mkCfgR (some 5) (rep r 5 []) (3 :: 1 :: 1 :: 3 :: 1 :: R'))
      (Scfg (r + 1) 0 1 (1 :: R')) tt := by
    cases r with
    | zero =>
      refine ⟨6, ?_⟩
      refine steps_succ tm 5 _ _ _ (step_mkCfgR_L_nil hh.fp.F3) ?_
      refine steps_succ tm 4 _ _ _ (step_mkCfgR_R hh.fp.F0) ?_
      refine steps_succ tm 3 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
      refine steps_succ tm 2 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
      refine steps_succ tm 1 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
      exact steps_one tm _ _ (step_mkCfgR_R hh.fp.kc.B3)
    | succ r' =>
      have ha : step tm (mkCfgR (some 5) (5 :: rep r' 5 []) (3 :: 1 :: 1 :: 3 :: 1 :: R')) =
                some (mkCfgR (some 5) (rep r' 5 []) (5 :: 1 :: 1 :: 1 :: 3 :: 1 :: R')) :=
        step_mkCfgR_L_cons hh.fp.F3
      have hb := loop_F5 hh r' [] (1 :: 1 :: 1 :: 3 :: 1 :: R')
      have hc : step tm (mkCfgR (some 5) [] (5 :: rep r' 5 (1 :: 1 :: 1 :: 3 :: 1 :: R'))) =
                some (mkCfgR (some 5) [] (0 :: rep (r' + 1) 5 (1 :: 1 :: 1 :: 3 :: 1 :: R'))) :=
        step_mkCfgR_L_nil hh.F5
      have hd : step tm (mkCfgR (some 5) [] (0 :: rep (r' + 1) 5 (1 :: 1 :: 1 :: 3 :: 1 :: R'))) =
                some (mkCfgR (some 1) [5] (rep (r' + 1) 5 (1 :: 1 :: 1 :: 3 :: 1 :: R'))) :=
        step_mkCfgR_R hh.fp.F0
      have he := loop_B5_H hh (r' + 1) [5] (1 :: 1 :: 1 :: 3 :: 1 :: R')
      have hrep5 : rep (r' + 1) 5 [5] = rep (r' + 2) 5 [] := by rw [rep_snoc_one]; rfl
      rw [hrep5] at he
      have hf1 : Reaches tm (mkCfgR (some 1) (rep (r' + 2) 5 []) (1 :: 1 :: 1 :: 3 :: 1 :: R'))
                            (Scfg (r' + 2) 0 1 (1 :: R')) 4 := by
        refine steps_succ tm 3 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
        refine steps_succ tm 2 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
        refine steps_succ tm 1 _ _ _ (step_mkCfgR_R hh.fp.kc.B1) ?_
        exact steps_one tm _ _ (step_mkCfgR_R hh.fp.kc.B3)
      exact ⟨_, steps_succ tm _ _ _ _ ha (reaches_trans hb
        (steps_succ tm _ _ _ _ hc (steps_succ tm _ _ _ _ hd (reaches_trans he hf1))))⟩
  obtain ⟨tt, ht⟩ := htail
  exact ⟨15 + tt, reaches_trans h0 ht⟩

/-- Execute `5^(r+1) G> 2^(2m+3) R` (`m ≥ 1`) all the way to `Scfg (r'+1) 0 m' R`
    with `H_plus2 m ≤ m' ∧ m' ≤ t`. -/
theorem exec_G2_2s (r m : Nat) (hm : 1 ≤ m) (R : List Nat) :
    ∃ r' m' t, Reaches tm (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 3) 2 R))
                          (Scfg (r' + 2) 0 m' R) t ∧ H_plus2 m ≤ m' ∧ m' ≤ t := by
  cases m with
  | zero => cases hm
  | succ m' =>
    have h4 : 2 * (m' + 1) + 3 = (2 * m' + 1) + 4 := by omega
    have hsplit : rep (2 * (m' + 1) + 3) 2 R = 2 :: 2 :: 2 :: 2 :: rep (2 * m' + 1) 2 R := by
      have ha : 2 * (m' + 1) + 3 = 2 * m' + 1 + 4 := by omega
      rw [ha]; rfl
    rw [hsplit]
    obtain ⟨t0, h0⟩ := bounce_G2_2s hh r (rep (2 * m' + 1) 2 R)
    obtain ⟨t1, h1, _⟩ := fwp2_step hh.fp (r + 1) 0 1 (rep (2 * m' + 1) 2 R)
    have hM_17 : 17 ≤ Pfn (r + 1) 0 1 := by
      have hle2 : Pfn 1 0 1 ≤ Pfn (r + 1) 0 1 := Pfn_mono_r (by omega : 1 ≤ r + 1) 0 1
      have hp_gen : ∀ m, Pfn 1 0 m = PexitOf Kfn (2 * m + 2) 0 := fun _ => rfl
      have hpe_gen : ∀ j M, PexitOf Kfn (j + 1) M = PexitOf Kfn j (Kfn (j + 1) M) := fun _ _ => rfl
      have hstep : Kfn 4 0 + 1 ≤ Pfn 1 0 1 := by
        have hg : ∀ j M, M + 1 ≤ PexitOf Kfn j M := by
          intro j; induction j with
          | zero => intro M; exact Nat.le_refl _
          | succ p ihp => intro M; have a := ihp (Kfn (p + 1) M); have b := Kfn_ge_succ (p + 1) M; rw [hpe_gen]; omega
        rw [hp_gen]
        have h4eq : 2 * 1 + 2 = 4 := rfl
        rw [h4eq, hpe_gen 3 0]
        exact hg 3 (Kfn 4 0)
      have hk_gen : ∀ j m, Kfn (j + 1) m = iter (Kfn j) (2 * m + 2) 0 := fun _ _ => rfl
      have hk_z : ∀ j, Kfn (j + 1) 0 = Kfn j (Kfn j 0) := fun _ => rfl
      have hK20 : Kfn 2 0 = 6 := rfl
      have hK1 : ∀ n, 2 * n ≤ iter (Kfn 1) n 0 := by
        intro n; induction n with
        | zero => exact Nat.le_refl 0
        | succ p ihp =>
          rw [iter_succ]
          have hg : ∀ z, 2 * z + 2 ≤ Kfn 1 z := by
            intro z; rw [hk_gen 0 z]
            have hg0 : ∀ q, q ≤ iter (Kfn 0) q 0 := by
              intro q; induction q with
              | zero => exact Nat.le_refl 0
              | succ u ihu => rw [iter_succ]; change u + 1 ≤ iter (Kfn 0) u 0 + 1; omega
            exact hg0 (2 * z + 2)
          have := hg (iter (Kfn 1) p 0); omega
      have hK3 : 28 ≤ Kfn 3 0 := by
        rw [hk_z 2, hK20, hk_gen 1 6]
        have h14eq : 2 * 6 + 2 = 14 := rfl
        rw [h14eq]; exact hK1 14
      have hstep34 : Kfn 3 0 ≤ Kfn 4 0 := Kfn_step_k 3 0
      omega
    obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2_H_rep hh (2 * m' + 1) r (Pfn (r + 1) 0 1) R
    have h2m : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
    have harg : H_plus2 (m' + 1) ≤ iter H2_H (2 * m' + 1) (Pfn (r + 1) 0 1) := by
      unfold H_plus2; rw [h2m]
      exact iter_mono_arg H2_H (fun _ _ h => H2_H_mono h) (2 * m' + 1) hM_17
    obtain ⟨ht2_le, hr2_pos⟩ := ht2 (by omega)
    cases r2 with
    | zero => omega
    | succ r2' =>
      exact ⟨r2', m2, (t0 + t1) + t2, reaches_trans (reaches_trans h0 h1) h2,
        Nat.le_trans harg hm2, Nat.le_trans ht2_le (Nat.le_add_left _ _)⟩

end Fwp2_HLemmas
end BB
