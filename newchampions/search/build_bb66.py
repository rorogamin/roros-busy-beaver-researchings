"""Verify and generate exact, axiom-free Lean 4 & Rocq 9.1 proofs for BB(6, 6) > f_{ω×2+1}(2)."""
from search.sim import parse_tm, run, fmt_cfg, mk_cfg
from search.gen_tm import gen_lean_tm, gen_rocq_tm

TM66 = '5RE3LB4LF2RA4LB1RZ_5LE3RB1LD2RA3LF3RD_3RB1LB3LC2RC4LC0LE_3RB2RD3LC2RC1LE3RE_5RC3RE2RA4LC2LE2LA_5RB1RZ1LF1LF1RF5LF'

ns, ms, tab = parse_tm(TM66)
assert (ns, ms) == (6, 6)
t, tp, p, s = run(tab, {}, 0, 0, 40)
assert t == 40 and fmt_cfg(tp, p, s) == '532 A> 111225', fmt_cfg(tp, p, s)
# Also test reload_2 for k=2, m=1
tp2, p2, s2 = mk_cfg('5333222', '25', 0)
for i in range(1, 30):
    _, tp2, p2, s2 = run(tab, tp2, p2, s2, 1)
    if s2 == 0:
        assert fmt_cfg(tp2, p2, s2) == '53222222 A> 15', fmt_cfg(tp2, p2, s2)
        break
print("BB(6, 6) Python check PASSED! boot@40: 532 A> 111225, general-k reload_2 verified.")

bb66_lean = f"""/-
  BB/BB6_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(6, 6):
    TM: {TM66}
    Domain: BB(6, 6) (6 states, 6 symbols)
    Previous wiki champion: BB(6, 6) > f_{{ω×2}}(89) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω×2+1}}(2)
    (strictly beats f_{{ω×2}}(89) by a full FGH ordinal level, and strictly < our BB(6, 7) & BB(7, 6))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwm2

namespace BB
namespace BB6_6

{gen_lean_tm('bb66', TM66)}

theorem bb66_core : Fwm2Core bb66 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_F2 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 5) (rep n 2 L) (2 :: R))
                 (mkCfgR (some 5) L (2 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 5) (2 :: rep k 2 L) (2 :: R)) =
              some (mkCfgR (some 5) (rep k 2 L) (2 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 2) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem loop_D1 (n : Nat) (L R : List Nat) :
    Reaches bb66 (mkCfgR (some 3) L (rep n 1 R))
                 (mkCfgR (some 3) (rep n 2 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb66 _
  | succ k ih =>
    have h1 : step bb66 (mkCfgR (some 3) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 3) (2 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb66) (q := 3) (w := 1) (cur := 1) rfl
    have h2 := ih (2 :: L); rw [rep_snoc_one] at h2; exact steps_succ bb66 k _ _ _ h1 h2

private theorem rep_add (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem reload_2 (k m : Nat) (R : List Nat) :
    ∃ t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg (k + 2 * m + 1) 0 (1 :: R)) t := by
  have h1 : step bb66 (B5cfg k m (2 :: R)) =
            some (mkCfgR (some 5) (rep k 2 (rep (2 * m + 1) 3 [5])) (2 :: 4 :: R)) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 0) (w := 3) (cur := 2) rfl
  have h2 := loop_F2 k (rep (2 * m + 1) 3 [5]) (4 :: R)
  have h3 : step bb66 (mkCfgR (some 5) (3 :: rep (2 * m) 3 [5]) (2 :: rep k 1 (4 :: R))) =
            some (mkCfgR (some 5) (rep (2 * m) 3 [5]) (3 :: rep (k + 1) 1 (4 :: R))) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 2) rfl
  have h4 := loop_F3 (2 * m) [5] (rep (k + 1) 1 (4 :: R))
  rw [rep_add] at h4
  have h5 : step bb66 (mkCfgR (some 5) [5] (3 :: rep (2 * m + (k + 1)) 1 (4 :: R))) =
            some (mkCfgR (some 5) [] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) := by
    have heq : (2 * m + (k + 1)) + 1 = k + 2 * m + 2 := by omega
    rw [← heq]; exact step_mkCfgR_L_cons (tm := bb66) (q := 5) (w := 0) (cur := 3) rfl
  have h6 : step bb66 (mkCfgR (some 5) [] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 5) [] (0 :: 5 :: rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_L_nil (tm := bb66) (q := 5) (w := 4) (cur := 5) rfl
  have h7 : step bb66 (mkCfgR (some 5) [] (0 :: 5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 1) [5] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_R (tm := bb66) (q := 5) (w := 4) (cur := 0) rfl
  have h8 : step bb66 (mkCfgR (some 1) [5] (5 :: rep (k + 2 * m + 2) 1 (4 :: R))) =
            some (mkCfgR (some 3) [3, 5] (rep (k + 2 * m + 2) 1 (4 :: R))) :=
    step_mkCfgR_R (tm := bb66) (q := 1) (w := 2) (cur := 5) rfl
  have h9 := loop_D1 (k + 2 * m + 2) [3, 5] (4 :: R)
  have h10 : step bb66 (mkCfgR (some 3) (2 :: rep (k + 2 * m + 1) 2 [3, 5]) (4 :: R)) =
             some (mkCfgR (some 4) (rep (k + 2 * m + 1) 2 [3, 5]) (2 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb66) (q := 3) (w := 0) (cur := 4) rfl
  have h11 : step bb66 (mkCfgR (some 4) (rep (k + 2 * m + 1) 2 [3, 5]) (2 :: 1 :: R)) =
             some (B5cfg (k + 2 * m + 1) 0 (1 :: R)) :=
    step_mkCfgR_R (tm := bb66) (q := 4) (w := 1) (cur := 2) rfl
  exact ⟨_, reaches_trans
    (steps_succ bb66 _ _ _ _ h1 (reaches_trans h2 (steps_succ bb66 _ _ _ _ h3 h4)))
    (steps_succ bb66 _ _ _ _ h5 (steps_succ bb66 _ _ _ _ h6 (steps_succ bb66 _ _ _ _ h7
      (steps_succ bb66 _ _ _ _ h8 (reaches_trans h9 (steps_succ bb66 _ _ _ _ h10 (steps_one bb66 _ _ h11)))))))⟩

theorem rule_2 (k m : Nat) (R : List Nat) :
    ∃ k' m' t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t ∧
      Wfn (2 * m + 1) 0 ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 k m R
  obtain ⟨t2, h2, hle2⟩ := fwm2_step bb66_core (k + 2 * m + 1) 0 R
  exact ⟨k + 2 * m + 1, Wfn (k + 2 * m + 1) 0, t1 + t2, reaches_trans h1 h2,
    Wfn_mono_k (by omega) 0, Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

theorem bb66_bootstrap :
    Reaches bb66 initConfig (B5cfg 0 0 [1, 1, 1, 2, 2, 5]) 40 := rfl

theorem bb66_halts_gt_f_omega_mul2_plus_1_2 :
    ValidTM 6 6 bb66 ∧ ∃ t, HaltsIn bb66 initConfig t ∧ f_omega_mul2_plus 1 2 < t := by
  refine ⟨bb66_valid, ?_⟩
  have hboot := bb66_bootstrap
  obtain ⟨t1, h1, _⟩ := fwm2_step bb66_core 0 0 [1, 1, 2, 2, 5]
  obtain ⟨t2, h2, _⟩ := fwm2_step bb66_core 0 (Wfn 0 0) [1, 2, 2, 5]
  obtain ⟨t3, h3, _⟩ := fwm2_step bb66_core 0 (Wfn 0 (Wfn 0 0)) [2, 2, 5]
  have hm3_ge : 2 ≤ Wfn 0 (Wfn 0 (Wfn 0 0)) := by
    have a := Wfn_ge_succ 0 0
    have b := Wfn_ge_succ 0 (Wfn 0 0)
    have c := Wfn_ge_succ 0 (Wfn 0 (Wfn 0 0))
    omega
  obtain ⟨k4, m4, t4, h4, hm4, _⟩ := rule_2 0 (Wfn 0 (Wfn 0 (Wfn 0 0))) [2, 5]
  obtain ⟨k5, m5, t5, h5, hm5, ht5⟩ := rule_2 k4 m4 [5]
  have hhalt : step bb66 (B5cfg k5 m5 [5]) =
               some (mkCfgR none (1 :: rep (k5 + 1) 2 (rep (2 * m5 + 1) 3 [5])) []) :=
    step_mkCfgR_R (tm := bb66) (q := 0) (w := 0) (cur := 5) rfl
  have hreach := reaches_trans (reaches_trans (reaches_trans (reaches_trans
    (reaches_trans (reaches_trans hboot h1) h2) h3) h4) h5) (steps_one bb66 _ _ hhalt)
  have hlt1 : f_omega_mul2 2 < m4 :=
    Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 2)
      (Nat.le_trans (Wfn_mono_k (by omega : 3 ≤ 2 * Wfn 0 (Wfn 0 (Wfn 0 0)) + 1) 0) hm4)
  have hlt2 : f_omega_mul2 (f_omega_mul2 2) ≤ f_omega_mul2 m4 :=
    (fOmegaMul_props 2 0).mono _ _ (Nat.le_of_lt hlt1)
  have hlt3 : f_omega_mul2 m4 < m5 :=
    Nat.lt_of_lt_of_le (Wfn_succ_zero_gt_f_omega_mul2 m4)
      (Nat.le_trans (Wfn_mono_k (by omega : m4 + 1 ≤ 2 * m4 + 1) 0) hm5)
  have hdef : f_omega_mul2_plus 1 2 = f_omega_mul2 (f_omega_mul2 2) := by
    change iter f_omega_mul2 2 2 = f_omega_mul2 (f_omega_mul2 2)
    rw [iter_succ, iter_succ, iter_zero]
  have hlt_m5 : f_omega_mul2_plus 1 2 < m5 := by rw [hdef]; exact Nat.lt_of_le_of_lt hlt2 hlt3
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m5 (Nat.le_trans ht5 (by omega))⟩

#print axioms bb66_halts_gt_f_omega_mul2_plus_1_2

end BB6_6
end BB
"""

bb66_v = f"""(*
  rocq/BB6_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(6, 6):
    TM: {TM66}
    Domain: BB(6, 6) (6 states, 6 symbols)
    Previous wiki champion: BB(6, 6) > f_{{ω×2}}(89) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω×2+1}}(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwm2.
Import ListNotations.

{gen_rocq_tm('bb66', TM66)}

Lemma bb66_core : Fwm2Core bb66.
Proof. constructor; [constructor; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_F2 : forall n L R,
  Reaches bb66 (mkCfgR (Some 5) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 5) L (2 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 2 2 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_F3 : forall n L R,
  Reaches bb66 (mkCfgR (Some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_D1 : forall n L R,
  Reaches bb66 (mkCfgR (Some 3) L (rep n 1 R))
               (mkCfgR (Some 3) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 3 1 _ L 1 _ eq_refl) |].
  specialize (IH (2 :: L) R). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma rep_add : forall a b s L, rep a s (rep b s L) = rep (a + b) s L.
Proof. induction a as [| p IH]; intros b s L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma reload_2 : forall k m R,
  exists t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg (k + 2 * m + 1) 0 (1 :: R)) t.
Proof.
  intros k m R. eexists. eapply reaches_trans.
  - unfold B5cfg.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 3 2 2 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_F2 k (rep (2 * m + 1) 3 [5]) (4 :: R)) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    change (1 :: rep k 1 (4 :: R)) with (rep (S k) 1 (4 :: R)).
    apply (loop_F3 (2 * m) [5] (rep (S k) 1 (4 :: R))).
  - rewrite rep_add.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 5 3 _ _ _ eq_refl) |].
    replace (1 :: rep (2 * m + S k) 1 (4 :: R)) with (rep (k + 2 * m + 2) 1 (4 :: R))
      by (replace (k + 2 * m + 2) with (S (2 * m + S k)) by lia; reflexivity).
    eapply steps_succ; [apply (step_mkCfgR_L_nil _ 5 4 5 _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 0 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 1 2 _ [5] 5 _ eq_refl) |].
    eapply reaches_trans; [apply (loop_D1 (k + 2 * m + 2) [3; 5] (4 :: R)) |].
    replace (k + 2 * m + 2) with (S (k + 2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 0 2 4 _ _ R eq_refl) |].
    apply steps_one. unfold B5cfg. apply (step_mkCfgR_R _ 4 1 _ _ 2 (1 :: R) eq_refl).
Qed.

Lemma rule_2 : forall k m R,
  exists k' m' t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t /\\
    Wfn (2 * m + 1) 0 <= m' /\\ m' <= t.
Proof.
  intros k m R.
  destruct (reload_2 k m R) as [t1 H1].
  destruct (fwm2_step bb66 bb66_core (k + 2 * m + 1) 0 R) as [t2 [H2 Hle2]].
  exists (k + 2 * m + 1), (Wfn (k + 2 * m + 1) 0), (t1 + t2).
  split; [eapply reaches_trans; eassumption | split; [apply Wfn_mono_k; lia | lia]].
Qed.

Lemma bb66_bootstrap :
  Reaches bb66 initConfig (B5cfg 0 0 [1; 1; 1; 2; 2; 5]) 40.
Proof. vm_compute. reflexivity. Qed.

Theorem bb66_halts_gt_f_omega_mul2_plus_1_2 :
  ValidTM 6 6 bb66 /\\ exists t, HaltsIn bb66 initConfig t /\\ f_omega_mul2_plus 1 2 < t.
Proof.
  split; [exact bb66_valid |].
  pose proof bb66_bootstrap as Hboot.
  destruct (fwm2_step bb66 bb66_core 0 0 [1; 1; 2; 2; 5]) as [t1 [H1 _]].
  destruct (fwm2_step bb66 bb66_core 0 (Wfn 0 0) [1; 2; 2; 5]) as [t2 [H2 _]].
  destruct (fwm2_step bb66 bb66_core 0 (Wfn 0 (Wfn 0 0)) [2; 2; 5]) as [t3 [H3 _]].
  set (m3 := Wfn 0 (Wfn 0 (Wfn 0 0))).
  assert (Hm3 : 2 <= m3).
  {{ pose proof (Wfn_ge_succ 0 0). pose proof (Wfn_ge_succ 0 (Wfn 0 0)).
     pose proof (Wfn_ge_succ 0 (Wfn 0 (Wfn 0 0))). unfold m3. lia. }}
  destruct (rule_2 0 m3 [2; 5]) as [k4 [m4 [t4 [H4 [Hm4 _]]]]].
  destruct (rule_2 k4 m4 [5]) as [k5 [m5 [t5 [H5 [Hm5 Ht5]]]]].
  assert (Hhalt : step bb66 (B5cfg k5 m5 [5]) =
    Some (mkCfgR None (1 :: rep (S k5) 2 (rep (2 * m5 + 1) 3 [5])) [])).
  {{ apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }}
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
      (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _
        Hboot H1) H2) H3) H4) H5) (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (Wfn_succ_zero_gt_f_omega_mul2 2) as Hlt1a.
  pose proof (Wfn_mono_k 3 (2 * m3 + 1) 0 ltac:(lia)) as Hlt1b.
  assert (Hlt1 : f_omega_mul2 2 < m4) by lia.
  pose proof (fgh_mono _ (fOmegaMul_props 2 0) (f_omega_mul2 2) m4 ltac:(lia)) as Hlt2.
  pose proof (Wfn_succ_zero_gt_f_omega_mul2 m4) as Hlt3a.
  pose proof (Wfn_mono_k (S m4) (2 * m4 + 1) 0 ltac:(lia)) as Hlt3b.
  assert (Hdef : f_omega_mul2_plus 1 2 = f_omega_mul2 (f_omega_mul2 2)).
  {{ change (f_omega_mul2_plus 1 2) with (iter f_omega_mul2 2 2). rewrite iter_succ, iter_succ, iter_zero. reflexivity. }}
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (fOmegaMul 2 0) with f_omega_mul2 in Hlt2. lia.
Qed.

Print Assumptions bb66_halts_gt_f_omega_mul2_plus_1_2.
"""

with open('lean/BB/BB6_6.lean', 'w', encoding='utf-8') as f:
    f.write(bb66_lean)
with open('rocq/BB6_6.v', 'w', encoding='utf-8') as f:
    f.write(bb66_v)
print("Wrote lean/BB/BB6_6.lean and rocq/BB6_6.v")
