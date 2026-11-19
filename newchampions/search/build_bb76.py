"""Verify and generate exact, axiom-free Lean 4 & Rocq 9.1 proofs for BB(7, 6) > f_{ω^2+1}(2)."""
from search.sim import parse_tm, run, fmt_cfg, mk_cfg
from search.gen_tm import gen_lean_tm, gen_rocq_tm

TM76 = '1LE3LB2LF2RA4LB2RA_4LF3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC1RZ3RD_5RB3RE1RZ4LC3LG5LE_5RB4RF1LF1LF2LF5RG_5LF5RG1LA1LG1RD5LG'

ns, ms, tab = parse_tm(TM76)
assert (ns, ms) == (7, 6)
t, tp, p, s = run(tab, {}, 0, 0, 112)
assert t == 112 and fmt_cfg(tp, p, s) == '533333332 A> 22', fmt_cfg(tp, p, s)
tp2, p2, s2 = mk_cfg('53332', '', 0)
th, tp3, p3, s3 = run(tab, tp2, p2, s2, 10)
assert th == 2 and s3 is None, (th, s3)
print("BB(7, 6) Python check PASSED! boot@112: 533333332 A> 22, halt in 2 steps.")

bb76_lean = f"""/-
  BB/BB7_6.lean
  Formal, axiom-free Lean 4 proof of a NEW Busy Beaver Champion for BB(7, 6):
    TM: {TM76}
    Domain: BB(7, 6) (7 states, 6 symbols)
    Previous wiki champion: BB(7, 6) > f_{{ω^2}}(110) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+1}}(2)
    (strictly beats f_{{ω^2}}(110) by a full FGH ordinal level, and strictly < our BB(7, 7) & BB(8, 6))
-/

import BB.TM
import BB.FGH
import BB.Kropitz
import BB.Fwp2
import BB.Fwp2_7

namespace BB
namespace BB7_6

{gen_lean_tm('bb76', TM76)}

theorem bb76_fp : Fwp2Core bb76 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem loop_F3 (n : Nat) (L R : List Nat) :
    Reaches bb76 (mkCfgR (some 5) (rep n 3 L) (3 :: R))
                 (mkCfgR (some 5) L (3 :: rep n 1 R)) n := by
  induction n generalizing R with
  | zero => exact reaches_zero bb76 _
  | succ k ih =>
    have h1 : step bb76 (mkCfgR (some 5) (3 :: rep k 3 L) (3 :: R)) =
              some (mkCfgR (some 5) (rep k 3 L) (3 :: 1 :: R)) :=
      step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 3) rfl
    have h2 := ih (1 :: R); rw [rep_snoc_one] at h2; exact steps_succ bb76 k _ _ _ h1 h2

private theorem loop_G1 (n : Nat) (L R : List Nat) :
    Reaches bb76 (mkCfgR (some 6) L (rep n 1 R))
                 (mkCfgR (some 6) (rep n 5 L) R) n := by
  induction n generalizing L with
  | zero => exact reaches_zero bb76 _
  | succ k ih =>
    have h1 : step bb76 (mkCfgR (some 6) L (1 :: rep k 1 R)) =
              some (mkCfgR (some 6) (5 :: L) (rep k 1 R)) :=
      step_mkCfgR_R (tm := bb76) (q := 6) (w := 4) (cur := 1) rfl
    have h2 := ih (5 :: L); rw [rep_snoc_one] at h2; exact steps_succ bb76 k _ _ _ h1 h2

private theorem rep_add (a b s : Nat) (L : List Nat) :
    rep a s (rep b s L) = rep (a + b) s L := by
  induction a with
  | zero => simp [rep]
  | succ p ih => rw [Nat.succ_add]; simp only [rep, ih]

theorem reload_2 (r m : Nat) (R : List Nat) :
    ∃ t, Reaches bb76 (Scfg (r + 1) 0 m (2 :: R))
                      (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) t := by
  have h1 : step bb76 (Scfg (r + 1) 0 m (2 :: R)) =
            some (mkCfgR (some 5) (rep (2 * m + 1) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 0) (w := 1) (cur := 2) rfl
  have h2 : step bb76 (mkCfgR (some 5) (3 :: rep (2 * m) 3 (rep (r + 1) 5 [])) (2 :: 2 :: R)) =
            some (mkCfgR (some 5) (rep (2 * m) 3 (rep (r + 1) 5 [])) (3 :: 1 :: 2 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 2) rfl
  have h3 := loop_F3 (2 * m) (rep (r + 1) 5 []) (1 :: 2 :: R)
  rw [rep_snoc_one] at h3
  have h4 : step bb76 (mkCfgR (some 5) (5 :: rep r 5 []) (3 :: rep (2 * m + 1) 1 (2 :: R))) =
            some (mkCfgR (some 5) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (2 :: R))) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 5) (w := 0) (cur := 3) rfl
  have h5 : step bb76 (mkCfgR (some 5) (rep r 5 []) (5 :: rep (2 * m + 2) 1 (2 :: R))) =
            some (mkCfgR (some 6) (rep (r + 1) 5 []) (rep (2 * m + 2) 1 (2 :: R))) :=
    step_mkCfgR_R (tm := bb76) (q := 5) (w := 4) (cur := 5) rfl
  have h6 := loop_G1 (2 * m + 2) (rep (r + 1) 5 []) (2 :: R)
  rw [rep_add] at h6
  have heq : (2 * m + 2) + (r + 1) = (r + 2 * m + 2) + 1 := by omega
  rw [heq] at h6
  have h7 : step bb76 (mkCfgR (some 6) (5 :: rep (r + 2 * m + 2) 5 []) (2 :: R)) =
            some (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (5 :: 1 :: R)) :=
    step_mkCfgR_L_cons (tm := bb76) (q := 6) (w := 0) (cur := 2) rfl
  have h8 : step bb76 (mkCfgR (some 0) (rep (r + 2 * m + 2) 5 []) (5 :: 1 :: R)) =
            some (mkCfgR (some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) :=
    step_mkCfgR_R (tm := bb76) (q := 0) (w := 1) (cur := 5) rfl
  exact ⟨_, reaches_trans
    (steps_succ bb76 _ _ _ _ h1 (steps_succ bb76 _ _ _ _ h2 h3))
    (steps_succ bb76 _ _ _ _ h4 (steps_succ bb76 _ _ _ _ h5 (reaches_trans h6
      (steps_succ bb76 _ _ _ _ h7 (steps_one bb76 _ _ h8)))))⟩

theorem rule_2 (r m : Nat) (R : List Nat) :
    ∃ r' m' t, Reaches bb76 (Scfg (r + 1) 0 m (2 :: R)) (Scfg (r' + 1) 0 m' R) t ∧
      H2_7 m ≤ m' ∧ m' ≤ t := by
  obtain ⟨t1, h1⟩ := reload_2 r m R
  obtain ⟨t2, h2, hle2⟩ := fwp2_empty3 bb76_fp (r + 2 * m + 1) R
  exact ⟨r + 2 * m + 1, Pempty (r + 2 * m + 1), t1 + t2, reaches_trans h1 h2,
    Pempty_mono (by omega), Nat.le_trans hle2 (Nat.le_add_left _ _)⟩

set_option maxRecDepth 2000 in
theorem bb76_bootstrap :
    Reaches bb76 initConfig (Scfg 1 0 3 [2, 2]) 112 := rfl

theorem bb76_halts_gt_f_omega2_plus_1_2 :
    ValidTM 7 6 bb76 ∧ ∃ t, HaltsIn bb76 initConfig t ∧ f_omega2_plus 1 2 < t := by
  refine ⟨bb76_valid, ?_⟩
  have hboot := bb76_bootstrap
  obtain ⟨r1, m1, t1, h1, hm1, _⟩ := rule_2 0 3 [2]
  obtain ⟨r2, m2, t2, h2, hm2, ht2⟩ := rule_2 r1 m1 []
  have hh1 : step bb76 (Scfg (r2 + 1) 0 m2 []) =
             some (mkCfgR (some 4) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 1]) := rfl
  have hh2 : step bb76 (mkCfgR (some 4) (rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [2, 1]) =
             some (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [1]) :=
    step_mkCfgR_R (tm := bb76) (q := 4) (w := 0) (cur := 2) rfl
  have hhalt : Reaches bb76 (Scfg (r2 + 1) 0 m2 [])
      (mkCfgR none (1 :: rep (2 * m2 + 1) 3 (rep (r2 + 1) 5 [])) [1]) 2 :=
    steps_succ bb76 1 _ _ _ hh1 (steps_one bb76 _ _ hh2)
  have hreach := reaches_trans (reaches_trans (reaches_trans hboot h1) h2) hhalt
  have hlt1 : f_omega2 2 < m1 :=
    Nat.lt_of_lt_of_le (H2_7_gt 2 (by omega)) (Nat.le_trans (H2_7_mono (by omega : 2 ≤ 3)) hm1)
  have hlt2 : f_omega2 (f_omega2 2) ≤ f_omega2 m1 :=
    (fOmega2_props 1 0 0).mono _ _ (Nat.le_of_lt hlt1)
  have hlt3 : f_omega2 m1 < m2 :=
    Nat.lt_of_lt_of_le (H2_7_gt m1 (by omega)) hm2
  have hdef : f_omega2_plus 1 2 = f_omega2 (f_omega2 2) := by
    change iter f_omega2 2 2 = f_omega2 (f_omega2 2)
    rw [iter_succ, iter_succ, iter_zero]
  have hlt_m2 : f_omega2_plus 1 2 < m2 := by rw [hdef]; exact Nat.lt_of_le_of_lt hlt2 hlt3
  refine ⟨_, ⟨_, hreach, rfl⟩, Nat.lt_of_lt_of_le hlt_m2 (Nat.le_trans ht2 (by omega))⟩

#print axioms bb76_halts_gt_f_omega2_plus_1_2

end BB7_6
end BB
"""

bb76_v = f"""(*
  rocq/BB7_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 6):
    TM: {TM76}
    Domain: BB(7, 6) (7 states, 6 symbols)
    Previous wiki champion: BB(7, 6) > f_{{ω^2}}(110) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{{ω^2+1}}(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

{gen_rocq_tm('bb76', TM76)}

Lemma bb76_fp : Fwp2Core bb76.
Proof. constructor; [constructor; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_F3 : forall n L R,
  Reaches bb76 (mkCfgR (Some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_G1 : forall n L R,
  Reaches bb76 (mkCfgR (Some 6) L (rep n 1 R))
               (mkCfgR (Some 6) (rep n 5 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 6 4 _ L 1 _ eq_refl) |].
  specialize (IH (5 :: L) R). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma rep_add : forall a b s L, rep a s (rep b s L) = rep (a + b) s L.
Proof. induction a as [| p IH]; intros b s L; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma reload_2 : forall r m R,
  exists t, Reaches bb76 (Scfg (S r) 0 m (2 :: R))
                         (mkCfgR (Some 0) (2 :: rep (r + 2 * m + 2) 5 []) (1 :: R)) t.
Proof.
  intros r m R. eexists. eapply reaches_trans.
  - unfold Scfg.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 1 2 2 _ _ R eq_refl) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    apply (loop_F3 (2 * m) (rep (S r) 5 []) (1 :: 2 :: R)).
  - rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 5 3 _ _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ _ 5 _ eq_refl) |].
    replace (1 :: 1 :: rep (2 * m) 1 (2 :: R)) with (rep (2 * m + 2) 1 (2 :: R))
      by (replace (2 * m + 2) with (S (S (2 * m))) by lia; reflexivity).
    eapply reaches_trans; [apply (loop_G1 (2 * m + 2) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_add.
    replace (2 * m + 2 + S r) with (S (r + 2 * m + 2)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 0 5 2 _ _ R eq_refl) |].
    apply steps_one. apply (step_mkCfgR_R _ 0 1 _ _ 5 (1 :: R) eq_refl).
Qed.

Lemma rule_2 : forall r m R,
  exists r' m' t, Reaches bb76 (Scfg (S r) 0 m (2 :: R)) (Scfg (S r') 0 m' R) t /\\
    H2_7 m <= m' /\\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_2 r m R) as [t1 H1].
  replace (r + 2 * m + 2) with (S (r + 2 * m + 1)) in H1 by lia.
  destruct (fwp2_empty3 bb76 bb76_fp (r + 2 * m + 1) R) as [t2 [H2 Hle2]].
  exists (r + 2 * m + 1), (Pempty (r + 2 * m + 1)), (t1 + t2).
  split; [eapply reaches_trans; eassumption | split; [unfold H2_7; apply Pempty_mono; lia | lia]].
Qed.

Lemma bb76_bootstrap :
  Reaches bb76 initConfig (Scfg 1 0 3 [2; 2]) 112.
Proof. vm_compute. reflexivity. Qed.

Theorem bb76_halts_gt_f_omega2_plus_1_2 :
  ValidTM 7 6 bb76 /\\ exists t, HaltsIn bb76 initConfig t /\\ f_omega2_plus 1 2 < t.
Proof.
  split; [exact bb76_valid |].
  pose proof bb76_bootstrap as Hboot.
  destruct (rule_2 0 3 [2]) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  destruct (rule_2 r1 m1 []) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  assert (Hh1 : step bb76 (Scfg (S r2) 0 m2 []) =
    Some (mkCfgR (Some 4) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 1])).
  {{ unfold Scfg, mkCfgR, step. simpl. reflexivity. }}
  assert (Hh2 : step bb76 (mkCfgR (Some 4) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 1]) =
    Some (mkCfgR None (1 :: rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [1])).
  {{ apply (step_mkCfgR_R _ 4 0 _ _ 2 [1] eq_refl). }}
  assert (Hhalt : Reaches bb76 (Scfg (S r2) 0 m2 [])
    (mkCfgR None (1 :: rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [1]) 2)
    by (eapply steps_succ; [exact Hh1 | apply steps_one; exact Hh2]).
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (H2_7_gt 2 ltac:(lia)) as Hlt1a.
  pose proof (H2_7_mono 2 3 ltac:(lia)) as Hlt1b.
  assert (Hlt1 : f_omega2 2 < m1) by lia.
  pose proof (fgh_mono _ (fOmega2_props 1 0 0) (f_omega2 2) m1 ltac:(lia)) as Hlt2.
  pose proof (H2_7_gt m1 ltac:(lia)) as Hlt3.
  assert (Hdef : f_omega2_plus 1 2 = f_omega2 (f_omega2 2)).
  {{ change (f_omega2_plus 1 2) with (iter f_omega2 2 2). rewrite iter_succ, iter_succ, iter_zero. reflexivity. }}
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (fOmega2 1 0 0) with f_omega2 in Hlt2. lia.
Qed.

Print Assumptions bb76_halts_gt_f_omega2_plus_1_2.
"""

with open('lean/BB/BB7_6.lean', 'w', encoding='utf-8') as f:
    f.write(bb76_lean)
with open('rocq/BB7_6.v', 'w', encoding='utf-8') as f:
    f.write(bb76_v)
print("Wrote lean/BB/BB7_6.lean and rocq/BB7_6.v")
