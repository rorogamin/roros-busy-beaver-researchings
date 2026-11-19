(*
  rocq/BB7_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 6):
    TM: 1LE3LB2LF2RA4LB2RA_4LF3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC1RZ3RD_5RB3RE1RZ4LC3LG5LE_5RB4RF1LF1LF2LF5RG_5LF5RG1LA1LG1RD5LG
    Domain: BB(7, 6) (7 states, 6 symbols)
    Previous wiki champion: BB(7, 6) > f_{ω^2}(110) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+1}(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

Definition bb76 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1LE 3LB 2LF 2RA 4LB 2RA *)
  | 0, 0 => Some (mkAction 1 DL (Some 4))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 5))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 2 DR (Some 0))
  (* State B (1): 4LF 3RB 1LD 2RA 3LF 5RB *)
  | 1, 0 => Some (mkAction 4 DL (Some 5))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  (* State D (3): 3RB 3RE 3LC 2RC 1RZ 3RD *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 1 DR None)
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  (* State E (4): 5RB 3RE 1RZ 4LC 3LG 5LE *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 1 DR None)
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  (* State F (5): 5RB 4RF 1LF 1LF 2LF 5RG *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 4 DR (Some 5))
  | 5, 2 => Some (mkAction 1 DL (Some 5))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 2 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DR (Some 6))
  (* State G (6): 5LF 5RG 1LA 1LG 1RD 5LG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 5 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 0))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 1 DR (Some 3))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | _, _ => None
  end.

Lemma bb76_valid : ValidTM 7 6 bb76.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 7 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 7 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists r' m' t, Reaches bb76 (Scfg (S r) 0 m (2 :: R)) (Scfg (S r') 0 m' R) t /\
    H2_7 m <= m' /\ m' <= t.
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
  ValidTM 7 6 bb76 /\ exists t, HaltsIn bb76 initConfig t /\ f_omega2_plus 1 2 < t.
Proof.
  split; [exact bb76_valid |].
  pose proof bb76_bootstrap as Hboot.
  destruct (rule_2 0 3 [2]) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  destruct (rule_2 r1 m1 []) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  assert (Hh1 : step bb76 (Scfg (S r2) 0 m2 []) =
    Some (mkCfgR (Some 4) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 1])).
  { unfold Scfg, mkCfgR, step. simpl. reflexivity. }
  assert (Hh2 : step bb76 (mkCfgR (Some 4) (rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [2; 1]) =
    Some (mkCfgR None (1 :: rep (2 * m2 + 1) 3 (rep (S r2) 5 [])) [1])).
  { apply (step_mkCfgR_R _ 4 0 _ _ 2 [1] eq_refl). }
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
  { change (f_omega2_plus 1 2) with (iter f_omega2 2 2). rewrite iter_succ, iter_succ, iter_zero. reflexivity. }
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (fOmega2 1 0 0) with f_omega2 in Hlt2. lia.
Qed.

Print Assumptions bb76_halts_gt_f_omega2_plus_1_2.
