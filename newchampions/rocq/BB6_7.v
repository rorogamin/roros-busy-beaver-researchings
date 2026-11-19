(*
  rocq/BB6_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(6, 7):
    TM: 6RD3LB6LF2RA4LB1RZ6LA_6LC3RB1LD2RA3LF4RE6LB_3RB1LB3LC2RC4LC0LE5LA_3RB2RD3LC2RC1LA3RE1LE_5RC3RE2RA4LC2LE2LE5RB_5RB3RD1LF1LF6LE5RF5LB
    Domain: BB(6, 7) (6 states, 7 symbols)
    Previous best dominated bounds: BB(5, 7) > f_{ω×2}(97), BB(6, 6) > f_{ω×2}(89)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+1}(6)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwm2.
Import ListNotations.

Definition bb67 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6RD 3LB 6LF 2RA 4LB 1RZ 6LA *)
  | 0, 0 => Some (mkAction 6 DR (Some 3))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 6 DL (Some 5))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 1 DR None)
  | 0, 6 => Some (mkAction 6 DL (Some 0))
  (* State B (1): 6LC 3RB 1LD 2RA 3LF 4RE 6LB *)
  | 1, 0 => Some (mkAction 6 DL (Some 2))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 4 DR (Some 4))
  | 1, 6 => Some (mkAction 6 DL (Some 1))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 0LE 5LA *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 0 DL (Some 4))
  | 2, 6 => Some (mkAction 5 DL (Some 0))
  (* State D (3): 3RB 2RD 3LC 2RC 1LA 3RE 1LE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 2 DR (Some 3))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 1 DL (Some 0))
  | 3, 5 => Some (mkAction 3 DR (Some 4))
  | 3, 6 => Some (mkAction 1 DL (Some 4))
  (* State E (4): 5RC 3RE 2RA 4LC 2LE 2LE 5RB *)
  | 4, 0 => Some (mkAction 5 DR (Some 2))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 0))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 2 DL (Some 4))
  | 4, 5 => Some (mkAction 2 DL (Some 4))
  | 4, 6 => Some (mkAction 5 DR (Some 1))
  (* State F (5): 5RB 3RD 1LF 1LF 6LE 5RF 5LB *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 3 DR (Some 3))
  | 5, 2 => Some (mkAction 1 DL (Some 5))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 6 DL (Some 4))
  | 5, 5 => Some (mkAction 5 DR (Some 5))
  | 5, 6 => Some (mkAction 5 DL (Some 1))
  | _, _ => None
  end.

Lemma bb67_valid : ValidTM 6 7 bb67.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 6 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 6 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb67_fwm2 : Fwm2Core bb67.
Proof.
  constructor; [constructor; reflexivity | ..]; reflexivity.
Qed.

Local Lemma loop_F2 : forall n L R,
  Reaches bb67 (mkCfgR (Some 5) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 5) L (2 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 2 2 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_F3 : forall n L R,
  Reaches bb67 (mkCfgR (Some 5) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 5) L (3 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 3 _ _ R eq_refl) |].
  specialize (IH L (1 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Local Lemma loop_D1 : forall n L R,
  Reaches bb67 (mkCfgR (Some 3) L (rep n 1 R))
               (mkCfgR (Some 3) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_R _ 3 1 _ L 1 _ eq_refl) |].
  specialize (IH (2 :: L) R). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rep_app_1 : forall a b R, rep a 1 (rep b 1 R) = rep (a + b) 1 R.
Proof.
  induction a as [| k IH]; intros b R; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma reload_2 : forall k m R,
  exists t, Reaches bb67 (B5cfg k m (2 :: R)) (B5cfg (2 * m + k) 0 (1 :: R)) t.
Proof.
  intros k m R.
  eexists. eapply reaches_trans.
  - eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 2 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_F2 k (rep (2 * m + 1) 3 [5]) (6 :: R)) |].
    replace (2 * m + 1) with (S (2 * m)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 3 2 _ _ _ eq_refl) |].
    change (1 :: rep k 1 (6 :: R)) with (rep (S k) 1 (6 :: R)).
    apply (loop_F3 (2 * m) [5] (rep (S k) 1 (6 :: R))).
  - rewrite rep_app_1.
    replace (2 * m + S k) with (2 * m + k + 1) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 5 0 5 3 _ [] _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 4 _ [] 5 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R _ 5 2 _ [5] 1 _ eq_refl) |].
    eapply reaches_trans; [apply (loop_D1 (2 * m + k + 1) [3; 5] (6 :: R)) |].
    replace (2 * m + k + 1) with (S (2 * m + k)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 3 0 2 6 _ _ R eq_refl) |].
    apply steps_one. unfold B5cfg.
    apply (step_mkCfgR_R _ 4 1 _ _ 2 (1 :: R) eq_refl).
Qed.

Definition H2 (m : nat) : nat := Wfn (2 * m) 0.

Lemma rule_2 : forall k m R,
  exists k' m' t, Reaches bb67 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t /\ H2 m <= m' /\ m' <= t.
Proof.
  intros k m R.
  destruct (reload_2 k m R) as [t1 H1].
  destruct (fwm2_step bb67 bb67_fwm2 (2 * m + k) 0 R) as [t2 [H2s Hle2]].
  exists (2 * m + k), (Wfn (2 * m + k) 0), (t1 + t2).
  split; [| split].
  - eapply reaches_trans; eassumption.
  - unfold H2. apply Wfn_mono_k; lia.
  - lia.
Qed.

Lemma H2_mono : forall x y, x <= y -> H2 x <= H2 y.
Proof. intros x y Hxy. unfold H2. apply Wfn_mono_k; lia. Qed.

Lemma H2_gt_f_omega_mul2 : forall m, 1 <= m -> f_omega_mul2 m < H2 m.
Proof.
  intros m Hm. unfold H2.
  pose proof (Wfn_succ_zero_gt_f_omega_mul2 m).
  pose proof (Wfn_mono_k (S m) (2 * m) 0 ltac:(lia)). lia.
Qed.

Lemma rule_2_rep : forall n k m R,
  exists k' m' t, Reaches bb67 (B5cfg k m (rep n 2 R)) (B5cfg k' m' R) t /\
    iter H2 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros k m R.
  - exists k, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_2 k m R) as [k1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists k1, m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_2 k m (rep (S p') 2 R)) as [k1 [m1 [t1 [H1 [Hm1 _]]]]].
      destruct (IH k1 m1 R) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists k2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H2 (S (S p')) m) with (iter H2 (S p') (H2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H2_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb67_bootstrap :
  Reaches bb67 initConfig (B5cfg 0 0 [2; 2; 2; 2; 2; 2; 2; 5]) 46.
Proof. vm_compute. reflexivity. Qed.

Theorem bb67_halts_gt_f_omega_mul2_plus_1_6 :
  ValidTM 6 7 bb67 /\ exists t, HaltsIn bb67 initConfig t /\ f_omega_mul2_plus 1 6 < t.
Proof.
  split; [exact bb67_valid |].
  pose proof bb67_bootstrap as Hboot.
  destruct (rule_2 0 0 [2; 2; 2; 2; 2; 2; 5]) as [k1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_ge : 6 <= m1).
  { assert (H15 : H2 0 = 15) by reflexivity. lia. }
  destruct (rule_2_rep 6 k1 m1 [5]) as [k2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  assert (Hhalt : step bb67 (B5cfg k2 m2 [5]) =
    Some (mkCfgR None (1 :: rep (S k2) 2 (rep (2 * m2 + 1) 3 [5])) [])).
  { apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r)
    (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H2 f_omega_mul2 1 H2_gt_f_omega_mul2
    (fOmegaMul_props 2 0) 6 6 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H2 H2_mono 6 6 m1 Hm1_ge) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  exists (((46 + t1) + t2) + 1). split.
  - eexists; split; [exact Hreach | reflexivity].
  - change (f_omega_mul2_plus 1 6) with (iter f_omega_mul2 6 6). lia.
Qed.

Print Assumptions bb67_halts_gt_f_omega_mul2_plus_1_6.
