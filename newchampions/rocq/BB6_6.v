(*
  rocq/BB6_6.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(6, 6):
    TM: 5RE3LB4LF2RA4LB1RZ_5LE3RB1LD2RA3LF3RD_3RB1LB3LC2RC4LC0LE_3RB2RD3LC2RC1LE3RE_5RC3RE2RA4LC2LE2LA_5RB1RZ1LF1LF1RF5LF
    Domain: BB(6, 6) (6 states, 6 symbols)
    Previous wiki champion: BB(6, 6) > f_{ω×2}(89) (User:Loader3229, Nov 2026)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2+1}(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwm2.
Import ListNotations.

Definition bb66 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 5RE 3LB 4LF 2RA 4LB 1RZ *)
  | 0, 0 => Some (mkAction 5 DR (Some 4))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 4 DL (Some 5))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 1 DR None)
  (* State B (1): 5LE 3RB 1LD 2RA 3LF 3RD *)
  | 1, 0 => Some (mkAction 5 DL (Some 4))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 3 DR (Some 3))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 0LE *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 0 DL (Some 4))
  (* State D (3): 3RB 2RD 3LC 2RC 1LE 3RE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 2 DR (Some 3))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 1 DL (Some 4))
  | 3, 5 => Some (mkAction 3 DR (Some 4))
  (* State E (4): 5RC 3RE 2RA 4LC 2LE 2LA *)
  | 4, 0 => Some (mkAction 5 DR (Some 2))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DR (Some 0))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 2 DL (Some 4))
  | 4, 5 => Some (mkAction 2 DL (Some 0))
  (* State F (5): 5RB 1RZ 1LF 1LF 1RF 5LF *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 1 DR None)
  | 5, 2 => Some (mkAction 1 DL (Some 5))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 1 DR (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | _, _ => None
  end.

Lemma bb66_valid : ValidTM 6 6 bb66.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 6 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 6 (destruct s as [| s]; [
      do 6 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

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
  exists k' m' t, Reaches bb66 (B5cfg k m (2 :: R)) (B5cfg k' m' R) t /\
    Wfn (2 * m + 1) 0 <= m' /\ m' <= t.
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
  ValidTM 6 6 bb66 /\ exists t, HaltsIn bb66 initConfig t /\ f_omega_mul2_plus 1 2 < t.
Proof.
  split; [exact bb66_valid |].
  pose proof bb66_bootstrap as Hboot.
  destruct (fwm2_step bb66 bb66_core 0 0 [1; 1; 2; 2; 5]) as [t1 [H1 _]].
  destruct (fwm2_step bb66 bb66_core 0 (Wfn 0 0) [1; 2; 2; 5]) as [t2 [H2 _]].
  destruct (fwm2_step bb66 bb66_core 0 (Wfn 0 (Wfn 0 0)) [2; 2; 5]) as [t3 [H3 _]].
  set (m3 := Wfn 0 (Wfn 0 (Wfn 0 0))).
  assert (Hm3 : 2 <= m3).
  { pose proof (Wfn_ge_succ 0 0). pose proof (Wfn_ge_succ 0 (Wfn 0 0)).
     pose proof (Wfn_ge_succ 0 (Wfn 0 (Wfn 0 0))). unfold m3. lia. }
  destruct (rule_2 0 m3 [2; 5]) as [k4 [m4 [t4 [H4 [Hm4 _]]]]].
  destruct (rule_2 k4 m4 [5]) as [k5 [m5 [t5 [H5 [Hm5 Ht5]]]]].
  assert (Hhalt : step bb66 (B5cfg k5 m5 [5]) =
    Some (mkCfgR None (1 :: rep (S k5) 2 (rep (2 * m5 + 1) 3 [5])) [])).
  { apply (step_mkCfgR_R _ 0 0 _ _ 5 [] eq_refl). }
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
  { change (f_omega_mul2_plus 1 2) with (iter f_omega_mul2 2 2). rewrite iter_succ, iter_succ, iter_zero. reflexivity. }
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (fOmegaMul 2 0) with f_omega_mul2 in Hlt2. lia.
Qed.

Print Assumptions bb66_halts_gt_f_omega_mul2_plus_1_2.
