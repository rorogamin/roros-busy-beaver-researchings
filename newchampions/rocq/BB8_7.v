(*
  rocq/BB8_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(8, 7):
    TM: 6LC3LB2LH2RA4LB6LH1RZ_5RA3RB1LD2RA3LF5RB0RH_3RB1LB3LC2RC4LC1LE4LH_3RB3RE3LC2RC5RF3RD1RZ_5RB3RE4RG4LC3LG5LE1RZ_5RB5RB1RZ1LF5LF5LF1RH_5LF4RG1LB1LG5LD5LG2LH_5LA0LH1LH1LH2LH5RG1RZ
    Domain: BB(8, 7) (8 states, 7 symbols)
    Previous best dominated bounds: BB(8, 6) > f_{ω^2+1}(f_ω(31)), BB(7, 7) > f_{ω^2+1}(3)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+2}(8)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H.
Import ListNotations.

Definition bb87 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6LC 3LB 2LH 2RA 4LB 6LH 1RZ *)
  | 0, 0 => Some (mkAction 6 DL (Some 2))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 6 DL (Some 7))
  | 0, 6 => Some (mkAction 1 DR None)
  (* State B (1): 5RA 3RB 1LD 2RA 3LF 5RB 0RH *)
  | 1, 0 => Some (mkAction 5 DR (Some 0))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 0 DR (Some 7))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 4LH *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 4 DL (Some 7))
  (* State D (3): 3RB 3RE 3LC 2RC 5RF 3RD 1RZ *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 5 DR (Some 5))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 1 DR None)
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 1RZ *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 1 DR None)
  (* State F (5): 5RB 5RB 1RZ 1LF 5LF 5LF 1RH *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 1 DR None)
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 1 DR (Some 7))
  (* State G (6): 5LF 4RG 1LB 1LG 5LD 5LG 2LH *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 5 DL (Some 3))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  (* State H (7): 5LA 0LH 1LH 1LH 2LH 5RG 1RZ *)
  | 7, 0 => Some (mkAction 5 DL (Some 0))
  | 7, 1 => Some (mkAction 0 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 1 DR None)
  | _, _ => None
  end.

Lemma bb87_valid : ValidTM 8 7 bb87.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 8 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 8 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb87_core : Fwp2_HCore bb87.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Local Lemma loop_H4 : forall n L R,
  Reaches bb87 (mkCfgR (Some 7) (rep n 4 L) (4 :: R))
               (mkCfgR (Some 7) L (4 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 4 4 _ _ R eq_refl) |].
  specialize (IH L (2 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_5 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb87 (Scfg (S r) 0 m (5 :: R)) (Scfg (S (S r')) 0 m' R) t /\
    H_plus2 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (sweep_HG bb87 bb87_core r m 6 R) as [ts Hs].
  destruct (exec_G2_2s bb87 bb87_core r m R Hm) as [r' [m' [te [He [Hme Hte]]]]].
  exists r', m'. eexists. split.
  - eapply reaches_trans; [| exact He].
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 0 5 2 5 _ _ R eq_refl) |].
    eapply reaches_trans; [exact Hs |].
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 6 1 4 6 _ _ R eq_refl) |].
    eapply reaches_trans; [apply (loop_H4 (2 * m + 1) (rep (S r) 5 []) (2 :: R)) |].
    rewrite rep_snoc_one.
    eapply steps_succ; [apply (step_mkCfgR_L_cons _ 7 1 5 4 _ _ _ eq_refl) |].
    replace (2 :: 2 :: rep (2 * m + 1) 2 R) with (rep (2 * m + 3) 2 R)
      by (replace (2 * m + 3) with (S (S (2 * m + 1))) by lia; reflexivity).
    apply steps_one. apply (step_mkCfgR_R _ 7 4 _ _ 5 _ eq_refl).
  - split; [exact Hme | lia].
Qed.

Lemma rule_5_rep : forall n r m R, 1 <= m ->
  exists r' m' t, Reaches bb87 (Scfg (S r) 0 m (rep n 5 R)) (Scfg (S r') 0 m' R) t /\
    iter H_plus2 n m <= m' /\ (1 <= n -> m' <= t).
Proof.
  induction n as [| p IH]; intros r m R Hm.
  - exists r, m, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
  - destruct p as [| p'].
    + destruct (rule_5 r m R Hm) as [r1 [m1 [t1 [H1 [Hm1 Ht1]]]]].
      exists (S r1), m1, t1. split; [exact H1 | split; [exact Hm1 | intros _; exact Ht1]].
    + destruct (rule_5 r m (rep (S p') 5 R) Hm) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
      assert (Hm1p : 1 <= m1) by (pose proof (H_plus2_ge_17 m); lia).
      destruct (IH (S r1) m1 R Hm1p) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
      exists r2, m2, (t1 + t2). split; [eapply reaches_trans; eassumption | split].
      * replace (iter H_plus2 (S (S p')) m) with (iter H_plus2 (S p') (H_plus2 m))
          by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
        eapply Nat.le_trans; [apply iter_mono_arg; [apply H_plus2_mono | exact Hm1] | exact Hm2].
      * intros _. pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb87_bootstrap :
  Reaches bb87 initConfig (Scfg 3 0 1 (rep 9 5 [1; 6])) 160.
Proof. vm_compute. reflexivity. Qed.

Theorem bb87_halts_gt_f_omega2_plus_2_8 :
  ValidTM 8 7 bb87 /\ exists t, HaltsIn bb87 initConfig t /\ f_omega2_plus 2 8 < t.
Proof.
  split; [exact bb87_valid |].
  pose proof bb87_bootstrap as Hboot.
  destruct (rule_5 2 1 (rep 8 5 [1; 6]) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_8 : 8 <= m1) by (pose proof (H_plus2_ge_17 1); lia).
  destruct (rule_5_rep 8 (S r1) m1 [1; 6] ltac:(lia)) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (fwp2_step bb87 (fh_fp _ bb87_core) (S r2) 0 m2 [6]) as [t3 [H3 _]].
  assert (Hhalt : step bb87 (Scfg (S r2) 0 (Pfn (S r2) 0 m2) [6]) =
    Some (mkCfgR None (1 :: 2 :: rep (2 * Pfn (S r2) 0 m2 + 1) 3 (rep (S r2) 5 [])) [])).
  { apply (step_mkCfgR_R _ 0 0 _ _ 6 [] eq_refl). }
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) H3)
    (steps_one _ _ _ Hhalt)) as Hreach.
  pose proof (iter_strict_dom H_plus2 (f_omega2_plus 1) 1 H_plus2_gt (fOmega2_props 1 0 1) 8 8 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H_plus2 H_plus2_mono 8 8 m1 Hm1_8) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | reflexivity] |].
  change (f_omega2_plus 2 8) with (iter (f_omega2_plus 1) 8 8). lia.
Qed.

Print Assumptions bb87_halts_gt_f_omega2_plus_2_8.
