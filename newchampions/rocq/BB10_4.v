From Stdlib Require Import List Lia Arith.
Import ListNotations.
From BB Require Import TM FGH Kropitz Fwp2_4.

(* BB(10,4) champion (fwp21_4):
   1LD2RG2LA3LG_0LI2LH2RB2RF_1LB1RC2RB3LG_0RC1RC1LD3RD_3RD1LE1LE3LE_1RI3LD2LE3LE_1RG1LH2RG3LG_1RC2LH1LA1LE_0LJ1RZ0RE0LI_3RC3LJ3LJ3LJ
   Proves: ValidTM 10 4 bb104 /\ exists t, HaltsIn bb104 initConfig t /\ iter f_omega2 3 3 < t. *)

Definition bb104 : TM := fun s sym =>
  match s, sym with
  (* A (0): 1LD 2RG 2LA 3LG *)
  | 0, 0 => Some (mkAction 1 DL (Some 3))
  | 0, 1 => Some (mkAction 2 DR (Some 6))
  | 0, 2 => Some (mkAction 2 DL (Some 0))
  | 0, 3 => Some (mkAction 3 DL (Some 6))
  (* B (1): 0LI 2LH 2RB 2RF *)
  | 1, 0 => Some (mkAction 0 DL (Some 8))
  | 1, 1 => Some (mkAction 2 DL (Some 7))
  | 1, 2 => Some (mkAction 2 DR (Some 1))
  | 1, 3 => Some (mkAction 2 DR (Some 5))
  (* C (2): 1LB 1RC 2RB 3LG *)
  | 2, 0 => Some (mkAction 1 DL (Some 1))
  | 2, 1 => Some (mkAction 1 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 1))
  | 2, 3 => Some (mkAction 3 DL (Some 6))
  (* D (3): 0RC 1RC 1LD 3RD *)
  | 3, 0 => Some (mkAction 0 DR (Some 2))
  | 3, 1 => Some (mkAction 1 DR (Some 2))
  | 3, 2 => Some (mkAction 1 DL (Some 3))
  | 3, 3 => Some (mkAction 3 DR (Some 3))
  (* E (4): 3RD 1LE 1LE 3LE *)
  | 4, 0 => Some (mkAction 3 DR (Some 3))
  | 4, 1 => Some (mkAction 1 DL (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 4))
  | 4, 3 => Some (mkAction 3 DL (Some 4))
  (* F (5): 1RI 3LD 2LE 3LE *)
  | 5, 0 => Some (mkAction 1 DR (Some 8))
  | 5, 1 => Some (mkAction 3 DL (Some 3))
  | 5, 2 => Some (mkAction 2 DL (Some 4))
  | 5, 3 => Some (mkAction 3 DL (Some 4))
  (* G (6): 1RG 1LH 2RG 3LG *)
  | 6, 0 => Some (mkAction 1 DR (Some 6))
  | 6, 1 => Some (mkAction 1 DL (Some 7))
  | 6, 2 => Some (mkAction 2 DR (Some 6))
  | 6, 3 => Some (mkAction 3 DL (Some 6))
  (* H (7): 1RC 2LH 1LA 1LE *)
  | 7, 0 => Some (mkAction 1 DR (Some 2))
  | 7, 1 => Some (mkAction 2 DL (Some 7))
  | 7, 2 => Some (mkAction 1 DL (Some 0))
  | 7, 3 => Some (mkAction 1 DL (Some 4))
  (* I (8): 0LJ 1RZ 0RE 0LI *)
  | 8, 0 => Some (mkAction 0 DL (Some 9))
  | 8, 1 => Some (mkAction 1 DR None)
  | 8, 2 => Some (mkAction 0 DR (Some 4))
  | 8, 3 => Some (mkAction 0 DL (Some 8))
  (* J (9): 3RC 3LJ 3LJ 3LJ *)
  | 9, 0 => Some (mkAction 3 DR (Some 2))
  | 9, 1 => Some (mkAction 3 DL (Some 9))
  | 9, 2 => Some (mkAction 3 DL (Some 9))
  | 9, 3 => Some (mkAction 3 DL (Some 9))
  | _, _ => None
  end.

Lemma bb104_valid : ValidTM 10 4 bb104.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]; try lia;
    destruct sym as [|[|[|[|sym]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|[|s]]]]]]]]]];
    try (destruct sym as [|[|[|[|sym]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb104_core : Fwp2_4Core bb104.
Proof. constructor; reflexivity. Qed.

Lemma bb104_init :
  Reaches bb104 initConfig (mkCfgR (Some 6) [] (rep 4 3 [0; 0; 0; 1])) 31.
Proof. unfold Reaches. vm_compute. reflexivity. Qed.

Lemma rep_r : forall n v R, rep n v (v :: R) = rep (S n) v R.
Proof. induction n as [| n' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma length_rep : forall n v L, length (rep n v L) = n + length L.
Proof. induction n as [| n' IH]; intros; [reflexivity | simpl; f_equal; apply IH]. Qed.

Lemma bb104_J_sweep_aux : forall L s R,
  (s = 1 \/ s = 2 \/ s = 3) ->
  Forall (fun x => x = 1 \/ x = 2 \/ x = 3) L ->
  exists t, Reaches bb104 (mkCfgR (Some 9) L (s :: R))
                          (mkCfgR (Some 6) [] (rep (S (S (length L))) 3 R)) t.
Proof.
  induction L as [| x L' IH]; intros s R Hs Hfa.
  - (* L = []: J on s writes 3, moves left to 0; J on 0 writes 3, moves right to C; C on 3 writes 3, moves left to G *)
    assert (H1 : Reaches bb104 (mkCfgR (Some 9) [] (s :: R)) (mkCfgR (Some 9) [] (0 :: 3 :: R)) 1).
    { apply steps_one. destruct Hs as [-> | [-> | ->]]; reflexivity. }
    assert (H2 : Reaches bb104 (mkCfgR (Some 9) [] (0 :: 3 :: R)) (mkCfgR (Some 2) [3] (3 :: R)) 1).
    { apply steps_one. reflexivity. }
    assert (H3 : Reaches bb104 (mkCfgR (Some 2) [3] (3 :: R)) (mkCfgR (Some 6) [] (3 :: 3 :: R)) 1).
    { apply steps_one. reflexivity. }
    exists (1 + 1 + 1). eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  - inversion Hfa as [| ? ? Hx Hfa']; subst.
    assert (H1 : Reaches bb104 (mkCfgR (Some 9) (x :: L') (s :: R)) (mkCfgR (Some 9) L' (x :: 3 :: R)) 1).
    { apply steps_one. destruct Hs as [-> | [-> | ->]]; reflexivity. }
    destruct (IH x (3 :: R) Hx Hfa') as [t2 H2].
    exists (1 + t2).
    eapply reaches_trans; [exact H1 |].
    simpl length. rewrite rep_r in H2. exact H2.
Qed.

Lemma forall_rep : forall n v (P : nat -> Prop) L,
  P v -> Forall P L -> Forall P (rep n v L).
Proof.
  induction n as [| n' IH]; intros v P L Hv HL; [exact HL | constructor; [exact Hv | apply IH; assumption]].
Qed.

Lemma f_omega2_props : FGHProps f_omega2.
Proof.
  constructor; unfold f_omega2.
  - intro n. apply (fgh_ge_self _ (fOmegaMul_props n 0) n).
  - intros n Hn. apply (fgh_gt_pos _ (fOmegaMul_props n 0) n Hn).
  - intros x y Hxy.
    eapply Nat.le_trans; [apply (fgh_mono _ (fOmegaMul_props x 0) x y Hxy) |].
    assert (Hma : forall a1 a2 n, a1 <= a2 -> fOmegaMul a1 0 n <= fOmegaMul a2 0 n).
    { intros a1 a2 n Ha. induction Ha as [| a2' Hle IH]; [lia |].
      eapply Nat.le_trans; [exact IH |].
      destruct n as [| n']; [change (fOmegaMul a2' 0 0 <= fOmegaMul a2' 0 0); lia |].
      change (fOmegaMul a2' 0 (S n') <= fOmegaMul a2' (S n') (S n')).
      apply fPlus_mono_idx; [apply (fOmegaMul_props a2' 0) | lia | lia]. }
    apply Hma; exact Hxy.
Qed.

(* One full cycle: G> 3^m 0 (0 :: R) -> G> 3^m' (0 :: R) with f_omega2 (m - 1) < m' *)
Lemma bb104_cycle : forall m R, 3 <= m -> R <> [] ->
  exists m' t, Reaches bb104 (mkCfgR (Some 6) [] (rep m 3 (0 :: 0 :: R)))
                             (mkCfgR (Some 6) [] (rep m' 3 (0 :: R))) t /\
               f_omega2 (m - 1) < m' /\ 3 <= m'.
Proof.
  intros m R Hm HR.
  destruct (f4_rule_G3_rep bb104 bb104_core m (0 :: 0 :: R) ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 _]]]]]].
  assert (H2 : Reaches bb104 (F4cfg (m - 1) a b (0 :: 0 :: R))
                             (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (0 :: R)) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb104 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (0 :: R))
                             (mkCfgR (Some 9) (rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) (1 :: 0 :: R)) 1).
  { apply steps_one. destruct R; [contradiction | reflexivity]. }
  assert (Hfa : Forall (fun x => x = 1 \/ x = 2 \/ x = 3) (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))).
  { apply forall_rep; [right; left; reflexivity |].
    apply forall_rep; [left; reflexivity |].
    apply forall_rep; [right; right; reflexivity | constructor]. }
  destruct (bb104_J_sweep_aux _ 1 (0 :: R) (or_introl eq_refl) Hfa) as [t4 H4].
  exists (S (S (length (rep (S b) 2 (rep a 1 (rep (m - 1) 3 [])))))), (t1 + 1 + 1 + t4).
  split.
  - eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4].
  - rewrite !length_rep, length_nil.
    specialize (Hge1 ltac:(lia)).
    pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)).
    pose proof (fgh_ge_self _ f_omega2_props (m - 1)).
    lia.
Qed.

(* Final halting cycle: G> 3^m 0 1 -> Halts in > f_omega2 (m - 1) steps *)
Lemma bb104_halt : forall m, 3 <= m ->
  exists t, HaltsIn bb104 (mkCfgR (Some 6) [] (rep m 3 [0; 1])) t /\ f_omega2 (m - 1) < t.
Proof.
  intros m Hm.
  destruct (f4_rule_G3_rep bb104 bb104_core m [0; 1] ltac:(lia)) as [a [b [t1 [H1 [Ha [Hge1 Hle1]]]]]].
  assert (H2 : Reaches bb104 (F4cfg (m - 1) a b [0; 1])
                             (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [1]) 1).
  { unfold F4cfg. apply steps_one. reflexivity. }
  assert (H3 : Reaches bb104 (mkCfgR (Some 8) (1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) [1])
                             (mkCfgR None (1 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []) 1).
  { apply steps_one. reflexivity. }
  exists (t1 + 1 + 1). split.
  - unfold HaltsIn. exists (mkCfgR None (1 :: 1 :: rep (S b) 2 (rep a 1 (rep (m - 1) 3 []))) []).
    split; [| reflexivity].
    eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  - specialize (Hge1 ltac:(lia)).
    pose proof (F4B_gt_f_omega2 (m - 1) ltac:(lia)).
    lia.
Qed.

Theorem BB10_4_champion :
  ValidTM 10 4 bb104 /\
  exists t, HaltsIn bb104 initConfig t /\ iter f_omega2 3 3 < t.
Proof.
  split; [exact bb104_valid |].
  pose proof bb104_init as H0.
  destruct (bb104_cycle 4 [0; 1] ltac:(lia) ltac:(discriminate)) as [m1 [t1 [H1 [Hm1 Hge1]]]].
  destruct (bb104_cycle m1 [1] Hge1 ltac:(discriminate)) as [m2 [t2 [H2 [Hm2 Hge2]]]].
  destruct (bb104_halt m2 Hge2) as [t3 [H3 Ht3]].
  destruct H3 as [cf [H3 Hcf]].
  exists (31 + t1 + t2 + t3). split.
  - unfold HaltsIn. exists cf. split; [| exact Hcf].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H0 | exact H1] | exact H2] | exact H3].
  - (* Never normalize concrete f_omega2 3! Use polymorphic monotonicity *)
    assert (Hmono : forall x y, x <= y -> f_omega2 x <= f_omega2 y) by (apply fgh_mono, f_omega2_props).
    replace (4 - 1) with 3 in Hm1 by lia.
    assert (Hstep1 : f_omega2 3 <= m1 - 1) by lia.
    assert (Hstep2 : f_omega2 (f_omega2 3) <= m2 - 1).
    { pose proof (Hmono _ _ Hstep1). lia. }
    assert (Hstep3 : f_omega2 (f_omega2 (f_omega2 3)) < t3).
    { pose proof (Hmono _ _ Hstep2). lia. }
    rewrite !iter_succ, iter_zero.
    lia.
Qed.

Print Assumptions BB10_4_champion.
