(*
  rocq/BB2_17.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 17):
    Domain: BB(2, 17) (2 states, 17 symbols)
    Previous best dominated bound: our BB(2, 16) > f_ω(f_6(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_7(2))
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb217 : TM := fun s sym =>
  match s, sym with
  | 0, 0  => Some (mkAction 9 DL (Some 1))
  | 0, 1  => Some (mkAction 5 DL (Some 0))
  | 0, 2  => Some (mkAction 1 DL (Some 1))
  | 0, 3  => Some (mkAction 6 DR (Some 0))
  | 0, 4  => Some (mkAction 3 DR (Some 0))
  | 0, 5  => Some (mkAction 4 DR (Some 0))
  | 0, 6  => Some (mkAction 2 DR (Some 1))
  | 0, 7  => Some (mkAction 8 DL (Some 1))
  | 0, 8  => Some (mkAction 5 DL (Some 0))
  | 0, 9  => Some (mkAction 10 DL (Some 0))
  | 0, 10 => Some (mkAction 16 DR (Some 0))
  | 0, 11 => Some (mkAction 7 DL (Some 1))
  | 0, 12 => Some (mkAction 11 DL (Some 1))
  | 0, 13 => Some (mkAction 12 DL (Some 1))
  | 0, 14 => Some (mkAction 13 DL (Some 1))
  | 0, 15 => Some (mkAction 14 DL (Some 1))
  | 0, 16 => Some (mkAction 15 DL (Some 1))
  | 1, 0  => Some (mkAction 4 DR (Some 0))
  | 1, 1  => Some (mkAction 1 DL (Some 0))
  | 1, 2  => Some (mkAction 3 DL (Some 1))
  | 1, 3  => Some (mkAction 2 DR (Some 1))
  | 1, 4  => Some (mkAction 2 DR (Some 1))
  | 1, 5  => Some (mkAction 3 DL (Some 0))
  | 1, 6  => Some (mkAction 3 DL (Some 1))
  | 1, 7  => Some (mkAction 7 DL (Some 1))
  | 1, 8  => Some (mkAction 8 DL (Some 1))
  | 1, 9  => Some (mkAction 1 DR None)
  | 1, 10 => Some (mkAction 16 DL (Some 1))
  | 1, 11 => Some (mkAction 11 DL (Some 1))
  | 1, 12 => Some (mkAction 12 DL (Some 1))
  | 1, 13 => Some (mkAction 13 DL (Some 1))
  | 1, 14 => Some (mkAction 14 DL (Some 1))
  | 1, 15 => Some (mkAction 15 DL (Some 1))
  | 1, 16 => Some (mkAction 16 DL (Some 1))
  | _, _  => None
  end.

Lemma bb217_valid : ValidTM 2 17 bb217.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 17 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 17 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb217_core : Kropitz2Core bb217.
Proof. constructor; reflexivity. Qed.

Lemma bb217_bootstrap : Reaches bb217 initConfig (B2cfg 7 0 [8; 9]) 166.
Proof.
  assert (H1 : Reaches bb217 initConfig (mkCfgR (Some 1) [] [4; 3; 3; 14; 9]) 25) by reflexivity.
  assert (H2 : Reaches bb217 (mkCfgR (Some 1) [] [4; 3; 3; 14; 9]) (mkCfgR (Some 0) [4] [3; 3; 3; 3; 13; 9]) 25) by reflexivity.
  assert (H3 : Reaches bb217 (mkCfgR (Some 0) [4] [3; 3; 3; 3; 13; 9]) (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 12; 9]) 25) by reflexivity.
  assert (H4 : Reaches bb217 (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 12; 9]) (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 3; 11; 9]) 25) by reflexivity.
  assert (H5 : Reaches bb217 (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 3; 11; 9]) (mkCfgR (Some 0) [4] [3; 3; 3; 3; 3; 3; 3; 7; 9]) 25) by reflexivity.
  assert (H6 : Reaches bb217 (mkCfgR (Some 0) [4] [3; 3; 3; 3; 3; 3; 3; 7; 9]) (mkCfgR (Some 1) [2; 2; 2; 2; 2; 2] [2; 3; 8; 9]) 25) by reflexivity.
  assert (H7 : Reaches bb217 (mkCfgR (Some 1) [2; 2; 2; 2; 2; 2] [2; 3; 8; 9]) (B2cfg 7 0 [8; 9]) 16) by reflexivity.
  replace 166 with (25 + (25 + (25 + (25 + (25 + (25 + (16))))))) by lia.
  eapply reaches_trans; [exact H1 |].
  eapply reaches_trans; [exact H2 |].
  eapply reaches_trans; [exact H3 |].
  eapply reaches_trans; [exact H4 |].
  eapply reaches_trans; [exact H5 |].
  eapply reaches_trans; [exact H6 |].
  exact H7.
Qed.

Theorem bb217_halts_gt_f_omega_f7_2 :
  ValidTM 2 17 bb217 /\ exists s, HaltsIn bb217 initConfig s /\ f_omega (fFin 7 2) < s.
Proof.
  split; [exact bb217_valid |].
  pose proof bb217_bootstrap as Hboot.
  remember (Kfn 7 0) as m eqn:Hm.
  destruct (kropitz2_step_8 bb217 bb217_core 7 0 [9]) as [t1 [H1 _]].
  rewrite <- Hm in H1.
  destruct (kropitz2_pass2_reload bb217 bb217_core 15 eq_refl eq_refl eq_refl 7 m) as [t2 [H2 _]].
  replace (2 * m + 7 + 1) with (2 * m + 8) in H2 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 16 14 eq_refl eq_refl (2 * m + 8) 0 []) as [t3 [H3 _]].
  replace (2 * 0 + (2 * m + 8) + 1) with (2 * m + 9) in H3 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 15 13 eq_refl eq_refl (2 * m + 9) 0 []) as [t4 [H4 _]].
  replace (2 * 0 + (2 * m + 9) + 1) with (2 * m + 10) in H4 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 14 12 eq_refl eq_refl (2 * m + 10) 0 []) as [t5 [H5 _]].
  replace (2 * 0 + (2 * m + 10) + 1) with (2 * m + 11) in H5 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 13 11 eq_refl eq_refl (2 * m + 11) 0 []) as [t6 [H6 _]].
  replace (2 * 0 + (2 * m + 11) + 1) with (2 * m + 12) in H6 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 12 10 eq_refl eq_refl (2 * m + 12) 0 []) as [t7 [H7 _]].
  replace (2 * 0 + (2 * m + 12) + 1) with (2 * m + 13) in H7 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 11 6 eq_refl eq_refl (2 * m + 13) 0 []) as [t8 [H8 _]].
  replace (2 * 0 + (2 * m + 13) + 1) with (2 * m + 14) in H8 by lia.
  destruct (kropitz2_reload_gen bb217 bb217_core 7 7 eq_refl eq_refl (2 * m + 14) 0 []) as [t9 [H9 _]].
  replace (2 * 0 + (2 * m + 14) + 1) with (2 * m + 15) in H9 by lia.
  destruct (kropitz2_step_8 bb217 bb217_core (2 * m + 15) 0 []) as [t10 [H10 Hle10]].
  destruct (kropitz2_halt bb217 bb217_core eq_refl eq_refl (2 * m + 15) (Kfn (2 * m + 15) 0)) as [cf [Hhalt Hst]].
  exists (166 + (t1 + (t2 + (t3 + (t4 + (t5 + (t6 + (t7 + (t8 + (t9 + (t10 + ((2 * (2 * m + 15) + 5))))))))))))).
  split.
  - exists cf. split; [| exact Hst].
    eapply reaches_trans; [exact Hboot |].
    eapply reaches_trans; [exact H1 |].
    eapply reaches_trans; [exact H2 |].
    eapply reaches_trans; [exact H3 |].
    eapply reaches_trans; [exact H4 |].
    eapply reaches_trans; [exact H5 |].
    eapply reaches_trans; [exact H6 |].
    eapply reaches_trans; [exact H7 |].
    eapply reaches_trans; [exact H8 |].
    eapply reaches_trans; [exact H9 |].
    eapply reaches_trans; [exact H10 |].
    exact Hhalt.
  - remember (fFin 7 2) as x0 eqn:Hx0.
    pose proof (Kfn_zero_gt_fFin2 7 ltac:(lia)) as Hfk.
    rewrite <- Hx0, <- Hm in Hfk. clear Hx0 Hm.
    pose proof (fgh_mono _ (fOmegaMul_props 1 0) x0 (2 * m + 14) ltac:(lia)) as Hmono.
    change (fOmegaMul 1 0 x0 <= fOmegaMul 1 0 (2 * m + 14))
      with (f_omega x0 <= f_omega (2 * m + 14)) in Hmono.
    pose proof (Kfn_zero_gt_fOmega (2 * m + 14)) as Hgt.
    replace (S (2 * m + 14)) with (2 * m + 15) in Hgt by lia.
    lia.
Qed.

Print Assumptions bb217_halts_gt_f_omega_f7_2.
