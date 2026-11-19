(*
  rocq/BB2_15.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 15):
    Domain: BB(2, 15) (2 states, 15 symbols)
    Previous best dominated bound: our BB(2, 14) > f_ω(f_4(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_ω(f_5(2))
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb215 : TM := fun s sym =>
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
  | 0, 10 => Some (mkAction 14 DR (Some 0))
  | 0, 11 => Some (mkAction 7 DL (Some 1))
  | 0, 12 => Some (mkAction 11 DL (Some 1))
  | 0, 13 => Some (mkAction 12 DL (Some 1))
  | 0, 14 => Some (mkAction 13 DL (Some 1))
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
  | 1, 10 => Some (mkAction 14 DL (Some 1))
  | 1, 11 => Some (mkAction 11 DL (Some 1))
  | 1, 12 => Some (mkAction 12 DL (Some 1))
  | 1, 13 => Some (mkAction 13 DL (Some 1))
  | 1, 14 => Some (mkAction 14 DL (Some 1))
  | _, _  => None
  end.

Lemma bb215_valid : ValidTM 2 15 bb215.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 15 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 15 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb215_core : Kropitz2Core bb215.
Proof. constructor; reflexivity. Qed.

Lemma bb215_bootstrap : Reaches bb215 initConfig (B2cfg 5 0 [8; 9]) 102.
Proof.
  assert (H1 : Reaches bb215 initConfig (mkCfgR (Some 1) [] [4; 3; 3; 12; 9]) 25) by reflexivity.
  assert (H2 : Reaches bb215 (mkCfgR (Some 1) [] [4; 3; 3; 12; 9]) (mkCfgR (Some 0) [4] [3; 3; 3; 3; 11; 9]) 25) by reflexivity.
  assert (H3 : Reaches bb215 (mkCfgR (Some 0) [4] [3; 3; 3; 3; 11; 9]) (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 7; 9]) 25) by reflexivity.
  assert (H4 : Reaches bb215 (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 7; 9]) (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 3; 8; 9]) 25) by reflexivity.
  assert (H5 : Reaches bb215 (mkCfgR (Some 0) [6; 6; 6; 6; 4] [3; 3; 8; 9]) (B2cfg 5 0 [8; 9]) 2) by reflexivity.
  replace 102 with (25 + (25 + (25 + (25 + (2))))) by lia.
  eapply reaches_trans; [exact H1 |].
  eapply reaches_trans; [exact H2 |].
  eapply reaches_trans; [exact H3 |].
  eapply reaches_trans; [exact H4 |].
  exact H5.
Qed.

Theorem bb215_halts_gt_f_omega_f5_2 :
  ValidTM 2 15 bb215 /\ exists s, HaltsIn bb215 initConfig s /\ f_omega (fFin 5 2) < s.
Proof.
  split; [exact bb215_valid |].
  pose proof bb215_bootstrap as Hboot.
  remember (Kfn 5 0) as m eqn:Hm.
  destruct (kropitz2_step_8 bb215 bb215_core 5 0 [9]) as [t1 [H1 _]].
  rewrite <- Hm in H1.
  destruct (kropitz2_pass2_reload bb215 bb215_core 13 eq_refl eq_refl eq_refl 5 m) as [t2 [H2 _]].
  replace (2 * m + 5 + 1) with (2 * m + 6) in H2 by lia.
  destruct (kropitz2_reload_gen bb215 bb215_core 14 12 eq_refl eq_refl (2 * m + 6) 0 []) as [t3 [H3 _]].
  replace (2 * 0 + (2 * m + 6) + 1) with (2 * m + 7) in H3 by lia.
  destruct (kropitz2_reload_gen bb215 bb215_core 13 11 eq_refl eq_refl (2 * m + 7) 0 []) as [t4 [H4 _]].
  replace (2 * 0 + (2 * m + 7) + 1) with (2 * m + 8) in H4 by lia.
  destruct (kropitz2_reload_gen bb215 bb215_core 12 10 eq_refl eq_refl (2 * m + 8) 0 []) as [t5 [H5 _]].
  replace (2 * 0 + (2 * m + 8) + 1) with (2 * m + 9) in H5 by lia.
  destruct (kropitz2_reload_gen bb215 bb215_core 11 6 eq_refl eq_refl (2 * m + 9) 0 []) as [t6 [H6 _]].
  replace (2 * 0 + (2 * m + 9) + 1) with (2 * m + 10) in H6 by lia.
  destruct (kropitz2_reload_gen bb215 bb215_core 7 7 eq_refl eq_refl (2 * m + 10) 0 []) as [t7 [H7 _]].
  replace (2 * 0 + (2 * m + 10) + 1) with (2 * m + 11) in H7 by lia.
  destruct (kropitz2_step_8 bb215 bb215_core (2 * m + 11) 0 []) as [t8 [H8 Hle8]].
  destruct (kropitz2_halt bb215 bb215_core eq_refl eq_refl (2 * m + 11) (Kfn (2 * m + 11) 0)) as [cf [Hhalt Hst]].
  exists (102 + (t1 + (t2 + (t3 + (t4 + (t5 + (t6 + (t7 + (t8 + ((2 * (2 * m + 11) + 5))))))))))).
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
    exact Hhalt.
  - remember (fFin 5 2) as x0 eqn:Hx0.
    pose proof (Kfn_zero_gt_fFin2 5 ltac:(lia)) as Hfk.
    rewrite <- Hx0, <- Hm in Hfk. clear Hx0 Hm.
    pose proof (fgh_mono _ (fOmegaMul_props 1 0) x0 (2 * m + 10) ltac:(lia)) as Hmono.
    change (fOmegaMul 1 0 x0 <= fOmegaMul 1 0 (2 * m + 10))
      with (f_omega x0 <= f_omega (2 * m + 10)) in Hmono.
    pose proof (Kfn_zero_gt_fOmega (2 * m + 10)) as Hgt.
    replace (S (2 * m + 10)) with (2 * m + 11) in Hgt by lia.
    lia.
Qed.

Print Assumptions bb215_halts_gt_f_omega_f5_2.
