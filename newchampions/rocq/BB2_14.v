(*
  rocq/BB2_14.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 14):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA13RA7LB11LB12LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ13LB11LB12LB13LB
    Domain: BB(2, 14) (2 states, 14 symbols)
    Previous best dominated bound: our BB(2, 13) > f_omega(2^16)
    Proved bound here: halts from blank tape in exact s steps with s > f_omega(f_4(2))
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb214 : TM := fun s sym =>
  match s, sym with
  (* State A (0) *)
  | 0, 0  => Some (mkAction 9  DL (Some 1))
  | 0, 1  => Some (mkAction 5  DL (Some 0))
  | 0, 2  => Some (mkAction 1  DL (Some 1))
  | 0, 3  => Some (mkAction 6  DR (Some 0))
  | 0, 4  => Some (mkAction 3  DR (Some 0))
  | 0, 5  => Some (mkAction 4  DR (Some 0))
  | 0, 6  => Some (mkAction 2  DR (Some 1))
  | 0, 7  => Some (mkAction 8  DL (Some 1))
  | 0, 8  => Some (mkAction 5  DL (Some 0))
  | 0, 9  => Some (mkAction 10 DL (Some 0))
  | 0, 10 => Some (mkAction 13 DR (Some 0))
  | 0, 11 => Some (mkAction 7  DL (Some 1))
  | 0, 12 => Some (mkAction 11 DL (Some 1))
  | 0, 13 => Some (mkAction 12 DL (Some 1))
  (* State B (1) *)
  | 1, 0  => Some (mkAction 4  DR (Some 0))
  | 1, 1  => Some (mkAction 1  DL (Some 0))
  | 1, 2  => Some (mkAction 3  DL (Some 1))
  | 1, 3  => Some (mkAction 2  DR (Some 1))
  | 1, 4  => Some (mkAction 2  DR (Some 1))
  | 1, 5  => Some (mkAction 3  DL (Some 0))
  | 1, 6  => Some (mkAction 3  DL (Some 1))
  | 1, 7  => Some (mkAction 7  DL (Some 1))
  | 1, 8  => Some (mkAction 8  DL (Some 1))
  | 1, 9  => Some (mkAction 1  DR None)
  | 1, 10 => Some (mkAction 13 DL (Some 1))
  | 1, 11 => Some (mkAction 11 DL (Some 1))
  | 1, 12 => Some (mkAction 12 DL (Some 1))
  | 1, 13 => Some (mkAction 13 DL (Some 1))
  | _, _  => None
  end.

Lemma bb214_valid : ValidTM 2 14 bb214.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 14 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 14 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb214_core : Kropitz2Core bb214.
Proof. constructor; reflexivity. Qed.

Lemma bb214_bootstrap :
  Reaches bb214 initConfig (B2cfg 4 0 [8; 9]) 76.
Proof. vm_compute. reflexivity. Qed.

Theorem bb214_halts_gt_f_omega_f4_2 :
  ValidTM 2 14 bb214 /\ exists s, HaltsIn bb214 initConfig s /\ f_omega (fFin 4 2) < s.
Proof.
  split; [exact bb214_valid |].
  pose proof bb214_bootstrap as Hboot.
  destruct (kropitz2_step_8 bb214 bb214_core 4 0 [9]) as [t1 [H1 _]].
  remember (Kfn 4 0) as m eqn:Hm.
  destruct (kropitz2_pass2_reload bb214 bb214_core 12 eq_refl eq_refl eq_refl 4 m) as [t2 [H2 _]].
  replace (2 * m + 4 + 1) with (2 * m + 5) in H2 by lia.
  destruct (kropitz2_reload_gen bb214 bb214_core 13 11 eq_refl eq_refl (2 * m + 5) 0 []) as [t3 [H3 _]].
  replace (2 * 0 + (2 * m + 5) + 1) with (2 * m + 6) in H3 by lia.
  destruct (kropitz2_reload_gen bb214 bb214_core 12 10 eq_refl eq_refl (2 * m + 6) 0 []) as [t4 [H4 _]].
  replace (2 * 0 + (2 * m + 6) + 1) with (2 * m + 7) in H4 by lia.
  destruct (kropitz2_reload_gen bb214 bb214_core 11 6 eq_refl eq_refl (2 * m + 7) 0 []) as [t5 [H5 _]].
  replace (2 * 0 + (2 * m + 7) + 1) with (2 * m + 8) in H5 by lia.
  destruct (kropitz2_reload_gen bb214 bb214_core 7 7 eq_refl eq_refl (2 * m + 8) 0 []) as [t6 [H6 _]].
  replace (2 * 0 + (2 * m + 8) + 1) with (2 * m + 9) in H6 by lia.
  destruct (kropitz2_step_8 bb214 bb214_core (2 * m + 9) 0 []) as [t7 [H7 Hle7]].
  destruct (kropitz2_halt bb214 bb214_core eq_refl eq_refl (2 * m + 9) (Kfn (2 * m + 9) 0)) as [cf [Hhalt Hst]].
  pose proof (Kfn_zero_gt_fFin2 4 ltac:(lia)) as Hf4.
  assert (Hle_arg : fFin 4 2 <= 2 * m + 8) by lia.
  pose proof (fgh_mono _ (fOmegaMul_props 1 0) _ _ Hle_arg) as Hmono.
  pose proof (Kfn_zero_gt_fOmega (2 * m + 8)) as Hgt.
  replace (S (2 * m + 8)) with (2 * m + 9) in Hgt by lia.
  eexists. split.
  - exists cf. split; [exact (reaches_trans _ _ _ _ _ _ Hboot (reaches_trans _ _ _ _ _ _ H1
      (reaches_trans _ _ _ _ _ _ H2 (reaches_trans _ _ _ _ _ _ H3
        (reaches_trans _ _ _ _ _ _ H4 (reaches_trans _ _ _ _ _ _ H5
          (reaches_trans _ _ _ _ _ _ H6 (reaches_trans _ _ _ _ _ _ H7 Hhalt)))))))) | exact Hst].
  - change (fOmegaMul 1 0) with f_omega in Hmono. lia.
Qed.

Print Assumptions bb214_halts_gt_f_omega_f4_2.
