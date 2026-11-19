(*
  rocq/BB2_13.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 13):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA12RA7LB11LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ12LB11LB12LB
    Domain: BB(2, 13) (2 states, 13 symbols)
    Previous best dominated bound: our BB(2, 12) > f_{17}(2)
    Proved bound here: halts from blank tape in exact s steps with s > f_omega(2^16)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb213 : TM := fun s sym =>
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
  | 0, 10 => Some (mkAction 12 DR (Some 0))
  | 0, 11 => Some (mkAction 7  DL (Some 1))
  | 0, 12 => Some (mkAction 11 DL (Some 1))
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
  | 1, 10 => Some (mkAction 12 DL (Some 1))
  | 1, 11 => Some (mkAction 11 DL (Some 1))
  | 1, 12 => Some (mkAction 12 DL (Some 1))
  | _, _  => None
  end.

Lemma bb213_valid : ValidTM 2 13 bb213.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 13 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 13 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb213_core : Kropitz2Core bb213.
Proof. constructor; reflexivity. Qed.

Lemma bb213_bootstrap :
  Reaches bb213 initConfig (B2cfg 3 0 [8; 9]) 54.
Proof. vm_compute. reflexivity. Qed.

Theorem bb213_halts_gt_f_omega_2_16 :
  ValidTM 2 13 bb213 /\ exists s, HaltsIn bb213 initConfig s /\ f_omega (2 ^ 16) < s.
Proof.
  split; [exact bb213_valid |].
  pose proof bb213_bootstrap as Hboot.
  destruct (kropitz2_step_8 bb213 bb213_core 3 0 [9]) as [t1 [H1 _]].
  remember (Kfn 3 0) as m eqn:Hm.
  destruct (kropitz2_pass2_reload bb213 bb213_core 11 eq_refl eq_refl eq_refl 3 m) as [t2 [H2 _]].
  replace (2 * m + 3 + 1) with (2 * m + 4) in H2 by lia.
  destruct (kropitz2_reload_gen bb213 bb213_core 12 10 eq_refl eq_refl (2 * m + 4) 0 []) as [t3 [H3 _]].
  replace (2 * 0 + (2 * m + 4) + 1) with (2 * m + 5) in H3 by lia.
  destruct (kropitz2_reload_gen bb213 bb213_core 11 6 eq_refl eq_refl (2 * m + 5) 0 []) as [t4 [H4 _]].
  replace (2 * 0 + (2 * m + 5) + 1) with (2 * m + 6) in H4 by lia.
  destruct (kropitz2_reload_gen bb213 bb213_core 7 7 eq_refl eq_refl (2 * m + 6) 0 []) as [t5 [H5 _]].
  replace (2 * 0 + (2 * m + 6) + 1) with (2 * m + 7) in H5 by lia.
  destruct (kropitz2_step_8 bb213 bb213_core (2 * m + 7) 0 []) as [t6 [H6 Hle6]].
  destruct (kropitz2_halt bb213 bb213_core eq_refl eq_refl (2 * m + 7) (Kfn (2 * m + 7) 0)) as [cf [Hhalt Hst]].
  pose proof Kfn_3_0_pow as Hpow15.
  assert (Hpow16 : 2 ^ 16 = 2 * 2 ^ 15).
  { replace 16 with (S 15) by lia. rewrite Nat.pow_succ_r by lia. reflexivity. }
  assert (Hle_arg : 2 ^ 16 <= 2 * m + 6) by lia.
  pose proof (fgh_mono _ (fOmegaMul_props 1 0) _ _ Hle_arg) as Hmono.
  pose proof (Kfn_zero_gt_fOmega (2 * m + 6)) as Hgt.
  replace (S (2 * m + 6)) with (2 * m + 7) in Hgt by lia.
  eexists. split.
  - exists cf. split; [exact (reaches_trans _ _ _ _ _ _ Hboot (reaches_trans _ _ _ _ _ _ H1
      (reaches_trans _ _ _ _ _ _ H2 (reaches_trans _ _ _ _ _ _ H3
        (reaches_trans _ _ _ _ _ _ H4 (reaches_trans _ _ _ _ _ _ H5
          (reaches_trans _ _ _ _ _ _ H6 Hhalt))))))) | exact Hst].
  - change (fOmegaMul 1 0) with f_omega in Hmono. lia.
Qed.

Print Assumptions bb213_halts_gt_f_omega_2_16.
