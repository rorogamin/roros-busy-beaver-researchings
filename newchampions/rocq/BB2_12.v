(*
  rocq/BB2_12.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 12):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA11RA7LB_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ11LB11LB
    Domain: BB(2, 12) (2 states, 12 symbols)
    Previous best dominated bound: our BB(2, 11) > f_7(2)
    Proved bound here: halts from blank tape in exact s steps with s > f_{17}(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb212 : TM := fun s sym =>
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
  | 0, 10 => Some (mkAction 11 DR (Some 0))
  | 0, 11 => Some (mkAction 7  DL (Some 1))
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
  | 1, 10 => Some (mkAction 11 DL (Some 1))
  | 1, 11 => Some (mkAction 11 DL (Some 1))
  | _, _  => None
  end.

Lemma bb212_valid : ValidTM 2 12 bb212.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 12 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 12 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb212_core : Kropitz2Core bb212.
Proof. constructor; reflexivity. Qed.

Lemma bb212_bootstrap :
  Reaches bb212 initConfig (B2cfg 2 0 [8; 9]) 36.
Proof. vm_compute. reflexivity. Qed.

Theorem bb212_halts_gt_f_17_2 :
  ValidTM 2 12 bb212 /\ exists s, HaltsIn bb212 initConfig s /\ fFin 17 2 < s.
Proof.
  split; [exact bb212_valid |].
  pose proof bb212_bootstrap as Hboot.
  destruct (kropitz2_step_8 bb212 bb212_core 2 0 [9]) as [t1 [H1 _]].
  rewrite Kfn_2_0_eq in H1.
  destruct (kropitz2_pass2_reload bb212 bb212_core 10 eq_refl eq_refl eq_refl 2 6) as [t2 [H2 _]].
  destruct (kropitz2_reload_gen bb212 bb212_core 11 6 eq_refl eq_refl 15 0 []) as [t3 [H3 _]].
  destruct (kropitz2_reload_gen bb212 bb212_core 7 7 eq_refl eq_refl 16 0 []) as [t4 [H4 _]].
  destruct (kropitz2_step_8 bb212 bb212_core 17 0 []) as [t5 [H5 Hle5]].
  destruct (kropitz2_halt bb212 bb212_core eq_refl eq_refl 17 (Kfn 17 0)) as [cf [Hhalt Hst]].
  pose proof (Kfn_zero_gt_fFin2 17 ltac:(lia)) as Hbound.
  eexists. split.
  - exists cf. split; [exact (reaches_trans _ _ _ _ _ _ Hboot (reaches_trans _ _ _ _ _ _ H1
      (reaches_trans _ _ _ _ _ _ H2 (reaches_trans _ _ _ _ _ _ H3
        (reaches_trans _ _ _ _ _ _ H4 (reaches_trans _ _ _ _ _ _ H5 Hhalt)))))) | exact Hst].
  - lia.
Qed.

Print Assumptions bb212_halts_gt_f_17_2.
