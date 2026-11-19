(*
  rocq/BB2_11.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(2, 11):
    TM: 9LB5LA1LB6RA3RA4RA2RB8LB5LA10LA7RA_4RA1LA3LB2RB2RB3LA3LB7LB8LB1RZ7LB
    Domain: BB(2, 11) (2 states, 11 symbols)
    Previous best dominated bound: BB(2, 9) > 10^^10^^10^^10^^10^^155 (< f_4(3) < f_5(2))
    Proved bound here: halts from blank tape in exact s steps with s > f_7(2)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Kropitz2.
Import ListNotations.

Definition bb211 : TM := fun s sym =>
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
  | 0, 10 => Some (mkAction 7  DR (Some 0))
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
  | 1, 10 => Some (mkAction 7  DL (Some 1))
  | _, _  => None
  end.

Lemma bb211_valid : ValidTM 2 11 bb211.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|s]]; try lia;
    do 11 (destruct sym as [|sym]; [simpl; lia |]); lia.
  - destruct s as [|[|s]];
    try (do 11 (destruct sym as [|sym]; [lia |]); reflexivity);
    reflexivity.
Qed.

Lemma bb211_core : Kropitz2Core bb211.
Proof. constructor; reflexivity. Qed.

Lemma bb211_bootstrap :
  Reaches bb211 initConfig (B2cfg 7 0 [8]) 179.
Proof. vm_compute. reflexivity. Qed.

Theorem bb211_halts_gt_f_7_2 :
  ValidTM 2 11 bb211 /\ exists s, HaltsIn bb211 initConfig s /\ fFin 7 2 < s.
Proof.
  split; [exact bb211_valid |].
  pose proof bb211_bootstrap as Hboot.
  destruct (kropitz2_step_8 bb211 bb211_core 7 0 []) as [t1 [H1 Hle1]].
  destruct (kropitz2_halt bb211 bb211_core eq_refl eq_refl 7 (Kfn 7 0)) as [cf [Hhalt Hst]].
  pose proof (Kfn_zero_gt_fFin2 7 ltac:(lia)) as Hbound.
  eexists. split.
  - exists cf. split; [exact (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) Hhalt) | exact Hst].
  - lia.
Qed.

Print Assumptions bb211_halts_gt_f_7_2.
