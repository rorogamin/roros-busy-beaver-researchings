(*
  rocq/BB7_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 7):
    TM: 6LF3LB6LA2RA4LB5RC5LA_1RZ3RB1LD2RA3LF5RB6LD_3RB1LB3LC2RC4LC1LE5RB_3RB3RE3LC2RC0LE3RD1LA_5RB3RE2LE4LC3LG5LE1RZ_5RB5RB4RF1LF2LD5LF4RG_5LF1RZ5LB1LG2RG5LG1RZ
    Domain: BB(7, 7) (7 states, 7 symbols)
    Previous best dominated bounds: BB(7, 6) > f_{ω^2}(110), BB(6, 7) > f_{ω×2+1}(6)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+1}(3)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_7.
Import ListNotations.

Definition bb77 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 6LF 3LB 6LA 2RA 4LB 5RC 5LA *)
  | 0, 0 => Some (mkAction 6 DL (Some 5))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 6 DL (Some 0))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 5 DR (Some 2))
  | 0, 6 => Some (mkAction 5 DL (Some 0))
  (* State B (1): 1RZ 3RB 1LD 2RA 3LF 5RB 6LD *)
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 6 DL (Some 3))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 5RB *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 5 DR (Some 1))
  (* State D (3): 3RB 3RE 3LC 2RC 0LE 3RD 1LA *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 0 DL (Some 4))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 1 DL (Some 0))
  (* State E (4): 5RB 3RE 2LE 4LC 3LG 5LE 1RZ *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 2 DL (Some 4))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 1 DR None)
  (* State F (5): 5RB 5RB 4RF 1LF 2LD 5LF 4RG *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 4 DR (Some 5))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 2 DL (Some 3))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 4 DR (Some 6))
  (* State G (6): 5LF 1RZ 5LB 1LG 2RG 5LG 1RZ *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 1 DR None)
  | 6, 2 => Some (mkAction 5 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 2 DR (Some 6))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 1 DR None)
  | _, _ => None
  end.

Lemma bb77_valid : ValidTM 7 7 bb77.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 7 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 7 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb77_core : Fwp2_7Core bb77.
Proof. constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Lemma bb77_bootstrap :
  Reaches bb77 initConfig (Scfg 2 0 0 [2; 2; 2; 2; 1; 5]) 69.
Proof. vm_compute. reflexivity. Qed.

Theorem bb77_halts_gt_f_omega2_plus_1_3 :
  ValidTM 7 7 bb77 /\ exists t, HaltsIn bb77 initConfig t /\ f_omega2_plus 1 3 < t.
Proof.
  split; [exact bb77_valid |].
  pose proof bb77_bootstrap as Hboot.
  destruct (rule_2_7 bb77 bb77_core 1 0 [2; 2; 2; 1; 5]) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_3 : 3 <= m1) by (pose proof H2_7_0_ge; lia).
  destruct (rule_2_7_rep bb77 bb77_core 3 r1 m1 [1; 5]) as [r2 [m2 [t2 [H2r [Hm2 Ht2]]]]].
  destruct (fwp2_step bb77 (f7_fp _ bb77_core) (S r2) 0 m2 [5]) as [t3 [H3 _]].
  destruct (rule_halt_5_7 bb77 bb77_core r2 (Pfn (S r2) 0 m2)) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _
    (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2r) H3) Hhalt) as Hreach.
  pose proof (iter_strict_dom H2_7 f_omega2 1 H2_7_gt (fOmega2_props 1 0 0) 3 3 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H2_7 H2_7_mono 3 3 m1 Hm1_3) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 1 3) with (iter f_omega2 3 3). lia.
Qed.

Print Assumptions bb77_halts_gt_f_omega2_plus_1_3.
