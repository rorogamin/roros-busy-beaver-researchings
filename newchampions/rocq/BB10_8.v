(*
  rocq/BB10_8.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(10, 8):
    TM: 1RJ3LB2LH2RA4LB6RI6LH7LH_7LE3RB1LD2RA3LF5RB3RC3RC_3RB1LB3LC2RC4LC1LE2RA3RE_3RB3RE3LC2RC6LD3RD3RB7RB_5RB3RE4RG4LC3LG5LE6LH3RF_5RB1RJ7RI1LF5LF5LF0LD2RA_5LF4RG1LB1LG5RJ5LG2LH6LD_7RH2RF1LH1LH2LH5RG3RJ6RH_1RZ5LJ1LI1LI6LB5RH1LI5RH_4RF5LA7LJ7LJ1RZ5RB7LJ6LG
    Domain: BB(10, 8) (10 states, 8 symbols)
    Previous best dominated bounds: BB(9, 8) > f_{ω^2+4}(7), BB(10, 7) > f_{ω^2+4}(4)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb108 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1RJ 3LB 2LH 2RA 4LB 6RI 6LH 7LH *)
  | 0, 0 => Some (mkAction 1 DR (Some 9))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 6 DR (Some 8))
  | 0, 6 => Some (mkAction 6 DL (Some 7))
  | 0, 7 => Some (mkAction 7 DL (Some 7))
  (* State B (1): 7LE 3RB 1LD 2RA 3LF 5RB 3RC 3RC *)
  | 1, 0 => Some (mkAction 7 DL (Some 4))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 3 DR (Some 2))
  | 1, 7 => Some (mkAction 3 DR (Some 2))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 3RE *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 2 DR (Some 0))
  | 2, 7 => Some (mkAction 3 DR (Some 4))
  (* State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 7RB *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 6 DL (Some 3))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 3 DR (Some 1))
  | 3, 7 => Some (mkAction 7 DR (Some 1))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 6LH 3RF *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 6 DL (Some 7))
  | 4, 7 => Some (mkAction 3 DR (Some 5))
  (* State F (5): 5RB 1RJ 7RI 1LF 5LF 5LF 0LD 2RA *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 1 DR (Some 9))
  | 5, 2 => Some (mkAction 7 DR (Some 8))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 0 DL (Some 3))
  | 5, 7 => Some (mkAction 2 DR (Some 0))
  (* State G (6): 5LF 4RG 1LB 1LG 5RJ 5LG 2LH 6LD *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 5 DR (Some 9))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  | 6, 7 => Some (mkAction 6 DL (Some 3))
  (* State H (7): 7RH 2RF 1LH 1LH 2LH 5RG 3RJ 6RH *)
  | 7, 0 => Some (mkAction 7 DR (Some 7))
  | 7, 1 => Some (mkAction 2 DR (Some 5))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 3 DR (Some 9))
  | 7, 7 => Some (mkAction 6 DR (Some 7))
  (* State I (8): 1RZ 5LJ 1LI 1LI 6LB 5RH 1LI 5RH *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 5 DL (Some 9))
  | 8, 2 => Some (mkAction 1 DL (Some 8))
  | 8, 3 => Some (mkAction 1 DL (Some 8))
  | 8, 4 => Some (mkAction 6 DL (Some 1))
  | 8, 5 => Some (mkAction 5 DR (Some 7))
  | 8, 6 => Some (mkAction 1 DL (Some 8))
  | 8, 7 => Some (mkAction 5 DR (Some 7))
  (* State J (9): 4RF 5LA 7LJ 7LJ 1RZ 5RB 7LJ 6LG *)
  | 9, 0 => Some (mkAction 4 DR (Some 5))
  | 9, 1 => Some (mkAction 5 DL (Some 0))
  | 9, 2 => Some (mkAction 7 DL (Some 9))
  | 9, 3 => Some (mkAction 7 DL (Some 9))
  | 9, 4 => Some (mkAction 1 DR None)
  | 9, 5 => Some (mkAction 5 DR (Some 1))
  | 9, 6 => Some (mkAction 7 DL (Some 9))
  | 9, 7 => Some (mkAction 6 DL (Some 6))
  | _, _ => None
  end.

Lemma bb108_valid : ValidTM 10 8 bb108.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 10 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 10 (destruct s as [| s]; [
      do 8 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb108_core : Fwp2_H7Core bb108.
Proof. constructor; [constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Definition H51 (m : nat) : nat := iter H7_H (2 * m - 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H7_H_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus 3 m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_minus_1 H7_H (f_omega2_plus 2) 1 ltac:(lia) H7_H_mono H7_H_inc H7_H_gt (fOmega2_props 1 0 2) m Hm).
Qed.

Lemma H51_inc : forall m, 1 <= m -> S m <= H51 m.
Proof.
  intros m Hm. pose proof (H51_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 3) m).
  change (f_omega2_plus 3 m) with (fOmega2 1 0 3 m) in *. lia.
Qed.

Lemma H51_ge_17 : forall m, 1 <= m -> 17 <= H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (iter_H_ge_17 H7_H (2 * m - 1) 1 ltac:(lia) ltac:(lia) H7_H_inc H7_H_ge_17).
Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb108 (Scfg (r + 2) 0 m (5 :: 1 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_51_4step bb108 9 5 6 2 4 5 (S r) m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hm) as [t0 H0].
  destruct (rule_7_H_rep bb108 bb108_core (2 * m - 1) r 1 (5 :: R) ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (r + 2) with (S (S r)) by lia.
  replace (r2 + 2) with (S (S r2)) by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | pose proof (Ht2 ltac:(lia)); lia]].
Qed.

Definition H5mid (m : nat) : nat := iter H51 (2 * m + 1) 1.

Lemma H5mid_mono : forall x y, x <= y -> H5mid x <= H5mid y.
Proof.
  intros x y Hxy. unfold H5mid.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H51_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H5mid_gt : forall m, 1 <= m -> f_omega2_plus 4 m < H5mid m.
Proof.
  intros m Hm. unfold H5mid.
  apply (climb_2m_plus_1 H51 (f_omega2_plus 3) 1 ltac:(lia) H51_mono H51_inc H51_gt (fOmega2_props 1 0 3) m Hm).
Qed.

Lemma H5mid_inc : forall m, 1 <= m -> S m <= H5mid m.
Proof.
  intros m Hm. pose proof (H5mid_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 4) m).
  change (f_omega2_plus 4 m) with (fOmega2 1 0 4 m) in *. lia.
Qed.

Lemma H5mid_ge_17 : forall m, 17 <= H5mid m.
Proof.
  intro m. unfold H5mid.
  apply (iter_H_ge_17 H51 (2 * m + 1) 1 ltac:(lia) ltac:(lia) H51_inc H51_ge_17).
Qed.

Lemma rule_5mid : forall r m R,
  exists r' m' t, Reaches bb108 (Scfg (r + 2) 0 m (5 :: 6 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t /\
    H5mid m <= m' /\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_5mark_empty bb108 5 (fh_fp _ (h6_fh _ (h7_h6 _ bb108_core))) (S r) m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [t0 H0].
  assert (Hpe : 1 <= Pempty (S r)) by (pose proof (Pempty_ge (S r)); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).
  destruct (iter_cursor_rep bb108 2 1 H51 H51_mono Hpos rule_51 (2 * m + 1) r (Pempty (S r)) R Hpe)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (S (S r)) with (r + 2) in H0 by lia.
  split; [eapply reaches_trans; eassumption | split].
  - unfold H5mid. eapply Nat.le_trans; [apply iter_mono_arg; [apply H51_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.

Lemma bb108_bootstrap :
  Reaches bb108 initConfig (Scfg 2 0 1 (5 :: rep 8 6 [])) 196.
Proof. vm_compute. reflexivity. Qed.

Theorem bb108_halts_gt_f_omega2_plus_5_7 :
  ValidTM 10 8 bb108 /\ exists t, HaltsIn bb108 initConfig t /\ f_omega2_plus 5 7 < t.
Proof.
  split; [exact bb108_valid |].
  pose proof bb108_bootstrap as Hboot.
  destruct (rule_5mid 0 1 (rep 7 6 [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : 7 <= m1) by (pose proof (H5mid_ge_17 1); lia).
  destruct (iter_cursor_rep0 bb108 2 6 H5mid H5mid_mono rule_5mid 7 r1 m1 [])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb108 5 (r2 + 2) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H5mid (f_omega2_plus 4) 1 H5mid_gt (fOmega2_props 1 0 4) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H5mid H5mid_mono 7 7 m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 5 7) with (iter (f_omega2_plus 4) 7 7). lia.
Qed.

Print Assumptions bb108_halts_gt_f_omega2_plus_5_7.
