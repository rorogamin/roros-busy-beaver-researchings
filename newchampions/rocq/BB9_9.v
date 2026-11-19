(*
  rocq/BB9_9.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(9, 9):
    TM: 8RH3LB2LH2RA4LB6RI6LH7LH8LH_1LF3RB1LD2RA3LF5RB3RC3RC3RC_3RB1LB3LC2RC4LC1LE2RA3RE3RD_3RB3RE3LC2RC6LD3RD3RB1RZ3RE_5RB3RE4RG4LC3LG5LE3LD3RF2RA_5RB5RB2RC1LF5LF5LF1RI2RA7RA_5LF4RG1LB1LG7LG5LG2LH6LD7LG_1RF1RZ1LH1LH2LH5RG1RZ1RZ1RZ_1RZ5LI8LI8LI8LE5RB8LI1RZ5RI
    Domain: BB(9, 9) (9 states, 9 symbols)
    Previous best dominated bounds: BB(8, 9) > f_{ω^2+4}(7), BB(9, 8) > f_{ω^2+4}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb99 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 8RH 3LB 2LH 2RA 4LB 6RI 6LH 7LH 8LH *)
  | 0, 0 => Some (mkAction 8 DR (Some 7))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 6 DR (Some 8))
  | 0, 6 => Some (mkAction 6 DL (Some 7))
  | 0, 7 => Some (mkAction 7 DL (Some 7))
  | 0, 8 => Some (mkAction 8 DL (Some 7))
  (* State B (1): 1LF 3RB 1LD 2RA 3LF 5RB 3RC 3RC 3RC *)
  | 1, 0 => Some (mkAction 1 DL (Some 5))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 3 DR (Some 2))
  | 1, 7 => Some (mkAction 3 DR (Some 2))
  | 1, 8 => Some (mkAction 3 DR (Some 2))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 2RA 3RE 3RD *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 2 DR (Some 0))
  | 2, 7 => Some (mkAction 3 DR (Some 4))
  | 2, 8 => Some (mkAction 3 DR (Some 3))
  (* State D (3): 3RB 3RE 3LC 2RC 6LD 3RD 3RB 1RZ 3RE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 6 DL (Some 3))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 3 DR (Some 1))
  | 3, 7 => Some (mkAction 1 DR None)
  | 3, 8 => Some (mkAction 3 DR (Some 4))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 3LD 3RF 2RA *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 3 DL (Some 3))
  | 4, 7 => Some (mkAction 3 DR (Some 5))
  | 4, 8 => Some (mkAction 2 DR (Some 0))
  (* State F (5): 5RB 5RB 2RC 1LF 5LF 5LF 1RI 2RA 7RA *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 2 DR (Some 2))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 1 DR (Some 8))
  | 5, 7 => Some (mkAction 2 DR (Some 0))
  | 5, 8 => Some (mkAction 7 DR (Some 0))
  (* State G (6): 5LF 4RG 1LB 1LG 7LG 5LG 2LH 6LD 7LG *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 7 DL (Some 6))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  | 6, 7 => Some (mkAction 6 DL (Some 3))
  | 6, 8 => Some (mkAction 7 DL (Some 6))
  (* State H (7): 1RF 1RZ 1LH 1LH 2LH 5RG 1RZ 1RZ 1RZ *)
  | 7, 0 => Some (mkAction 1 DR (Some 5))
  | 7, 1 => Some (mkAction 1 DR None)
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 1 DR None)
  | 7, 7 => Some (mkAction 1 DR None)
  | 7, 8 => Some (mkAction 1 DR None)
  (* State I (8): 1RZ 5LI 8LI 8LI 8LE 5RB 8LI 1RZ 5RI *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 5 DL (Some 8))
  | 8, 2 => Some (mkAction 8 DL (Some 8))
  | 8, 3 => Some (mkAction 8 DL (Some 8))
  | 8, 4 => Some (mkAction 8 DL (Some 4))
  | 8, 5 => Some (mkAction 5 DR (Some 1))
  | 8, 6 => Some (mkAction 8 DL (Some 8))
  | 8, 7 => Some (mkAction 1 DR None)
  | 8, 8 => Some (mkAction 5 DR (Some 8))
  | _, _ => None
  end.

Lemma bb99_valid : ValidTM 9 9 bb99.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 9 (destruct s as [| s]; [
      do 9 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 9 (destruct s as [| s]; [
      do 9 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb99_core : Fwp2_H8Core bb99.
Proof. constructor; [constructor; [constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Definition H51 (m : nat) : nat := iter H8_H (2 * m - 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H8_H_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus 4 m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_minus_1 H8_H (f_omega2_plus 3) 1 ltac:(lia) H8_H_mono H8_H_inc H8_H_gt (fOmega2_props 1 0 3) m Hm).
Qed.

Lemma H51_inc : forall m, 1 <= m -> S m <= H51 m.
Proof.
  intros m Hm. pose proof (H51_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 4) m).
  change (f_omega2_plus 4 m) with (fOmega2 1 0 4 m) in *. lia.
Qed.

Lemma H51_ge_17 : forall m, 1 <= m -> 17 <= H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (iter_H_ge_17 H8_H (2 * m - 1) 1 ltac:(lia) ltac:(lia) H8_H_inc H8_H_ge_17).
Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb99 (Scfg (r + 2) 0 m (5 :: 1 :: R)) (Scfg (r' + 2) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_51_4step bb99 8 5 7 2 3 4 (S r) m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hm) as [t0 H0].
  destruct (rule_8_H_rep bb99 bb99_core (2 * m - 1) r 1 (5 :: R) ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (r + 2) with (S (S r)) by lia.
  replace (r2 + 2) with (S (S r2)) by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | pose proof (Ht2 ltac:(lia)); lia]].
Qed.

Lemma bb99_bootstrap :
  Reaches bb99 initConfig (Scfg 3 0 1 (5 :: rep 8 1 [])) 138.
Proof. vm_compute. reflexivity. Qed.

Theorem bb99_halts_gt_f_omega2_plus_5_7 :
  ValidTM 9 9 bb99 /\ exists t, HaltsIn bb99 initConfig t /\ f_omega2_plus 5 7 < t.
Proof.
  split; [exact bb99_valid |].
  pose proof bb99_bootstrap as Hboot.
  destruct (rule_51 1 1 (rep 7 1 []) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : 7 <= m1) by (pose proof (H51_ge_17 1 ltac:(lia)); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).
  destruct (iter_cursor_rep bb99 2 1 H51 H51_mono Hpos rule_51 7 r1 m1 [] ltac:(lia))
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb99 5 (r2 + 2) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H51 (f_omega2_plus 4) 1 H51_gt (fOmega2_props 1 0 4) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H51 H51_mono 7 7 m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 5 7) with (iter (f_omega2_plus 4) 7 7). lia.
Qed.

Print Assumptions bb99_halts_gt_f_omega2_plus_5_7.
