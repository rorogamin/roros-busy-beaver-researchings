(*
  rocq/BB11_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(11, 7):
    TM: 2RK3LB2LH2RA4LB4RI6LH_6LJ3RB1LD2RA3LF5RB3RC_3RB1LB3LC2RC4LC1LE3RD_3RB3RE3LC2RC3RG3RD3RE_5RB3RE4RG4LC3LG5LE2RA_5RB1RJ2RA1LF5LF5LF5LH_5LF4RG1LB1LG2RF5LG2LH_2RD2RF1LH1LH2LH5RG6RF_1RZ5LJ1LI1LI1LI5RH4LK_1LA5LA6LJ6LJ6LJ5RB6RF_6LC5LH4LK4LK4LK5RD2LB
    Domain: BB(11, 7) (11 states, 7 symbols)
    Previous best dominated bounds: BB(10, 7) > f_{ω^2+4}(4), BB(11, 6) > f_{ω^2+4}(8)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+5}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb117 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2RK 3LB 2LH 2RA 4LB 4RI 6LH *)
  | 0, 0 => Some (mkAction 2 DR (Some 10))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 4 DR (Some 8))
  | 0, 6 => Some (mkAction 6 DL (Some 7))
  (* State B (1): 6LJ 3RB 1LD 2RA 3LF 5RB 3RC *)
  | 1, 0 => Some (mkAction 6 DL (Some 9))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 3))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DL (Some 5))
  | 1, 5 => Some (mkAction 5 DR (Some 1))
  | 1, 6 => Some (mkAction 3 DR (Some 2))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC 1LE 3RD *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 1 DL (Some 4))
  | 2, 6 => Some (mkAction 3 DR (Some 3))
  (* State D (3): 3RB 3RE 3LC 2RC 3RG 3RD 3RE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 3 DR (Some 6))
  | 3, 5 => Some (mkAction 3 DR (Some 3))
  | 3, 6 => Some (mkAction 3 DR (Some 4))
  (* State E (4): 5RB 3RE 4RG 4LC 3LG 5LE 2RA *)
  | 4, 0 => Some (mkAction 5 DR (Some 1))
  | 4, 1 => Some (mkAction 3 DR (Some 4))
  | 4, 2 => Some (mkAction 4 DR (Some 6))
  | 4, 3 => Some (mkAction 4 DL (Some 2))
  | 4, 4 => Some (mkAction 3 DL (Some 6))
  | 4, 5 => Some (mkAction 5 DL (Some 4))
  | 4, 6 => Some (mkAction 2 DR (Some 0))
  (* State F (5): 5RB 1RJ 2RA 1LF 5LF 5LF 5LH *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 1 DR (Some 9))
  | 5, 2 => Some (mkAction 2 DR (Some 0))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 5 DL (Some 7))
  (* State G (6): 5LF 4RG 1LB 1LG 2RF 5LG 2LH *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 2 DR (Some 5))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  (* State H (7): 2RD 2RF 1LH 1LH 2LH 5RG 6RF *)
  | 7, 0 => Some (mkAction 2 DR (Some 3))
  | 7, 1 => Some (mkAction 2 DR (Some 5))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 6 DR (Some 5))
  (* State I (8): 1RZ 5LJ 1LI 1LI 1LI 5RH 4LK *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 5 DL (Some 9))
  | 8, 2 => Some (mkAction 1 DL (Some 8))
  | 8, 3 => Some (mkAction 1 DL (Some 8))
  | 8, 4 => Some (mkAction 1 DL (Some 8))
  | 8, 5 => Some (mkAction 5 DR (Some 7))
  | 8, 6 => Some (mkAction 4 DL (Some 10))
  (* State J (9): 1LA 5LA 6LJ 6LJ 6LJ 5RB 6RF *)
  | 9, 0 => Some (mkAction 1 DL (Some 0))
  | 9, 1 => Some (mkAction 5 DL (Some 0))
  | 9, 2 => Some (mkAction 6 DL (Some 9))
  | 9, 3 => Some (mkAction 6 DL (Some 9))
  | 9, 4 => Some (mkAction 6 DL (Some 9))
  | 9, 5 => Some (mkAction 5 DR (Some 1))
  | 9, 6 => Some (mkAction 6 DR (Some 5))
  (* State K (10): 6LC 5LH 4LK 4LK 4LK 5RD 2LB *)
  | 10, 0 => Some (mkAction 6 DL (Some 2))
  | 10, 1 => Some (mkAction 5 DL (Some 7))
  | 10, 2 => Some (mkAction 4 DL (Some 10))
  | 10, 3 => Some (mkAction 4 DL (Some 10))
  | 10, 4 => Some (mkAction 4 DL (Some 10))
  | 10, 5 => Some (mkAction 5 DR (Some 3))
  | 10, 6 => Some (mkAction 2 DL (Some 1))
  | _, _ => None
  end.

Lemma bb117_valid : ValidTM 11 7 bb117.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 11 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 11 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb117_core : Fwp2_H6Core bb117.
Proof. constructor; [constructor; [constructor; [constructor; reflexivity | ..]; reflexivity | ..]; reflexivity | ..]; reflexivity. Qed.

Definition H51 (m : nat) : nat := iter H_plus2 (2 * m - 1) 1.

Lemma H51_mono : forall x y, x <= y -> H51 x <= H51 y.
Proof.
  intros x y Hxy. unfold H51.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H_plus2_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H51_gt : forall m, 1 <= m -> f_omega2_plus 2 m < H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (climb_2m_minus_1 H_plus2 (f_omega2_plus 1) 1 ltac:(lia) H_plus2_mono H_plus2_inc H_plus2_gt (fOmega2_props 1 0 1) m Hm).
Qed.

Lemma H51_inc : forall m, 1 <= m -> S m <= H51 m.
Proof.
  intros m Hm. pose proof (H51_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 2) m).
  change (f_omega2_plus 2 m) with (fOmega2 1 0 2 m) in *. lia.
Qed.

Lemma H51_ge_17 : forall m, 1 <= m -> 17 <= H51 m.
Proof.
  intros m Hm. unfold H51.
  apply (iter_H_ge_17 H_plus2 (2 * m - 1) 1 ltac:(lia) ltac:(lia) H_plus2_inc (fun z _ => H_plus2_ge_17 z)).
Qed.

Lemma rule_51 : forall r m R, 1 <= m ->
  exists r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_51_4step bb117 9 3 5 2 3 4 r m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hm) as [t0 H0].
  destruct (rule_6_H_rep bb117 bb117_core (2 * m - 1) r 1 (5 :: R) ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (r + 1) with (S r) by lia.
  replace (r2 + 1) with (S r2) by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | destruct (Ht2 ltac:(lia)) as [Ht2a _]; lia]].
Qed.

Definition H5mid (m : nat) : nat := iter H51 (2 * m + 1) 1.

Lemma H5mid_mono : forall x y, x <= y -> H5mid x <= H5mid y.
Proof.
  intros x y Hxy. unfold H5mid.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H51_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H5mid_gt : forall m, 1 <= m -> f_omega2_plus 3 m < H5mid m.
Proof.
  intros m Hm. unfold H5mid.
  apply (climb_2m_plus_1 H51 (f_omega2_plus 2) 1 ltac:(lia) H51_mono H51_inc H51_gt (fOmega2_props 1 0 2) m Hm).
Qed.

Lemma H5mid_inc : forall m, 1 <= m -> S m <= H5mid m.
Proof.
  intros m Hm. pose proof (H5mid_gt m Hm).
  pose proof (fgh_ge_self _ (fOmega2_props 1 0 3) m).
  change (f_omega2_plus 3 m) with (fOmega2 1 0 3 m) in *. lia.
Qed.

Lemma H5mid_ge_17 : forall m, 17 <= H5mid m.
Proof.
  intro m. unfold H5mid.
  apply (iter_H_ge_17 H51 (2 * m + 1) 1 ltac:(lia) ltac:(lia) H51_inc H51_ge_17).
Qed.

Lemma rule_5mid : forall r m R,
  exists r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 4 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H5mid m <= m' /\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_5mark_empty bb117 3 (fh_fp _ (h6_fh _ bb117_core)) r m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [t0 H0].
  assert (Hpe : 1 <= Pempty r) by (pose proof (Pempty_ge r); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).
  destruct (iter_cursor_rep bb117 1 1 H51 H51_mono Hpos rule_51 (2 * m + 1) r (Pempty r) R Hpe)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (S r) with (r + 1) in H0 by lia.
  split; [eapply reaches_trans; eassumption | split].
  - unfold H5mid. eapply Nat.le_trans; [apply iter_mono_arg; [apply H51_mono | exact Hpe] | exact Hm2].
  - pose proof (Ht2 ltac:(lia)). lia.
Qed.

Definition H5top (m : nat) : nat := iter H5mid (2 * m + 1) 0.

Lemma H5top_mono : forall x y, x <= y -> H5top x <= H5top y.
Proof.
  intros x y Hxy. unfold H5top.
  apply iter_mono_steps; [intro z; destruct z; [lia | pose proof (H5mid_inc (S z) ltac:(lia)); lia] | lia].
Qed.

Lemma H5top_gt : forall m, 1 <= m -> f_omega2_plus 4 m < H5top m.
Proof.
  intros m Hm. unfold H5top.
  rewrite iter_add, iter_succ, iter_zero.
  assert (H0 : 1 <= H5mid 0) by (pose proof (H5mid_ge_17 0); lia).
  pose proof (climb_double H5mid (f_omega2_plus 3) 1 ltac:(lia) H5mid_mono H5mid_inc H5mid_gt (fOmega2_props 1 0 3) m Hm) as H1.
  pose proof (iter_mono_arg H5mid H5mid_mono (2 * m) 1 (H5mid 0) H0) as H2.
  change (f_omega2_plus 4 m) with (fNext (f_omega2_plus 3) m). lia.
Qed.

Lemma H5top_ge_17 : forall m, 17 <= H5top m.
Proof.
  intro m. unfold H5top.
  replace (2 * m + 1) with (S (2 * m)) by lia. rewrite iter_succ. apply H5mid_ge_17.
Qed.

Lemma rule_5top : forall r m R,
  exists r' m' t, Reaches bb117 (Scfg (r + 1) 0 m (5 :: 6 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H5top m <= m' /\ m' <= t.
Proof.
  intros r m R.
  destruct (reload_5top_zero bb117 3 6 3 6 5 r m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [t0 H0].
  destruct (iter_cursor_rep0 bb117 1 4 H5mid H5mid_mono rule_5mid (2 * m + 1) r 0 R)
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (S r) with (r + 1) in H0 by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | pose proof (Ht2 ltac:(lia)); lia]].
Qed.

Lemma bb117_bootstrap :
  Reaches bb117 initConfig (Scfg 1 0 1 (5 :: rep 8 6 [])) 57.
Proof. vm_compute. reflexivity. Qed.

Theorem bb117_halts_gt_f_omega2_plus_5_7 :
  ValidTM 11 7 bb117 /\ exists t, HaltsIn bb117 initConfig t /\ f_omega2_plus 5 7 < t.
Proof.
  split; [exact bb117_valid |].
  pose proof bb117_bootstrap as Hboot.
  destruct (rule_5top 0 1 (rep 7 6 [])) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : 7 <= m1) by (pose proof (H5top_ge_17 1); lia).
  destruct (iter_cursor_rep0 bb117 1 6 H5top H5top_mono rule_5top 7 r1 m1 [])
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb117 3 (r2 + 1) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H5top (f_omega2_plus 4) 1 H5top_gt (fOmega2_props 1 0 4) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H5top H5top_mono 7 7 m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 5 7) with (iter (f_omega2_plus 4) 7 7). lia.
Qed.

Print Assumptions bb117_halts_gt_f_omega2_plus_5_7.
