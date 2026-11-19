(*
  rocq/BB9_7.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(9, 7):
    TM: 2RH3LB2LH2RA4LB4RI6LH_1LH3RB1LD2RA3LF5RB3RC_3RB1LB3LC2RC4LC1LE3RD_3RB3RE3LC2RC3LC3RD3RE_5RB3RE4RG4LC3LG5LE2RA_5RB5RB6RD1LF5LF5LF6RE_5LF4RG1LB1LG6RI5LG2LH_1LF6RC1LH1LH2LH5RG5LE_1RZ5LI6LI6LI6LI5RB1RZ
    Domain: BB(9, 7) (9 states, 7 symbols)
    Previous best dominated bounds: BB(8, 7) > f_{ω^2+2}(8), BB(9, 6) > f_{ω^2+2}(7)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω^2+3}(7)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz Fwp2 Fwp2_H Fwp2_H8.
Import ListNotations.

Definition bb97 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2RH 3LB 2LH 2RA 4LB 4RI 6LH *)
  | 0, 0 => Some (mkAction 2 DR (Some 7))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 2 DL (Some 7))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 4 DR (Some 8))
  | 0, 6 => Some (mkAction 6 DL (Some 7))
  (* State B (1): 1LH 3RB 1LD 2RA 3LF 5RB 3RC *)
  | 1, 0 => Some (mkAction 1 DL (Some 7))
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
  (* State D (3): 3RB 3RE 3LC 2RC 3LC 3RD 3RE *)
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 1 => Some (mkAction 3 DR (Some 4))
  | 3, 2 => Some (mkAction 3 DL (Some 2))
  | 3, 3 => Some (mkAction 2 DR (Some 2))
  | 3, 4 => Some (mkAction 3 DL (Some 2))
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
  (* State F (5): 5RB 5RB 6RD 1LF 5LF 5LF 6RE *)
  | 5, 0 => Some (mkAction 5 DR (Some 1))
  | 5, 1 => Some (mkAction 5 DR (Some 1))
  | 5, 2 => Some (mkAction 6 DR (Some 3))
  | 5, 3 => Some (mkAction 1 DL (Some 5))
  | 5, 4 => Some (mkAction 5 DL (Some 5))
  | 5, 5 => Some (mkAction 5 DL (Some 5))
  | 5, 6 => Some (mkAction 6 DR (Some 4))
  (* State G (6): 5LF 4RG 1LB 1LG 6RI 5LG 2LH *)
  | 6, 0 => Some (mkAction 5 DL (Some 5))
  | 6, 1 => Some (mkAction 4 DR (Some 6))
  | 6, 2 => Some (mkAction 1 DL (Some 1))
  | 6, 3 => Some (mkAction 1 DL (Some 6))
  | 6, 4 => Some (mkAction 6 DR (Some 8))
  | 6, 5 => Some (mkAction 5 DL (Some 6))
  | 6, 6 => Some (mkAction 2 DL (Some 7))
  (* State H (7): 1LF 6RC 1LH 1LH 2LH 5RG 5LE *)
  | 7, 0 => Some (mkAction 1 DL (Some 5))
  | 7, 1 => Some (mkAction 6 DR (Some 2))
  | 7, 2 => Some (mkAction 1 DL (Some 7))
  | 7, 3 => Some (mkAction 1 DL (Some 7))
  | 7, 4 => Some (mkAction 2 DL (Some 7))
  | 7, 5 => Some (mkAction 5 DR (Some 6))
  | 7, 6 => Some (mkAction 5 DL (Some 4))
  (* State I (8): 1RZ 5LI 6LI 6LI 6LI 5RB 1RZ *)
  | 8, 0 => Some (mkAction 1 DR None)
  | 8, 1 => Some (mkAction 5 DL (Some 8))
  | 8, 2 => Some (mkAction 6 DL (Some 8))
  | 8, 3 => Some (mkAction 6 DL (Some 8))
  | 8, 4 => Some (mkAction 6 DL (Some 8))
  | 8, 5 => Some (mkAction 5 DR (Some 1))
  | 8, 6 => Some (mkAction 1 DR None)
  | _, _ => None
  end.

Lemma bb97_valid : ValidTM 9 7 bb97.
Proof.
  split.
  - intros s sym Hs Hsym.
    do 9 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia
    |]); lia.
  - intros s sym H.
    do 9 (destruct s as [| s]; [
      do 7 (destruct sym as [| sym]; [lia |]); reflexivity
    |]); reflexivity.
Qed.

Lemma bb97_core : Fwp2_H6Core bb97.
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
  exists r' m' t, Reaches bb97 (Scfg (r + 1) 0 m (5 :: 1 :: R)) (Scfg (r' + 1) 0 m' (5 :: R)) t /\
    H51 m <= m' /\ m' <= t.
Proof.
  intros r m R Hm.
  destruct (reload_51_4step bb97 8 3 5 2 3 4 r m R
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hm) as [t0 H0].
  destruct (rule_6_H_rep bb97 bb97_core (2 * m - 1) r 1 (5 :: R) ltac:(lia)) as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  exists r2, m2, (t0 + t2).
  replace (r + 1) with (S r) by lia.
  replace (r2 + 1) with (S r2) by lia.
  split; [eapply reaches_trans; eassumption | split; [exact Hm2 | destruct (Ht2 ltac:(lia)) as [Ht2a _]; lia]].
Qed.

Lemma bb97_bootstrap :
  Reaches bb97 initConfig (Scfg 1 0 1 (5 :: rep 8 1 [])) 76.
Proof. vm_compute. reflexivity. Qed.

Theorem bb97_halts_gt_f_omega2_plus_3_7 :
  ValidTM 9 7 bb97 /\ exists t, HaltsIn bb97 initConfig t /\ f_omega2_plus 3 7 < t.
Proof.
  split; [exact bb97_valid |].
  pose proof bb97_bootstrap as Hboot.
  destruct (rule_51 0 1 (rep 7 1 []) ltac:(lia)) as [r1 [m1 [t1 [H1 [Hm1 _]]]]].
  assert (Hm1_k : 7 <= m1) by (pose proof (H51_ge_17 1 ltac:(lia)); lia).
  assert (Hpos : forall x, 1 <= x -> 1 <= H51 x) by (intros x Hx; pose proof (H51_ge_17 x Hx); lia).
  destruct (iter_cursor_rep bb97 1 1 H51 H51_mono Hpos rule_51 7 r1 m1 [] ltac:(lia))
    as [r2 [m2 [t2 [H2 [Hm2 Ht2]]]]].
  destruct (halt_cursor_5 bb97 3 (r2 + 1) m2 eq_refl eq_refl) as [cf [Hhalt Hst]].
  pose proof (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ (reaches_trans _ _ _ _ _ _ Hboot H1) H2) Hhalt) as Hreach.
  pose proof (iter_strict_dom H51 (f_omega2_plus 2) 1 H51_gt (fOmega2_props 1 0 2) 7 7 ltac:(lia) ltac:(lia)) as Hlt1.
  pose proof (iter_mono_arg H51 H51_mono 7 7 m1 Hm1_k) as Hlt2.
  pose proof (Ht2 ltac:(lia)) as Hlet.
  eexists. split; [eexists; split; [exact Hreach | exact Hst] |].
  change (f_omega2_plus 3 7) with (iter (f_omega2_plus 2) 7 7). lia.
Qed.

Print Assumptions bb97_halts_gt_f_omega2_plus_3_7.
