(*
  rocq/BB7_5.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(7, 5):
    TM: 1LF3LB4LC2RA4LB_2RF3RB1LC2RA2RD_3RB1LB3LC2RC4LC_1RZ4LD1LE2RD2RD_3RF1LD3LE2RE3LF_1LG3RF4LE2RD4LC_2LC2RB3LG2RG0LA
    Domain: BB(7, 5) (7 states, 5 symbols)
    Previous live wiki record: BB(7, 5) > f_{ω×2}(2 ↑^{12} 5)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω×2}(f_ω(14))
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Definition bb75 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 1LF 3LB 4LC 2RA 4LB *)
  | 0, 0 => Some (mkAction 1 DL (Some 5))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 4 DL (Some 2))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  (* State B (1): 2RF 3RB 1LC 2RA 2RD *)
  | 1, 0 => Some (mkAction 2 DR (Some 5))
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 2))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 2 DR (Some 3))
  (* State C (2): 3RB 1LB 3LC 2RC 4LC *)
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  (* State D (3): 1RZ 4LD 1LE 2RD 2RD *)
  | 3, 0 => Some (mkAction 1 DR None)
  | 3, 1 => Some (mkAction 4 DL (Some 3))
  | 3, 2 => Some (mkAction 1 DL (Some 4))
  | 3, 3 => Some (mkAction 2 DR (Some 3))
  | 3, 4 => Some (mkAction 2 DR (Some 3))
  (* State E (4): 3RF 1LD 3LE 2RE 3LF *)
  | 4, 0 => Some (mkAction 3 DR (Some 5))
  | 4, 1 => Some (mkAction 1 DL (Some 3))
  | 4, 2 => Some (mkAction 3 DL (Some 4))
  | 4, 3 => Some (mkAction 2 DR (Some 4))
  | 4, 4 => Some (mkAction 3 DL (Some 5))
  (* State F (5): 1LG 3RF 4LE 2RD 4LC *)
  | 5, 0 => Some (mkAction 1 DL (Some 6))
  | 5, 1 => Some (mkAction 3 DR (Some 5))
  | 5, 2 => Some (mkAction 4 DL (Some 4))
  | 5, 3 => Some (mkAction 2 DR (Some 3))
  | 5, 4 => Some (mkAction 4 DL (Some 2))
  (* State G (6): 2LC 2RB 3LG 2RG 0LA *)
  | 6, 0 => Some (mkAction 2 DL (Some 2))
  | 6, 1 => Some (mkAction 2 DR (Some 1))
  | 6, 2 => Some (mkAction 3 DL (Some 6))
  | 6, 3 => Some (mkAction 2 DR (Some 6))
  | 6, 4 => Some (mkAction 0 DL (Some 0))
  | _, _ => None
  end.

Lemma bb75_valid : ValidTM 7 5 bb75.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|s]]]]]]]; try lia;
    destruct sym as [|[|[|[|[|sym]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|s]]]]]]];
    try (destruct sym as [|[|[|[|[|sym]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb75_kropitz : KropitzCore bb75 2.
Proof. constructor; reflexivity. Qed.

(* Basic right/left sweep loops *)

Lemma loop_D3_R : forall n L R,
  Reaches bb75 (mkCfgR (Some 3) L (rep n 3 R))
               (mkCfgR (Some 3) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb75 3 1 (Some 3) L 3 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_E2_L : forall n L R,
  Reaches bb75 (mkCfgR (Some 4) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 4) L (2 :: rep n 3 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 4 2 2 2 (Some 4) _ _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_E3_R : forall n L R,
  Reaches bb75 (mkCfgR (Some 4) L (rep n 3 R))
               (mkCfgR (Some 4) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb75 4 1 (Some 4) L 3 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_F1_R : forall n L R,
  Reaches bb75 (mkCfgR (Some 5) L (rep n 1 R))
               (mkCfgR (Some 5) (rep n 3 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb75 5 2 (Some 5) L 1 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_B1_R : forall n L R,
  Reaches bb75 (mkCfgR (Some 1) L (rep n 1 R))
               (mkCfgR (Some 1) (rep n 3 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb75 1 2 (Some 1) L 1 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_A3_R : forall n L R,
  Reaches bb75 (mkCfgR (Some 0) L (rep n 3 R))
               (mkCfgR (Some 0) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb75 0 1 (Some 0) L 3 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

(* Sweep C2-1: 3^n 2^k C> 2 1^(j+1) R -> 2^k C> 2 1^(j+1+n) R *)
Lemma sweep_C2_1 : forall n k j R,
  exists t, Reaches bb75
    (mkCfgR (Some 2) (rep k 2 (rep n 3 [])) (2 :: rep (S j) 1 R))
    (mkCfgR (Some 2) (rep k 2 []) (2 :: rep (S j + n) 1 R)) t.
Proof.
  induction n as [| n' IH]; intros k j R.
  - exists 0. replace (S j + 0) with (S j) by lia. apply reaches_zero.
  - assert (Hstep : Reaches bb75
      (mkCfgR (Some 2) (rep k 2 (3 :: rep n' 3 [])) (2 :: 1 :: rep j 1 R))
      (mkCfgR (Some 2) (rep k 2 (rep n' 3 [])) (2 :: 1 :: 1 :: rep j 1 R))
      (k + 1 + (k + 2) + 2)).
    { eapply reaches_trans; [eapply reaches_trans |].
      - eapply reaches_trans; [apply (loop_C2 bb75 2 bb75_kropitz k (3 :: rep n' 3 []) (1 :: rep j 1 R)) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 2 2 3 2 (Some 2) _ _ eq_refl).
      - replace (3 :: 3 :: rep k 3 (1 :: rep j 1 R)) with (rep (k + 2) 3 (1 :: rep j 1 R))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        apply (loop_C3 bb75 2 bb75_kropitz (k + 2) (rep n' 3 []) (1 :: rep j 1 R)).
      - replace (rep (k + 2) 2 (rep n' 3 [])) with (2 :: 2 :: rep k 2 (rep n' 3 []))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 2 0 2 1 (Some 1) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 1 0 2 2 (Some 2) _ _ eq_refl). }
    destruct (IH k (S j) R) as [t2 H2].
    replace (S j + S n') with (S (S j) + n') by lia.
    exists (k + 1 + (k + 2) + 2 + t2).
    eapply reaches_trans; [exact Hstep | exact H2].
Qed.

(* Sweep E2-1: 3^n 2^k E> 2 1^(j+1) R -> 2^k E> 2 1^(j+1+n) R *)
Lemma sweep_E2_1 : forall n k j R,
  exists t, Reaches bb75
    (mkCfgR (Some 4) (rep k 2 (rep n 3 [])) (2 :: rep (S j) 1 R))
    (mkCfgR (Some 4) (rep k 2 []) (2 :: rep (S j + n) 1 R)) t.
Proof.
  induction n as [| n' IH]; intros k j R.
  - exists 0. replace (S j + 0) with (S j) by lia. apply reaches_zero.
  - assert (Hstep : Reaches bb75
      (mkCfgR (Some 4) (rep k 2 (3 :: rep n' 3 [])) (2 :: 1 :: rep j 1 R))
      (mkCfgR (Some 4) (rep k 2 (rep n' 3 [])) (2 :: 1 :: 1 :: rep j 1 R))
      (k + 1 + (k + 2) + 2)).
    { eapply reaches_trans; [eapply reaches_trans |].
      - eapply reaches_trans; [apply (loop_E2_L k (3 :: rep n' 3 []) (1 :: rep j 1 R)) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 4 2 3 2 (Some 4) _ _ eq_refl).
      - replace (3 :: 3 :: rep k 3 (1 :: rep j 1 R)) with (rep (k + 2) 3 (1 :: rep j 1 R))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        apply (loop_E3_R (k + 2) (rep n' 3 []) (1 :: rep j 1 R)).
      - replace (rep (k + 2) 2 (rep n' 3 [])) with (2 :: 2 :: rep k 2 (rep n' 3 []))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 4 0 2 1 (Some 3) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 3 0 2 2 (Some 4) _ _ eq_refl). }
    destruct (IH k (S j) R) as [t2 H2].
    replace (S j + S n') with (S (S j) + n') by lia.
    exists (k + 1 + (k + 2) + 2 + t2).
    eapply reaches_trans; [exact Hstep | exact H2].
Qed.

(* Sweep E2-4: 3^n 2^k E> 2 4 3^j R -> 2^k E> 2 4 3^(j+n) R *)
Lemma sweep_E2_4 : forall n k j R,
  exists t, Reaches bb75
    (mkCfgR (Some 4) (rep k 2 (rep n 3 [])) (2 :: 4 :: rep j 3 R))
    (mkCfgR (Some 4) (rep k 2 []) (2 :: 4 :: rep (j + n) 3 R)) t.
Proof.
  induction n as [| n' IH]; intros k j R.
  - exists 0. replace (j + 0) with j by lia. apply reaches_zero.
  - assert (Hstep : Reaches bb75
      (mkCfgR (Some 4) (rep k 2 (3 :: rep n' 3 [])) (2 :: 4 :: rep j 3 R))
      (mkCfgR (Some 4) (rep k 2 (rep n' 3 [])) (2 :: 4 :: 3 :: rep j 3 R))
      (k + 1 + (k + 2) + 2)).
    { eapply reaches_trans; [eapply reaches_trans |].
      - eapply reaches_trans; [apply (loop_E2_L k (3 :: rep n' 3 []) (4 :: rep j 3 R)) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 4 2 3 2 (Some 4) _ _ eq_refl).
      - replace (3 :: 3 :: rep k 3 (4 :: rep j 3 R)) with (rep (k + 2) 3 (4 :: rep j 3 R))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        apply (loop_E3_R (k + 2) (rep n' 3 []) (4 :: rep j 3 R)).
      - replace (rep (k + 2) 2 (rep n' 3 [])) with (2 :: 2 :: rep k 2 (rep n' 3 []))
          by (replace (k + 2) with (S (S k)) by lia; reflexivity).
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 4 2 2 4 (Some 5) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 5 3 2 2 (Some 4) _ _ eq_refl). }
    destruct (IH k (S j) R) as [t2 H2].
    replace (j + S n') with (S j + n') by lia.
    exists (k + 1 + (k + 2) + 2 + t2).
    eapply reaches_trans; [exact Hstep | exact H2].
Qed.

(* A4 step: Bcfg (S k) m (4 :: R) -> Bcfg k 0 (rep (2*m+2) 1 (4 :: R)) *)
Lemma rule_A4_step : forall m k R,
  exists t, Reaches bb75
    (Bcfg (S k) m (4 :: R))
    (Bcfg k 0 (rep (2 * m + 2) 1 (4 :: R))) t.
Proof.
  intros m k R. unfold Bcfg.
  assert (H1 : Reaches bb75
    (mkCfgR (Some 0) (2 :: 2 :: rep k 2 (rep (2 * m + 1) 3 [])) (4 :: R))
    (mkCfgR (Some 2) (rep k 2 (rep (2 * m + 1) 3 [])) (2 :: 1 :: 4 :: R)) 2).
  { eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 0 3 2 4 (Some 1) _ _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_cons bb75 1 0 2 2 (Some 2) _ _ eq_refl). }
  destruct (sweep_C2_1 (2 * m + 1) k 0 (4 :: R)) as [t2 H2].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 2) (rep k 2 []) (2 :: rep (2 * m + 2) 1 (4 :: R)))
    (mkCfgR (Some 0) (rep (S k) 2 [3]) (rep (2 * m + 2) 1 (4 :: R)))
    (k + 1 + 1 + 1 + k)).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
    - eapply reaches_trans; [apply (loop_C2 bb75 2 bb75_kropitz k [] (rep (2 * m + 2) 1 (4 :: R))) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 2 2 2 (Some 2) _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 2 2 (Some 1) [] 0 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 1 1 (Some 0) [3] 3 _ eq_refl).
    - replace (rep (S k) 2 [3]) with (rep k 2 [2; 3])
        by (replace (S k) with (k + 1) by lia; rewrite rep_add; reflexivity).
      apply (loop_A3_R k [2; 3] (rep (2 * m + 2) 1 (4 :: R))). }
  replace (1 + (2 * m + 1)) with (2 * m + 2) in H2 by lia.
  exists (2 + t2 + (k + 1 + 1 + 1 + k)).
  eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
Qed.

(* A4 base: Bcfg 0 m (4 :: R) -> 3^(2m+3) 2^1 D> R *)
Lemma rule_A4_base : forall m R,
  exists t, Reaches bb75
    (Bcfg 0 m (4 :: R))
    (mkCfgR (Some 3) (2 :: rep (2 * m + 3) 3 []) R) t /\ 2 * m + 3 <= t.
Proof.
  intros m R. unfold Bcfg.
  assert (Hloop : forall n j R0,
    exists t, Reaches bb75
      (mkCfgR (Some 2) (rep n 3 []) (3 :: rep (S j) 1 R0))
      (mkCfgR (Some 2) [] (0 :: rep (S j + n + 1) 1 R0)) t).
  { induction n as [| n' IH]; intros j R0.
    - replace (S j + 0 + 1) with (S (S j)) by lia. simpl. exists 3.
      eapply steps_succ; [apply (step_mkCfgR_R bb75 2 1 (Some 2) [] 3 _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 2 0 2 1 (Some 1) _ _ eq_refl) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 1 0 2 (Some 2) _ eq_refl).
    - assert (Hs : Reaches bb75
        (mkCfgR (Some 2) (3 :: rep n' 3 []) (3 :: 1 :: rep j 1 R0))
        (mkCfgR (Some 2) (rep n' 3 []) (3 :: 1 :: 1 :: rep j 1 R0)) 3).
      { eapply steps_succ; [apply (step_mkCfgR_R bb75 2 1 (Some 2) _ 3 _ eq_refl) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 2 0 2 1 (Some 1) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 1 0 3 2 (Some 2) _ _ eq_refl). }
      destruct (IH (S j) R0) as [t2 H2].
      replace (S j + S n' + 1) with (S (S j) + n' + 1) by lia.
      exists (3 + t2). eapply reaches_trans; [exact Hs | exact H2]. }
  assert (H1 : Reaches bb75
    (mkCfgR (Some 0) (2 :: rep (2 * m + 1) 3 []) (4 :: R))
    (mkCfgR (Some 2) (rep (2 * m) 3 []) (3 :: 1 :: 4 :: R)) 2).
  { replace (2 * m + 1) with (S (2 * m)) by lia. simpl.
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 0 3 2 4 (Some 1) _ _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_cons bb75 1 0 3 2 (Some 2) _ _ eq_refl). }
  destruct (Hloop (2 * m) 0 (4 :: R)) as [t2 H2].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 2) [] (0 :: rep (2 * m + 2) 1 (4 :: R)))
    (mkCfgR (Some 3) (2 :: rep (2 * m + 3) 3 []) R) (1 + (2 * m + 2) + 1)).
  { eapply reaches_trans; [eapply reaches_trans |].
    - apply steps_one. apply (step_mkCfgR_R bb75 2 2 (Some 1) [] 0 _ eq_refl).
    - apply (loop_B1_R (2 * m + 2) [3] (4 :: R)).
    - replace (rep (2 * m + 2) 3 [3]) with (rep (2 * m + 3) 3 [])
        by (replace (2 * m + 3) with ((2 * m + 2) + 1) by lia; rewrite rep_add; reflexivity).
      apply steps_one. apply (step_mkCfgR_R bb75 1 1 (Some 3) _ 4 _ eq_refl). }
  replace (1 + 2 * m + 1) with (2 * m + 2) in H2 by lia.
  exists (2 + t2 + (1 + (2 * m + 2) + 1)).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | lia].
Qed.

(* Full A4 recursion: W5 k m *)
Fixpoint W5 (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => m + 1
  | S k' => fun m => W5 k' (iter (Kfn k') (2 * m + 2) 0)
  end.

Lemma W5_ge : forall k m, m + 1 <= W5 k m.
Proof.
  induction k as [| k' IH]; intro m; [simpl; lia |].
  change (m + 1 <= W5 k' (iter (Kfn k') (2 * m + 2) 0)).
  pose proof (IH (iter (Kfn k') (2 * m + 2) 0)).
  assert (Hge : 2 * m + 2 <= iter (Kfn k') (2 * m + 2) 0).
  { clear IH H. induction (2 * m + 2) as [| n IHn]; [simpl; lia |].
    simpl. pose proof (Kfn_ge_succ k' (iter (Kfn k') n 0)). lia. }
  lia.
Qed.

Lemma W5_gt_f_omega : forall m, f_omega m < 2 * W5 (m + 1) 0 + 1.
Proof.
  intro m.
  assert (H1 : Kfn m (Kfn m 0) <= W5 (m + 1) 0).
  { replace (m + 1) with (S m) by lia. simpl.
    pose proof (W5_ge m (Kfn m (Kfn m 0))). lia. }
  assert (H2 : m <= Kfn m 0) by (pose proof (Kfn_zero_ge m); lia).
  assert (H3 : Kfn m m <= Kfn m (Kfn m 0)) by (apply Kfn_mono; exact H2).
  assert (H4 : fFin m m <= Kfn m m) by (apply Kfn_ge_fFin).
  change (fFin m m < 2 * W5 (m + 1) 0 + 1). lia.
Qed.

Lemma rule_A4_full : forall k m R,
  exists t, Reaches bb75 (Bcfg k m (4 :: R))
    (mkCfgR (Some 3) (2 :: rep (2 * W5 k m + 1) 3 []) R) t /\ 2 * W5 k m + 1 <= t.
Proof.
  induction k as [| k' IH]; intros m R.
  - change (W5 0 m) with (m + 1). replace (2 * (m + 1) + 1) with (2 * m + 3) by lia.
    destruct (rule_A4_base m R) as [t [Ht Hle]]. exists t. split; [exact Ht | lia].
  - destruct (rule_A4_step m k' R) as [t1 H1].
    destruct (kropitz_rep bb75 2 bb75_kropitz k' (2 * m + 2) 0 (4 :: R)) as [t2 H2].
    destruct (IH (iter (Kfn k') (2 * m + 2) 0) R) as [t3 [H3 Hle3]].
    exists (t1 + t2 + t3).
    split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | change (W5 (S k') m) with (W5 k' (iter (Kfn k') (2 * m + 2) 0)); lia].
Qed.

(* F4 -> A4: 3^(m+2) F> 4 R -> Bcfg (m+1) 0 (4 :: R) -> 3^(2*W5 (m+1) 0 + 1) 2^1 D> R *)
Lemma rule_F4 : forall m R,
  exists t, Reaches bb75
    (mkCfgR (Some 5) (rep (m + 2) 3 []) (4 :: R))
    (mkCfgR (Some 3) (2 :: rep (2 * W5 (m + 1) 0 + 1) 3 []) R) t /\ 2 * W5 (m + 1) 0 + 1 <= t.
Proof.
  intros m R.
  assert (Hloop : forall n j R0,
    exists t, Reaches bb75
      (mkCfgR (Some 2) (rep n 3 []) (rep (S j) 3 (4 :: R0)))
      (mkCfgR (Some 2) [] (rep (S j + n) 3 (4 :: R0))) t).
  { induction n as [| n' IH]; intros j R0.
    - exists 0. replace (S j + 0) with (S j) by lia. apply reaches_zero.
    - assert (Hs : Reaches bb75
        (mkCfgR (Some 2) (3 :: rep n' 3 []) (rep (S j) 3 (4 :: R0)))
        (mkCfgR (Some 2) (rep n' 3 []) (rep (S (S j)) 3 (4 :: R0)))
        (S j + 1 + j + 1)).
      { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
        - apply (loop_C3 bb75 2 bb75_kropitz (S j) (3 :: rep n' 3 []) (4 :: R0)).
        - simpl. apply steps_one. apply (step_mkCfgR_L_cons bb75 2 3 2 4 (Some 2) _ _ eq_refl).
        - apply (loop_C2 bb75 2 bb75_kropitz j (3 :: rep n' 3 []) (4 :: R0)).
        - apply steps_one. apply (step_mkCfgR_L_cons bb75 2 2 3 2 (Some 2) _ _ eq_refl). }
      destruct (IH (S j) R0) as [t2 H2].
      replace (S j + S n') with (S (S j) + n') by lia.
      exists (S j + 1 + j + 1 + t2). eapply reaches_trans; [exact Hs | exact H2]. }
  assert (H1 : Reaches bb75
    (mkCfgR (Some 5) (rep (m + 2) 3 []) (4 :: R))
    (mkCfgR (Some 2) (rep (m + 1) 3 []) (3 :: 4 :: R)) 1).
  { replace (m + 2) with (S (m + 1)) by lia. simpl.
    apply steps_one. apply (step_mkCfgR_L_cons bb75 5 3 3 4 (Some 2) _ _ eq_refl). }
  destruct (Hloop (m + 1) 0 R) as [t2 H2].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 2) [] (rep (m + 2) 3 (4 :: R)))
    (Bcfg (m + 1) 0 (4 :: R))
    ((m + 2) + 1 + (m + 1) + 1 + 1 + 1 + (m + 1))).
  { unfold Bcfg.
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|].
    - apply (loop_C3 bb75 2 bb75_kropitz (m + 2) [] (4 :: R)).
    - replace (m + 2) with (S (m + 1)) by lia. simpl.
      apply steps_one. apply (step_mkCfgR_L_cons bb75 2 3 2 4 (Some 2) _ _ eq_refl).
    - apply (loop_C2 bb75 2 bb75_kropitz (m + 1) [] (4 :: R)).
    - apply steps_one. apply (step_mkCfgR_L_nil bb75 2 2 2 (Some 2) _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 2 2 (Some 1) [] 0 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 1 1 (Some 0) [3] 3 _ eq_refl).
    - change (rep (2 * 0 + 1) 3 []) with [3].
      replace (rep (S (m + 1)) 2 [3]) with (rep (m + 1) 2 [2; 3])
        by (replace (S (m + 1)) with ((m + 1) + 1) by lia; rewrite (rep_add (m + 1) 1); reflexivity).
      apply (loop_A3_R (m + 1) [2; 3] (4 :: R)). }
  replace (1 + (m + 1)) with (m + 2) in H2 by lia.
  destruct (rule_A4_full (m + 1) 0 R) as [t4 [H4 Hle4]].
  exists (1 + t2 + ((m + 2) + 1 + (m + 1) + 1 + 1 + 1 + (m + 1)) + t4).
  split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | lia].
Qed.

(* D1 rules: Dcfg k m R := 3^m 2^(k+1) D> R *)
Definition Dcfg5 (k m : nat) (R : list nat) : Config :=
  mkCfgR (Some 3) (rep (S k) 2 (rep m 3 [])) R.

Lemma rule_D1_base : forall m R,
  exists t, Reaches bb75 (Dcfg5 0 m (1 :: R)) (Dcfg5 0 (2 * W5 (m + 1) 0 + 1) R) t /\
            2 * W5 (m + 1) 0 + 1 <= t.
Proof.
  intros m R. unfold Dcfg5.
  assert (Hloop : forall n j R0,
    exists t, Reaches bb75
      (mkCfgR (Some 4) (rep n 3 []) (3 :: rep (S j) 1 R0))
      (mkCfgR (Some 4) [] (0 :: rep (S j + n + 1) 1 R0)) t).
  { induction n as [| n' IH]; intros j R0.
    - replace (S j + 0 + 1) with (S (S j)) by lia. simpl. exists 3.
      eapply steps_succ; [apply (step_mkCfgR_R bb75 4 1 (Some 4) [] 3 _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 4 0 2 1 (Some 3) _ _ eq_refl) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 3 0 2 (Some 4) _ eq_refl).
    - assert (Hs : Reaches bb75
        (mkCfgR (Some 4) (3 :: rep n' 3 []) (3 :: 1 :: rep j 1 R0))
        (mkCfgR (Some 4) (rep n' 3 []) (3 :: 1 :: 1 :: rep j 1 R0)) 3).
      { eapply steps_succ; [apply (step_mkCfgR_R bb75 4 1 (Some 4) _ 3 _ eq_refl) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 4 0 2 1 (Some 3) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 3 0 3 2 (Some 4) _ _ eq_refl). }
      destruct (IH (S j) R0) as [t2 H2].
      replace (S j + S n' + 1) with (S (S j) + n' + 1) by lia.
      exists (3 + t2). eapply reaches_trans; [exact Hs | exact H2]. }
  assert (H12 : exists t12, Reaches bb75
    (mkCfgR (Some 3) (2 :: rep m 3 []) (1 :: R))
    (mkCfgR (Some 4) [] (0 :: rep (m + 1) 1 (4 :: R))) t12).
  { destruct m as [| m'].
    - exists 2.
      eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 3 3 2 1 (Some 3) _ _ eq_refl) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 3 0 2 (Some 4) _ eq_refl).
    - assert (Ha : Reaches bb75
        (mkCfgR (Some 3) (2 :: 3 :: rep m' 3 []) (1 :: R))
        (mkCfgR (Some 4) (rep m' 3 []) (3 :: 1 :: 4 :: R)) 2).
      { eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 3 3 2 1 (Some 3) _ _ eq_refl) |].
        apply steps_one. apply (step_mkCfgR_L_cons bb75 3 0 3 2 (Some 4) _ _ eq_refl). }
      destruct (Hloop m' 0 (4 :: R)) as [tb Hb].
      replace (1 + m' + 1) with (S m' + 1) in Hb by lia.
      exists (2 + tb). eapply reaches_trans; [exact Ha | exact Hb]. }
  destruct H12 as [t12 H12].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 4) [] (0 :: rep (m + 1) 1 (4 :: R)))
    (mkCfgR (Some 5) (rep (m + 2) 3 []) (4 :: R)) (1 + (m + 1))).
  { eapply reaches_trans.
    - apply steps_one. apply (step_mkCfgR_R bb75 4 2 (Some 5) [] 0 _ eq_refl).
    - replace (rep (m + 2) 3 []) with (rep (m + 1) 3 [3])
        by (replace (m + 2) with ((m + 1) + 1) by lia; rewrite (rep_add (m + 1) 1); reflexivity).
      apply (loop_F1_R (m + 1) [3] (4 :: R)). }
  destruct (rule_F4 m R) as [t4 [H4 Hle4]].
  exists (t12 + (1 + (m + 1)) + t4).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H12 | exact H3] | exact H4] | lia].
Qed.

Lemma rule_D1_step : forall k m R,
  exists t, Reaches bb75
    (Dcfg5 (S k) m (1 :: R))
    (Dcfg5 k 1 (rep (m + 1) 1 (4 :: R))) t.
Proof.
  intros k m R. unfold Dcfg5.
  assert (H1 : Reaches bb75
    (mkCfgR (Some 3) (2 :: 2 :: rep k 2 (rep m 3 [])) (1 :: R))
    (mkCfgR (Some 4) (rep k 2 (rep m 3 [])) (2 :: 1 :: 4 :: R)) 2).
  { eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 3 3 2 1 (Some 3) _ _ eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_cons bb75 3 0 2 2 (Some 4) _ _ eq_refl). }
  destruct (sweep_E2_1 m k 0 (4 :: R)) as [t2 H2].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 4) (rep k 2 []) (2 :: rep (m + 1) 1 (4 :: R)))
    (mkCfgR (Some 3) (rep (S k) 2 [3]) (rep (m + 1) 1 (4 :: R)))
    (k + 1 + 1 + 1 + k)).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
    - eapply reaches_trans; [apply (loop_E2_L k [] (rep (m + 1) 1 (4 :: R))) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 4 2 2 (Some 4) _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 4 2 (Some 5) [] 0 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 5 1 (Some 3) [3] 3 _ eq_refl).
    - replace (rep (S k) 2 [3]) with (rep k 2 [2; 3])
        by (replace (S k) with (k + 1) by lia; rewrite rep_add; reflexivity).
      apply (loop_D3_R k [2; 3] (rep (m + 1) 1 (4 :: R))). }
  replace (1 + m) with (m + 1) in H2 by lia.
  exists (2 + t2 + (k + 1 + 1 + 1 + k)).
  eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
Qed.

Fixpoint Dfn (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => 2 * W5 (m + 1) 0 + 1
  | S k' => fun m => iter (Dfn k') (m + 1) 1
  end.

Lemma rule_D1_full : forall k m R,
  exists t, Reaches bb75 (Dcfg5 k m (1 :: R)) (Dcfg5 k (Dfn k m) R) t /\ Dfn k m <= t.
Proof.
  induction k as [| k' IH]; intros m R.
  - simpl. apply rule_D1_base.
  - assert (Hrep : forall n x R0,
      exists t, Reaches bb75 (Dcfg5 k' x (rep n 1 R0)) (Dcfg5 k' (iter (Dfn k') n x) R0) t /\
                (1 <= n -> iter (Dfn k') n x <= t)).
    { induction n as [| p IHp]; intros x R0.
      - exists 0. split; [apply reaches_zero | lia].
      - destruct (IH x (rep p 1 R0)) as [t1 [H1 Hle1]].
        destruct (IHp (Dfn k' x) R0) as [t2 [H2 Hle2]].
        replace (iter (Dfn k') (S p) x) with (iter (Dfn k') p (Dfn k' x))
          by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
        exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        intros _. destruct p as [| p']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia]. }
    destruct (rule_D1_step k' m R) as [t1 H1].
    destruct (Hrep (m + 1) 1 (4 :: R)) as [t2 [H2 Hle2]].
    assert (H3 : Reaches bb75 (Dcfg5 k' (iter (Dfn k') (m + 1) 1) (4 :: R))
                              (Dcfg5 (S k') (iter (Dfn k') (m + 1) 1) R) 1).
    { unfold Dcfg5. apply steps_one. apply (step_mkCfgR_R bb75 3 1 (Some 3) _ 4 _ eq_refl). }
    exists (t1 + t2 + 1). split.
    + eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
    + specialize (Hle2 ltac:(lia)). simpl. lia.
Qed.

Lemma W5_gt_f_omega_strong : forall m, f_omega m < W5 (m + 1) 0.
Proof.
  intro m.
  assert (H1 : Kfn m (Kfn m 0) < W5 (m + 1) 0).
  { replace (m + 1) with (S m) by lia. simpl.
    pose proof (W5_ge m (Kfn m (Kfn m 0))). lia. }
  assert (H2 : m <= Kfn m 0) by (pose proof (Kfn_zero_ge m); lia).
  assert (H3 : Kfn m m <= Kfn m (Kfn m 0)) by (apply Kfn_mono; exact H2).
  assert (H4 : fFin m m <= Kfn m m) by (apply Kfn_ge_fFin).
  change (fFin m m < W5 (m + 1) 0). lia.
Qed.

(* Growth of Dfn: f_{ω + k}(m) < Dfn k m *)
Lemma Dfn_ge_succ : forall k m, S m <= Dfn k m.
Proof.
  induction k as [| k' IH]; intro m.
  - simpl. pose proof (W5_gt_f_omega_strong m).
    pose proof (fgh_ge_self _ (fOmegaMul_props 1 0) m).
    change (m <= f_omega m) in H0. lia.
  - simpl. assert (Hge : forall n, n + 1 <= iter (Dfn k') n 1).
    { induction n as [| p IHp]; [simpl; lia |].
      simpl. pose proof (IH (iter (Dfn k') p 1)). lia. }
    pose proof (Hge (m + 1)). lia.
Qed.

Lemma W5_mono : forall k x y, x <= y -> W5 k x <= W5 k y.
Proof.
  induction k as [| k' IH]; intros x y Hxy; [simpl; lia |].
  simpl. apply IH.
  assert (Hstep : forall n, iter (Kfn k') n 0 <= iter (Kfn k') (S n) 0).
  { intro n. simpl. pose proof (Kfn_ge_succ k' (iter (Kfn k') n 0)). lia. }
  assert (Hmn : forall a b, a <= b -> iter (Kfn k') a 0 <= iter (Kfn k') b 0).
  { intros a b Hab. induction Hab; [lia | eapply Nat.le_trans; [exact IHHab | apply Hstep]]. }
  apply Hmn. lia.
Qed.

Lemma W5_step_k : forall k m, W5 k m <= W5 (S k) m.
Proof.
  intros k m. change (W5 k m <= W5 k (iter (Kfn k) (2 * m + 2) 0)). apply W5_mono.
  assert (Hge : 2 * m + 2 <= iter (Kfn k) (2 * m + 2) 0).
  { induction (2 * m + 2) as [| n IHn]; [simpl; lia |].
    simpl. pose proof (Kfn_ge_succ k (iter (Kfn k) n 0)). lia. }
  lia.
Qed.

Lemma W5_mono_k : forall k1 k2 m, k1 <= k2 -> W5 k1 m <= W5 k2 m.
Proof.
  intros k1 k2 m Hk. induction Hk; [lia | eapply Nat.le_trans; [exact IHHk | apply W5_step_k]].
Qed.

Lemma Dfn_mono : forall k x y, x <= y -> Dfn k x <= Dfn k y.
Proof.
  induction k as [| k' IH]; intros x y Hxy.
  - simpl. pose proof (W5_mono_k (x + 1) (y + 1) 0 ltac:(lia)). lia.
  - simpl. assert (Hstep : forall n, iter (Dfn k') n 1 <= iter (Dfn k') (S n) 1).
    { intro n. simpl. pose proof (Dfn_ge_succ k' (iter (Dfn k') n 1)). lia. }
    assert (Hmn : forall a b, a <= b -> iter (Dfn k') a 1 <= iter (Dfn k') b 1).
    { intros a b Hab. induction Hab; [lia | eapply Nat.le_trans; [exact IHHab | apply Hstep]]. }
    apply Hmn. lia.
Qed.

Lemma Dfn_step_k : forall k m, Dfn k m <= Dfn (S k) m.
Proof.
  intros k m. simpl.
  assert (Hge : m <= iter (Dfn k) m 1).
  { induction m as [| p IHp]; [simpl; lia |].
    simpl. pose proof (Dfn_ge_succ k (iter (Dfn k) p 1)). lia. }
  replace (m + 1) with (S m) by lia. simpl.
  apply Dfn_mono. exact Hge.
Qed.

Lemma Dfn_mono_k : forall k1 k2 m, k1 <= k2 -> Dfn k1 m <= Dfn k2 m.
Proof.
  intros k1 k2 m Hk. induction Hk; [lia | eapply Nat.le_trans; [exact IHHk | apply Dfn_step_k]].
Qed.

Lemma Dfn_ge_double : forall k m, 2 * m + 1 <= Dfn k m.
Proof.
  induction k as [| k' IH]; intro m.
  - simpl. pose proof (W5_gt_f_omega_strong m).
    pose proof (fgh_ge_self _ (fOmegaMul_props 1 0) m).
    change (m <= f_omega m) in H0. lia.
  - simpl. assert (Hge : forall n, 2 * n + 1 <= iter (Dfn k') n 1).
    { induction n as [| p IHp]; [simpl; lia |].
      simpl. pose proof (IH (iter (Dfn k') p 1)). lia. }
    pose proof (Hge (m + 1)). lia.
Qed.

Lemma Dfn_one_ge_2k : forall k, 2 * k + 1 <= Dfn k 1.
Proof.
  induction k as [| k' IH].
  - simpl. pose proof (W5_ge 2 0). lia.
  - simpl. pose proof (Dfn_ge_double k' (Dfn k' 1)). lia.
Qed.

Lemma Dfn_gt_2_f_omega_plus : forall k m, 2 * f_omega_plus k m < Dfn k (2 * m).
Proof.
  induction k as [| k' IH]; intro m.
  - change (2 * f_omega m < Dfn 0 (2 * m)).
    pose proof (W5_gt_f_omega_strong m) as H0.
    pose proof (Dfn_mono 0 m (2 * m) ltac:(lia)) as Hm.
    change (2 * W5 (m + 1) 0 + 1 <= Dfn 0 (2 * m)) in Hm. lia.
  - rewrite f_omega_plus_succ_eq.
    assert (Hiter : forall j, 2 * iter (f_omega_plus k') j m <= iter (Dfn k') j (2 * m)).
    { induction j as [| j' IHj]; [simpl; lia |].
      simpl.
      eapply Nat.le_trans; [| apply Dfn_mono; exact IHj].
      pose proof (IH (iter (f_omega_plus k') j' m)). lia. }
    assert (Hinit : 2 * m + 1 <= iter (Dfn k') m 1).
    { clear Hiter. induction m as [| p IHp]; [simpl; lia |].
      simpl. pose proof (Dfn_ge_double k' (iter (Dfn k') p 1)). lia. }
    change (2 * iter (f_omega_plus k') m m < iter (Dfn k') (2 * m + 1) 1).
    replace (2 * m + 1) with (S (m + m)) by lia.
    rewrite iter_succ, iter_add.
    pose proof (Dfn_ge_double k' (iter (Dfn k') m (iter (Dfn k') m 1))) as Hd.
    assert (Harg : iter (Dfn k') m (2 * m) <= iter (Dfn k') m (iter (Dfn k') m 1)).
    { apply iter_mono_arg; [exact (Dfn_mono k') | lia]. }
    pose proof (Hiter m). lia.
Qed.

(* A0 rule: Bcfg (S k) m [] -> Dcfg5 (k + 2 * m + 2) 1 [1] *)
Lemma rule_A0 : forall k m,
  exists t, Reaches bb75 (Bcfg (S k) m []) (Dcfg5 (k + 2 * m + 2) 1 [1]) t.
Proof.
  intros k m. unfold Bcfg, Dcfg5.
  assert (H1 : Reaches bb75
    (mkCfgR (Some 0) (2 :: 2 :: rep k 2 (rep (2 * m + 1) 3 [])) [])
    (mkCfgR (Some 4) (rep k 2 (rep (2 * m + 1) 3 [])) (2 :: 4 :: [1])) 2).
  { eapply steps_succ; [apply (step_mkCfgR_L_cons bb75 0 0 2 0 (Some 5) _ [] eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_cons bb75 5 3 2 2 (Some 4) _ [1] eq_refl). }
  destruct (sweep_E2_4 (2 * m + 1) k 0 [1]) as [t2 H2].
  assert (H3 : Reaches bb75
    (mkCfgR (Some 4) (rep k 2 []) (2 :: 4 :: rep (2 * m + 1) 3 [1]))
    (mkCfgR (Some 3) (rep (S (k + 2 * m + 2)) 2 [3]) [1])
    (k + 1 + 1 + 1 + k + 1 + (2 * m + 1))).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
    - eapply reaches_trans; [apply (loop_E2_L k [] (4 :: rep (2 * m + 1) 3 [1])) |].
      apply steps_one. apply (step_mkCfgR_L_nil bb75 4 2 2 (Some 4) _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 4 2 (Some 5) [] 0 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb75 5 1 (Some 3) [3] 3 _ eq_refl).
    - apply (loop_D3_R k [2; 3] (4 :: rep (2 * m + 1) 3 [1])).
    - apply steps_one. apply (step_mkCfgR_R bb75 3 1 (Some 3) _ 4 _ eq_refl).
    - replace (rep (S (k + 2 * m + 2)) 2 [3]) with (rep (2 * m + 1) 2 (2 :: rep k 2 [2; 3]))
        by (replace (S (k + 2 * m + 2)) with ((2 * m + 1) + 1 + k + 1) by lia;
            rewrite !rep_add; reflexivity).
      apply (loop_D3_R (2 * m + 1) (2 :: rep k 2 [2; 3]) [1]). }
  exists (2 + t2 + (k + 1 + 1 + 1 + k + 1 + (2 * m + 1))).
  eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
Qed.

Lemma rule_D0 : forall k m, exists t, HaltsIn bb75 (Dcfg5 k m []) t /\ t = 1.
Proof.
  intros k m. exists 1. split; [| reflexivity].
  exists (mkCfgR None (1 :: rep (S k) 2 (rep m 3 [])) []).
  split; [| reflexivity].
  apply steps_one. apply (step_mkCfgR_R_nil bb75 3 0 None _ eq_refl).
Qed.

Lemma bb75_bootstrap : Reaches bb75 initConfig (Bcfg 15 1 [1]) 146.
Proof. unfold Reaches, initConfig, Bcfg, mkCfgR, rep. vm_compute. reflexivity. Qed.

Lemma Kfn_succ_gt_f_omega : forall n, f_omega n < Kfn (S n) 1.
Proof.
  intro n.
  assert (Hn : n <= Kfn n 0) by (pose proof (Kfn_zero_ge n); lia).
  assert (H1 : n <= Kfn n (Kfn n 0)) by (pose proof (Kfn_ge_succ n (Kfn n 0)); lia).
  pose proof (Kfn_ge_fFin n n) as Hf.
  pose proof (Kfn_mono n n (Kfn n (Kfn n 0)) H1) as Hm1.
  pose proof (Kfn_ge_succ n (Kfn n (Kfn n 0))) as Hs.
  assert (Heq : Kfn (S n) 1 = Kfn n (Kfn n (Kfn n (Kfn n 0)))) by reflexivity.
  pose proof (Kfn_ge_succ n (Kfn n (Kfn n (Kfn n 0)))) as Hs2.
  change (fFin n n < Kfn (S n) 1). rewrite Heq. lia.
Qed.

Lemma Dfn_gt_f_omega_mul2 : forall X M, X < M -> f_omega_mul2 X < Dfn (14 + 2 * M + 2) 1.
Proof.
  intros X M HM.
  assert (H1k : Dfn (S X) 1 <= Dfn (14 + 2 * M + 2) 1) by (apply Dfn_mono_k; lia).
  assert (H2k : 2 * X <= Dfn X 1) by (pose proof (Dfn_one_ge_2k X); lia).
  assert (H3k : Dfn X (2 * X) <= Dfn (S X) 1).
  { change (Dfn (S X) 1) with (Dfn X (Dfn X 1)). apply Dfn_mono. exact H2k. }
  pose proof (Dfn_gt_2_f_omega_plus X X).
  change (f_omega_mul2 X) with (f_omega_plus X X). lia.
Qed.

Theorem bb75_halts_gt_f_omega_mul2_f_omega_14 :
  ValidTM 7 5 bb75 /\ exists t, HaltsIn bb75 initConfig t /\ f_omega_mul2 (f_omega 14) < t.
Proof.
  split; [exact bb75_valid |].
  pose proof bb75_bootstrap as Hb.
  destruct (kropitz_step bb75 2 bb75_kropitz 15 1 []) as [t1 [H1 _]].
  destruct (rule_A0 14 (Kfn 15 1)) as [t2 H2].
  destruct (rule_D1_full (14 + 2 * Kfn 15 1 + 2) 1 []) as [t3 [H3 Hle3]].
  destruct (rule_D0 (14 + 2 * Kfn 15 1 + 2) (Dfn (14 + 2 * Kfn 15 1 + 2) 1)) as [t4 [[cf [H4 Hst]] _]].
  assert (Hall : Reaches bb75 initConfig cf (146 + t1 + t2 + t3 + t4)).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hb | exact H1] | exact H2] | exact H3] | exact H4]. }
  pose proof (Dfn_gt_f_omega_mul2 (f_omega 14) (Kfn 15 1) (Kfn_succ_gt_f_omega 14)) as Hfb.
  exists (146 + t1 + t2 + t3 + t4).
  split; [exists cf; split; [exact Hall | exact Hst] | lia].
Qed.

Print Assumptions bb75_halts_gt_f_omega_mul2_f_omega_14.
