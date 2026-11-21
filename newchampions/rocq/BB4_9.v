(*
  rocq/BB4_9.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(4, 9):
    TM: 5LC3LB7LA2RA4LB8LB4LB6LA7RA_1RZ3RB1LC2RA3RD3RA4LC0LC2LA_3RB1LB3LC2RC4LC5LC5LD8LC3RA_3RB---6LC4LD4LC4LD6LC7LA---
    Domain: BB(4, 9) (4 states, 9 symbols)
    Proved bound here: halts from blank tape in exact t steps with t > f_{ω+4}(12)
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Definition bb49 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 5 DL (Some 2))
  | 0, 1 => Some (mkAction 3 DL (Some 1))
  | 0, 2 => Some (mkAction 7 DL (Some 0))
  | 0, 3 => Some (mkAction 2 DR (Some 0))
  | 0, 4 => Some (mkAction 4 DL (Some 1))
  | 0, 5 => Some (mkAction 8 DL (Some 1))
  | 0, 6 => Some (mkAction 4 DL (Some 1))
  | 0, 7 => Some (mkAction 6 DL (Some 0))
  | 0, 8 => Some (mkAction 7 DR (Some 0))
  | 1, 0 => Some (mkAction 1 DR None)
  | 1, 1 => Some (mkAction 3 DR (Some 1))
  | 1, 2 => Some (mkAction 1 DL (Some 2))
  | 1, 3 => Some (mkAction 2 DR (Some 0))
  | 1, 4 => Some (mkAction 3 DR (Some 3))
  | 1, 5 => Some (mkAction 3 DR (Some 0))
  | 1, 6 => Some (mkAction 4 DL (Some 2))
  | 1, 7 => Some (mkAction 0 DL (Some 2))
  | 1, 8 => Some (mkAction 2 DL (Some 0))
  | 2, 0 => Some (mkAction 3 DR (Some 1))
  | 2, 1 => Some (mkAction 1 DL (Some 1))
  | 2, 2 => Some (mkAction 3 DL (Some 2))
  | 2, 3 => Some (mkAction 2 DR (Some 2))
  | 2, 4 => Some (mkAction 4 DL (Some 2))
  | 2, 5 => Some (mkAction 5 DL (Some 2))
  | 2, 6 => Some (mkAction 5 DL (Some 3))
  | 2, 7 => Some (mkAction 8 DL (Some 2))
  | 2, 8 => Some (mkAction 3 DR (Some 0))
  | 3, 0 => Some (mkAction 3 DR (Some 1))
  | 3, 2 => Some (mkAction 6 DL (Some 2))
  | 3, 3 => Some (mkAction 4 DL (Some 3))
  | 3, 4 => Some (mkAction 4 DL (Some 2))
  | 3, 5 => Some (mkAction 4 DL (Some 3))
  | 3, 6 => Some (mkAction 6 DL (Some 2))
  | 3, 7 => Some (mkAction 7 DL (Some 0))
  | _, _ => None
  end.

Lemma bb49_valid : ValidTM 4 9 bb49.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|s]]]]; try lia;
    destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|s]]]];
    try (destruct sym as [|[|[|[|[|[|[|[|[|sym]]]]]]]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma bb49_kropitz : KropitzCore bb49 2.
Proof. constructor; reflexivity. Qed.

Definition Dcfg (N : nat) (R : list nat) : Config :=
  mkCfgR (Some 3) (rep N 3 []) R.

Fixpoint Gexit (k : nat) : nat -> nat :=
  match k with
  | 0 => fun m => 2 * m + 4
  | S j => fun m => Gexit j (Kfn (S j) m)
  end.

Definition G4 (N : nat) : nat := Gexit (N - 1) 0.
Definition G5 (N : nat) : nat := iter G4 N 2.
Definition G6 (N : nat) : nat := iter G5 N 4.
Definition G7 (N : nat) : nat := iter G6 N 4.

(* Rule D0 *)
Lemma rule_D0 : forall N, exists t, HaltsIn bb49 (Dcfg N []) t /\ t = 2.
Proof.
  intro N. exists 2. split; [| reflexivity].
  exists (mkCfgR None (1 :: 3 :: rep N 3 []) []).
  split; [| reflexivity].
  eapply steps_succ; [apply (step_mkCfgR_R_nil bb49 3 2 (Some 1) _ eq_refl) |].
  apply steps_one. apply (step_mkCfgR_R_nil bb49 1 0 None _ eq_refl).
Qed.

(* Rule D4 *)
Lemma loop_C_4 : forall n j L R,
  exists t, Reaches bb49 (mkCfgR (Some 2) (rep n 3 L) (2 :: rep j 3 (4 :: R)))
                         (mkCfgR (Some 2) L (2 :: rep (j + n) 3 (4 :: R))) t.
Proof.
  induction n as [| k IH]; intros j L R.
  - exists 0. replace (j + 0) with j by lia. apply reaches_zero.
  - assert (Hstep : Reaches bb49
      (mkCfgR (Some 2) (3 :: rep k 3 L) (2 :: rep j 3 (4 :: R)))
      (mkCfgR (Some 2) (rep k 3 L) (2 :: rep (S j) 3 (4 :: R)))
      (S (j + 2) + S (j + 1))).
    { eapply reaches_trans.
      - eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 2 3 2 (Some 2) _ _ eq_refl) |].
        replace (3 :: 3 :: rep j 3 (4 :: R)) with (rep (j + 2) 3 (4 :: R)).
        + apply (loop_C3 bb49 2 bb49_kropitz (j + 2) (rep k 3 L) (4 :: R)).
        + replace (j + 2) with (S (S j)) by lia. reflexivity.
      - replace (j + 2) with (S (j + 1)) by lia. simpl.
        eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 3 2 4 (Some 2) _ _ eq_refl) |].
        replace (3 :: rep j 3 (4 :: R)) with (rep (j + 1) 3 (4 :: R))
          by (replace (j + 1) with (S j) by lia; reflexivity).
        apply (loop_C2 bb49 2 bb49_kropitz (j + 1) (rep k 3 L) (4 :: R)). }
    destruct (IH (S j) L R) as [t2 Hrest].
    replace (j + S k) with (S j + k) by lia.
    exists (S (j + 2) + S (j + 1) + t2).
    eapply reaches_trans; [exact Hstep | exact Hrest].
Qed.

Lemma d4_entry : forall k R,
  exists t, Reaches bb49 (Dcfg (k + 2) (4 :: R)) (Bcfg (S k) 0 (4 :: R)) t.
Proof.
  intros k R.
  replace (k + 2) with (S (S k)) by lia.
  destruct (loop_C_4 (S k) 0 [] R) as [tl Hl]. simpl in Hl.
  exists (S (S (S (tl + S (S (S (S k))))))).
  unfold Dcfg, Bcfg. simpl.
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 3 3 4 (Some 2) _ _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) _ 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 3 2 4 (Some 2) _ _ eq_refl) |].
  eapply reaches_trans; [exact Hl |].
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 2 2 2 (Some 2) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 1 (Some 0) [3] 3 _ eq_refl) |].
  pose proof (loop_A3 bb49 2 bb49_kropitz (S k) [2; 3] (4 :: R)) as H.
  rewrite rep_snoc_one in H. exact H.
Qed.

Lemma b4_exit : forall k m R,
  exists t, Reaches bb49 (Bcfg k m (4 :: R)) (Dcfg (Gexit k m) R) t /\ Gexit k m <= t.
Proof.
  induction k as [| j IH]; intros m R.
  - exists (S ((8 * m + 7) + 1)). split; [| simpl; lia].
    unfold Bcfg, Dcfg. simpl.
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 3 2 4 (Some 1) _ _ eq_refl) |].
    eapply reaches_trans; [apply (kropitz_level0_from_B bb49 2 bb49_kropitz m (4 :: R)) |].
    apply steps_one.
    replace (m + (m + 0) + 4) with (S (2 * m + 3)) by lia.
    apply (step_mkCfgR_R bb49 1 2 (Some 3) _ 4 R eq_refl).
  - destruct (kropitz_rep bb49 2 bb49_kropitz j (2 * m + 2) 0 (4 :: R)) as [t3 H3].
    destruct (IH (Kfn (S j) m) R) as [t4 [H4 Hle4]].
    exists ((S ((2 * j + 5) * (2 * m + 1) + (2 * j + 4)) + t3) + t4).
    split; [| change (Gexit j (Kfn (S j) m) <= (S ((2 * j + 5) * (2 * m + 1) + (2 * j + 4)) + t3) + t4); lia].
    eapply reaches_trans; [eapply reaches_trans; [| exact H3] | exact H4].
    unfold Bcfg at 1. simpl.
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 3 2 4 (Some 1) _ _ eq_refl) |].
    apply (kropitz_levelS_from_B bb49 2 bb49_kropitz j m (4 :: R)).
Qed.

Lemma Gexit_ge : forall k m, 2 * m + 4 <= Gexit k m.
Proof.
  induction k as [| j IH]; intro m; [simpl; lia |].
  change (2 * m + 4 <= Gexit j (Kfn (S j) m)).
  pose proof (IH (Kfn (S j) m)). pose proof (Kfn_ge_succ (S j) m). lia.
Qed.

Lemma Gexit_mono_m : forall k x y, x <= y -> Gexit k x <= Gexit k y.
Proof.
  induction k as [| j IH]; intros x y Hxy; [simpl; lia |].
  change (Gexit j (Kfn (S j) x) <= Gexit j (Kfn (S j) y)).
  apply IH, Kfn_mono; exact Hxy.
Qed.

Lemma Gexit_step_k : forall k m, Gexit k m <= Gexit (S k) m.
Proof.
  intros k m. change (Gexit k m <= Gexit k (Kfn (S k) m)). apply Gexit_mono_m.
  pose proof (Kfn_ge_succ (S k) m). lia.
Qed.

Lemma Gexit_mono_k : forall k1 k2 m, k1 <= k2 -> Gexit k1 m <= Gexit k2 m.
Proof.
  intros k1 k2 m Hk. induction Hk as [| j Hle IH]; [lia |].
  eapply Nat.le_trans; [exact IH | apply Gexit_step_k].
Qed.

Lemma rule_D4 : forall N R, 2 <= N ->
  exists t, Reaches bb49 (Dcfg N (4 :: R)) (Dcfg (G4 N) R) t /\ G4 N <= t.
Proof.
  intros N R HN. destruct N as [|[|k]]; try lia.
  destruct (d4_entry k R) as [t1 H1].
  destruct (b4_exit (S k) 0 R) as [t2 [H2 Hle2]].
  replace (k + 2) with (S (S k)) in H1 by lia.
  unfold G4. replace (S (S k) - 1) with (S k) by lia.
  exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] | lia].
Qed.

Lemma G4_mono : forall x y, x <= y -> G4 x <= G4 y.
Proof. intros x y Hxy. unfold G4. apply Gexit_mono_k. lia. Qed.

Lemma G4_ge_2x_plus_4 : forall n, 2 <= n -> 2 * n + 4 <= G4 n.
Proof.
  intros n Hn. destruct n as [|[|k]]; try lia.
  unfold G4. replace (S (S k) - 1) with (S k) by lia.
  change (2 * S (S k) + 4 <= Gexit k (Kfn (S k) 0)).
  pose proof (Gexit_ge k (Kfn (S k) 0)).
  pose proof (Kfn_zero_ge (S k)). lia.
Qed.

Lemma G4_inc : forall n, 2 <= n -> S n <= G4 n.
Proof. intros n Hn. pose proof (G4_ge_2x_plus_4 n Hn). lia. Qed.

Lemma rule_D4_rep : forall n N R, 2 <= N ->
  exists t, Reaches bb49 (Dcfg N (rep n 4 R)) (Dcfg (iter G4 n N) R) t /\
            (1 <= n -> iter G4 n N <= t).
Proof.
  induction n as [| k IH]; intros N R HN.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_D4 N (rep k 4 R) HN) as [t1 [H1 Hle1]].
    assert (HGN : 2 <= G4 N) by (pose proof (G4_inc N HN); lia).
    destruct (IH (G4 N) R HGN) as [t2 [H2 Hle2]].
    replace (iter G4 (S k) N) with (iter G4 k (G4 N))
      by (replace (S k) with (k + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split.
    + eapply reaches_trans; [exact H1 | exact H2].
    + intros _. destruct k as [| k'].
      * simpl in *. lia.
      * specialize (Hle2 ltac:(lia)). lia.
Qed.

(* Rule D5 *)
Lemma loop_D3 : forall n L R,
  Reaches bb49 (mkCfgR (Some 3) (rep n 3 L) (3 :: R))
               (mkCfgR (Some 3) L (3 :: rep n 4 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 3 3 3 (Some 3) _ _ eq_refl) |].
  specialize (IH L (4 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma rule_D5_expand : forall N R, 1 <= N ->
  Reaches bb49 (Dcfg N (5 :: R)) (Dcfg 2 (rep N 4 R)) (N + 3).
Proof.
  intros N R HN. destruct N as [| k]; [lia |].
  replace (S k + 3) with (S (k + 3)) by lia.
  unfold Dcfg.
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 3 3 5 (Some 3) _ _ eq_refl) |].
  eapply reaches_trans; [apply (loop_D3 k [] (4 :: R)) |].
  rewrite rep_snoc_one.
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 3 3 3 (Some 3) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 3 2 (Some 1) [] 0 _ eq_refl) |].
  apply steps_one. apply (step_mkCfgR_R bb49 1 2 (Some 3) [3] 4 (rep (S k) 4 R) eq_refl).
Qed.

Lemma rule_D5 : forall N R, 1 <= N ->
  exists t, Reaches bb49 (Dcfg N (5 :: R)) (Dcfg (G5 N) R) t /\ G5 N <= t.
Proof.
  intros N R HN.
  pose proof (rule_D5_expand N R HN) as H1.
  destruct (rule_D4_rep N 2 R ltac:(lia)) as [t2 [H2 Hle2]].
  exists ((N + 3) + t2). split.
  - eapply reaches_trans; [exact H1 | exact H2].
  - specialize (Hle2 HN). unfold G5. lia.
Qed.

(* Rule D6 *)
Lemma loop_D6_shuttle : forall n R,
  Reaches bb49 (mkCfgR (Some 2) (rep n 3 []) (3 :: 6 :: R))
               (mkCfgR (Some 2) [] (0 :: 6 :: rep (S n) 5 R)) (3 * n + 3).
Proof.
  induction n as [| k IH]; intro R.
  - simpl.
    eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) [] 3 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 4 2 6 (Some 3) [] R eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_nil bb49 3 5 2 (Some 2) _ eq_refl).
  - replace (3 * S k + 3) with (S (S (S (3 * k + 3)))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) _ 3 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 4 2 6 (Some 3) _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 5 3 2 (Some 2) _ _ eq_refl) |].
    specialize (IH (5 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma d6_exit_16 : forall R, Reaches bb49 (mkCfgR (Some 2) [] (0 :: 6 :: R)) (Dcfg 4 R) 16.
Proof.
  intro R. unfold Dcfg. simpl.
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 1 3 3 6 (Some 2) [] R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) [] 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 3 2 4 (Some 2) [] R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 2 2 2 (Some 2) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 1 (Some 0) [3] 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 3 2 4 (Some 1) [3] R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 1 0 3 2 (Some 2) [] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) [] 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 0 2 1 (Some 1) [] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 1 0 2 (Some 2) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 2 (Some 1) [3] 1 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 2 (Some 1) [3; 3] 1 _ eq_refl) |].
  apply steps_one. apply (step_mkCfgR_R bb49 1 2 (Some 3) [3; 3; 3] 4 R eq_refl).
Qed.

Lemma rule_D6_expand : forall N R, 1 <= N ->
  Reaches bb49 (Dcfg N (6 :: R)) (Dcfg 4 (rep N 5 R)) (3 * N + 17).
Proof.
  intros N R HN. destruct N as [| k]; [lia |].
  replace (3 * S k + 17) with (S ((3 * k + 3) + 16)) by lia.
  unfold Dcfg at 1. simpl.
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 5 3 6 (Some 2) _ _ eq_refl) |].
  eapply reaches_trans; [apply loop_D6_shuttle | apply d6_exit_16].
Qed.

(* Rule D7 *)
Lemma loop_D7_shuttle : forall n R,
  Reaches bb49 (mkCfgR (Some 0) (rep n 3 []) (3 :: 7 :: R))
               (mkCfgR (Some 0) [] (0 :: 7 :: rep (S n) 6 R)) (3 * n + 3).
Proof.
  induction n as [| k IH]; intro R.
  - simpl.
    eapply steps_succ; [apply (step_mkCfgR_R bb49 0 1 (Some 0) [] 3 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 5 2 7 (Some 0) [] R eq_refl) |].
    apply steps_one. apply (step_mkCfgR_L_nil bb49 0 6 2 (Some 0) _ eq_refl).
  - replace (3 * S k + 3) with (S (S (S (3 * k + 3)))) by lia.
    eapply steps_succ; [apply (step_mkCfgR_R bb49 0 1 (Some 0) _ 3 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 5 2 7 (Some 0) _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 6 3 2 (Some 0) _ _ eq_refl) |].
    specialize (IH (6 :: R)). rewrite rep_snoc_one in IH. exact IH.
Qed.

Lemma d7_exit_14 : forall R, Reaches bb49 (mkCfgR (Some 0) [] (0 :: 7 :: R)) (Dcfg 4 R) 14.
Proof.
  intro R. unfold Dcfg. simpl.
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 0 4 0 (Some 2) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 2 (Some 0) [3] 5 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 5 3 7 (Some 0) [3] R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 0 1 (Some 0) [3] 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 0 3 2 6 (Some 1) [3] R eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 1 0 3 2 (Some 2) [] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 1 (Some 2) [] 3 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 2 0 2 1 (Some 1) [] _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_L_nil bb49 1 0 2 (Some 2) _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 2 2 (Some 1) [] 0 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 2 (Some 1) [3] 1 _ eq_refl) |].
  eapply steps_succ; [apply (step_mkCfgR_R bb49 1 2 (Some 1) [3; 3] 1 _ eq_refl) |].
  apply steps_one. apply (step_mkCfgR_R bb49 1 2 (Some 3) [3; 3; 3] 4 R eq_refl).
Qed.

Lemma rule_D7_expand : forall N R, 1 <= N ->
  Reaches bb49 (Dcfg N (7 :: R)) (Dcfg 4 (rep N 6 R)) (3 * N + 15).
Proof.
  intros N R HN. destruct N as [| k]; [lia |].
  replace (3 * S k + 15) with (S ((3 * k + 3) + 14)) by lia.
  unfold Dcfg at 1. simpl.
  eapply steps_succ; [apply (step_mkCfgR_L_cons bb49 3 6 3 7 (Some 0) _ _ eq_refl) |].
  eapply reaches_trans; [apply loop_D7_shuttle | apply d7_exit_14].
Qed.

(* Growth Bounds *)
Lemma G4_sq_gt_f_omega : forall n, 2 <= n -> f_omega n < G4 (G4 n).
Proof.
  intros n Hn.
  pose proof (G4_ge_2x_plus_4 n Hn) as HM.
  generalize dependent (G4 n). intros M HM.
  destruct M as [|[|j]]; try lia.
  assert (Hj : n <= j) by lia.
  assert (Hge1 : 2 * Kfn (S j) 0 + 4 <= G4 (S (S j))).
  { unfold G4. replace (S (S j) - 1) with (S j) by lia.
    change (2 * Kfn (S j) 0 + 4 <= Gexit j (Kfn (S j) 0)). apply Gexit_ge. }
  assert (HK2 : n <= Kfn j 0) by (pose proof (Kfn_zero_ge j); lia).
  assert (HK3 : Kfn j n <= Kfn (S j) 0).
  { change (Kfn j n <= Kfn j (Kfn j 0)). apply Kfn_mono; exact HK2. }
  assert (HK4 : fFin n n <= Kfn j n)
    by (eapply Nat.le_trans; [apply Kfn_ge_fFin | apply Kfn_mono_k; exact Hj]).
  rewrite f_omega_eq. lia.
Qed.

Lemma G5_ge_3x : forall x, 2 <= x -> 3 * x <= G5 x.
Proof.
  intros x _.
  assert (Hstep : forall k, 2 + 4 * k <= iter G4 k 2).
  { intro k. induction k as [| m IH]; simpl; [lia |].
    pose proof (G4_ge_2x_plus_4 (iter G4 m 2) ltac:(lia)). lia. }
  pose proof (Hstep x). unfold G5. lia.
Qed.

Lemma G5_mono : forall x y, x <= y -> G5 x <= G5 y.
Proof.
  intros x y Hxy. unfold G5. apply iter_mono_steps; [| exact Hxy].
  intro z. destruct z as [|[|k]].
  - lia.
  - unfold G4. simpl. lia.
  - pose proof (G4_inc (S (S k)) ltac:(lia)). lia.
Qed.

Lemma G5_inc : forall x, 2 <= x -> S x <= G5 x.
Proof. intros x Hx. pose proof (G5_ge_3x x Hx). lia. Qed.

Lemma G5_sq_gt : forall x, 2 <= x -> f_omega_plus 1 x < G5 (G5 x).
Proof.
  apply (climb_level G4 f_omega 2 ltac:(lia) G4_mono G4_inc G4_sq_gt_f_omega G5_ge_3x
           (fOmegaMul_props 1 0)).
Qed.

Lemma G6_ge_3x : forall x, 2 <= x -> 3 * x <= G6 x.
Proof.
  intros x _.
  assert (Hstep : forall k, 4 + 4 * k <= iter G5 k 4).
  { intro k. induction k as [| m IH]; simpl; [lia |].
    pose proof (G5_ge_3x (iter G5 m 4) ltac:(lia)). lia. }
  pose proof (Hstep x). unfold G6. lia.
Qed.

Lemma G6_mono : forall x y, x <= y -> G6 x <= G6 y.
Proof.
  intros x y Hxy. unfold G6. apply iter_mono_steps; [| exact Hxy].
  intro z. destruct z as [|[|k]].
  - lia.
  - unfold G5. rewrite iter_succ, iter_zero. pose proof (G4_ge_2x_plus_4 2 ltac:(lia)). lia.
  - pose proof (G5_inc (S (S k)) ltac:(lia)). lia.
Qed.

Lemma G6_inc : forall x, 2 <= x -> S x <= G6 x.
Proof. intros x Hx. pose proof (G6_ge_3x x Hx). lia. Qed.

Lemma G6_sq_gt : forall x, 2 <= x -> f_omega_plus 2 x < G6 (G6 x).
Proof.
  apply (climb_level G5 (f_omega_plus 1) 4 ltac:(lia) G5_mono G5_inc G5_sq_gt G6_ge_3x
           (fOmegaMul_props 1 1)).
Qed.

Lemma G7_ge_3x : forall x, 2 <= x -> 3 * x <= G7 x.
Proof.
  intros x _.
  assert (Hstep : forall k, 4 + 4 * k <= iter G6 k 4).
  { intro k. induction k as [| m IH]; simpl; [lia |].
    pose proof (G6_ge_3x (iter G6 m 4) ltac:(lia)). lia. }
  pose proof (Hstep x). unfold G7. lia.
Qed.

Lemma G7_mono : forall x y, x <= y -> G7 x <= G7 y.
Proof.
  intros x y Hxy. unfold G7. apply iter_mono_steps; [| exact Hxy].
  intro z. destruct z as [|[|k]].
  - lia.
  - unfold G6. rewrite iter_succ, iter_zero. pose proof (G5_ge_3x 4 ltac:(lia)). lia.
  - pose proof (G6_inc (S (S k)) ltac:(lia)). lia.
Qed.

Lemma G7_inc : forall x, 2 <= x -> S x <= G7 x.
Proof. intros x Hx. pose proof (G7_ge_3x x Hx). lia. Qed.

Lemma G7_sq_gt : forall x, 2 <= x -> f_omega_plus 3 x < G7 (G7 x).
Proof.
  apply (climb_level G6 (f_omega_plus 2) 4 ltac:(lia) G6_mono G6_inc G6_sq_gt G7_ge_3x
           (fOmegaMul_props 1 2)).
Qed.

(* Full execution rules for 5^n, 6, 6^n, 7, 7^n *)
Lemma rule_D5_rep : forall n N R, 2 <= N ->
  exists t, Reaches bb49 (Dcfg N (rep n 5 R)) (Dcfg (iter G5 n N) R) t /\
            (1 <= n -> iter G5 n N <= t).
Proof.
  induction n as [| k IH]; intros N R HN.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_D5 N (rep k 5 R) ltac:(lia)) as [t1 [H1 Hle1]].
    assert (HGN : 2 <= G5 N) by (pose proof (G5_inc N HN); lia).
    destruct (IH (G5 N) R HGN) as [t2 [H2 Hle2]].
    replace (iter G5 (S k) N) with (iter G5 k (G5 N))
      by (replace (S k) with (k + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
    intros _. destruct k as [| k']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

Lemma rule_D6 : forall N R, 1 <= N ->
  exists t, Reaches bb49 (Dcfg N (6 :: R)) (Dcfg (G6 N) R) t /\ G6 N <= t.
Proof.
  intros N R HN.
  pose proof (rule_D6_expand N R HN) as H1.
  destruct (rule_D5_rep N 4 R ltac:(lia)) as [t2 [H2 Hle2]].
  exists ((3 * N + 17) + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
  specialize (Hle2 HN). unfold G6. lia.
Qed.

Lemma rule_D6_rep : forall n N R, 2 <= N ->
  exists t, Reaches bb49 (Dcfg N (rep n 6 R)) (Dcfg (iter G6 n N) R) t /\
            (1 <= n -> iter G6 n N <= t).
Proof.
  induction n as [| k IH]; intros N R HN.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_D6 N (rep k 6 R) ltac:(lia)) as [t1 [H1 Hle1]].
    assert (HGN : 2 <= G6 N) by (pose proof (G6_inc N HN); lia).
    destruct (IH (G6 N) R HGN) as [t2 [H2 Hle2]].
    replace (iter G6 (S k) N) with (iter G6 k (G6 N))
      by (replace (S k) with (k + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
    intros _. destruct k as [| k']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

Lemma rule_D7 : forall N R, 1 <= N ->
  exists t, Reaches bb49 (Dcfg N (7 :: R)) (Dcfg (G7 N) R) t /\ G7 N <= t.
Proof.
  intros N R HN.
  pose proof (rule_D7_expand N R HN) as H1.
  destruct (rule_D6_rep N 4 R ltac:(lia)) as [t2 [H2 Hle2]].
  exists ((3 * N + 15) + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
  specialize (Hle2 HN). unfold G7. lia.
Qed.

Lemma rule_D7_rep : forall n N R, 2 <= N ->
  exists t, Reaches bb49 (Dcfg N (rep n 7 R)) (Dcfg (iter G7 n N) R) t /\
            (1 <= n -> iter G7 n N <= t).
Proof.
  induction n as [| k IH]; intros N R HN.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_D7 N (rep k 7 R) ltac:(lia)) as [t1 [H1 Hle1]].
    assert (HGN : 2 <= G7 N) by (pose proof (G7_inc N HN); lia).
    destruct (IH (G7 N) R HGN) as [t2 [H2 Hle2]].
    replace (iter G7 (S k) N) with (iter G7 k (G7 N))
      by (replace (S k) with (k + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
    intros _. destruct k as [| k']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

(* Bootstrap from Blank Tape & Main Champion Theorem *)

Lemma G7_triple_gt : forall z, 2 <= z -> 3 * f_omega_plus 3 z + 1 <= G7 (3 * z + 1).
Proof.
  intros z Hz.
  assert (H1 : f_omega_plus 3 z < G7 (3 * z)).
  { unfold G7.
    replace (3 * z) with (2 * z + z) by lia.
    rewrite iter_add.
    rewrite <- iter_two_mul.
    assert (HzG : z <= iter G6 z 4).
    { pose proof (G7_ge_3x z Hz) as H3. unfold G7 in H3. lia. }
    assert (Harg : iter (fun y => G6 (G6 y)) z z <= iter (fun y => G6 (G6 y)) z (iter G6 z 4)).
    { apply iter_mono_arg; [intros a b Hab; apply G6_mono, G6_mono; exact Hab | exact HzG]. }
    assert (Hstrict : forall k, 1 <= k -> iter (f_omega_plus 2) k z < iter (fun y => G6 (G6 y)) k z).
    { intros k Hk. destruct k as [| m]; [lia |].
      assert (Hle : forall j, 2 <= iter (f_omega_plus 2) j z /\
                              iter (f_omega_plus 2) j z <= iter (fun y => G6 (G6 y)) j z).
      { intro j. induction j as [| j' [IH1 IH2]]; simpl.
        - lia.
        - split.
          + eapply Nat.le_trans; [exact IH1 | apply (fgh_ge_self _ (fOmegaMul_props 1 2))].
          + eapply Nat.le_trans; [apply (fgh_mono _ (fOmegaMul_props 1 2)); exact IH2 |].
            apply Nat.lt_le_incl, G6_sq_gt. lia. }
      destruct (Hle m) as [Hm1 Hm2]. simpl.
      eapply Nat.le_lt_trans; [apply (fgh_mono _ (fOmegaMul_props 1 2)); exact Hm2 |].
      apply G6_sq_gt. lia. }
    pose proof (Hstrict z ltac:(lia)).
    rewrite f_omega_plus_succ_eq. lia. }
  unfold G7 in *.
  replace (3 * z + 1) with (S (3 * z)) by lia.
  rewrite iter_succ.
  assert (Hge2 : 2 <= iter G6 (3 * z) 4) by (pose proof (G7_ge_3x (3 * z) ltac:(lia)); unfold G7 in *; lia).
  pose proof (G6_ge_3x (iter G6 (3 * z) 4) Hge2).
  lia.
Qed.

Lemma bb49_bootstrap :
  Reaches bb49 initConfig (Dcfg 8 (rep 3 4 (rep 3 5 (rep 3 6 (rep 12 7 []))))) 355.
Proof. unfold Reaches, initConfig, Dcfg, mkCfgR, rep. vm_compute. reflexivity. Qed.

Theorem bb49_halts_gt_f_omega_plus_4_12 :
  ValidTM 4 9 bb49 /\ exists t, HaltsIn bb49 initConfig t /\ f_omega_plus 4 12 < t.
Proof.
  split; [exact bb49_valid |].
  pose proof bb49_bootstrap as Hb.
  destruct (rule_D4_rep 3 8 (rep 3 5 (rep 3 6 (rep 12 7 []))) ltac:(lia)) as [t1 [H1 _]].
  set (N1 := iter G4 3 8).
  assert (HN1 : 2 <= N1).
  { unfold N1. assert (Hself : forall z, 2 <= z -> z <= G4 z) by (intros z Hz; pose proof (G4_inc z Hz); lia).
    simpl. pose proof (Hself 8 ltac:(lia)). pose proof (Hself (G4 8) ltac:(lia)). pose proof (Hself (G4 (G4 8)) ltac:(lia)). lia. }
  destruct (rule_D5_rep 3 N1 (rep 3 6 (rep 12 7 [])) HN1) as [t2 [H2 _]].
  set (N2 := iter G5 3 N1).
  assert (HN2 : 2 <= N2).
  { unfold N2. assert (Hself : forall z, 2 <= z -> z <= G5 z) by (intros z Hz; pose proof (G5_inc z Hz); lia).
    simpl. pose proof (Hself N1 HN1). pose proof (Hself (G5 N1) ltac:(lia)). pose proof (Hself (G5 (G5 N1)) ltac:(lia)). lia. }
  destruct (rule_D6_rep 3 N2 (rep 12 7 []) HN2) as [t3 [H3 _]].
  set (N3 := iter G6 3 N2).
  assert (HN3 : 37 <= N3).
  { unfold N3. simpl.
    pose proof (G6_ge_3x N2 HN2).
    pose proof (G6_ge_3x (G6 N2) ltac:(lia)).
    pose proof (G6_ge_3x (G6 (G6 N2)) ltac:(lia)).
    lia. }
  destruct (rule_D7_rep 12 N3 [] ltac:(lia)) as [t4 [H4 Hle4]].
  destruct (rule_D0 (iter G7 12 N3)) as [t5 [[cf [H5 Hst]] _]].
  assert (Hall : Reaches bb49 initConfig cf (355 + t1 + t2 + t3 + t4 + t5)).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hb | exact H1] | exact H2] | exact H3] | exact H4] | exact H5]. }
  assert (Hfb : f_omega_plus 4 12 < iter G7 12 N3).
  { assert (Harg : iter G7 12 37 <= iter G7 12 N3).
    { apply iter_mono_arg; [exact G7_mono | exact HN3]. }
    assert (Hind : forall k, 2 <= iter (f_omega_plus 3) k 12 /\
                             3 * iter (f_omega_plus 3) k 12 + 1 <= iter G7 k 37).
    { intro k. induction k as [| k' [IH1 IH2]]; simpl.
      - lia.
      - split.
        + eapply Nat.le_trans; [exact IH1 | apply (fgh_ge_self _ (fOmegaMul_props 1 3))].
        + eapply Nat.le_trans; [apply (G7_triple_gt _ IH1) | apply G7_mono; exact IH2]. }
    destruct (Hind 12) as [_ H12].
    rewrite f_omega_plus_succ_eq. lia. }
  specialize (Hle4 ltac:(lia)).
  exists (355 + t1 + t2 + t3 + t4 + t5).
  split; [exists cf; split; [exact Hall | exact Hst] | lia].
Qed.

Print Assumptions bb49_halts_gt_f_omega_plus_4_12.
