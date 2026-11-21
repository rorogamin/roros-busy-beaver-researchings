(*
  rocq/BB9_3.v
  Formal, axiom-free Rocq 9.1 proof of a NEW Busy Beaver Champion for BB(9, 3):
    TM: 2LI1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD2RA_1RC2LE1LG_0LA0LD1RH_1LD2RA2LG_1RZ2LA2LI_1RD1LI2LH
    Domain: BB(9, 3) (9 states, 3 symbols)
    Previous live wiki record: BB(9, 3) > f_{ω+2}^3(f_{ω+1}^2(f_ω(14)))
    Proved bound here: halts from blank tape in exact t steps with
      t > iter (f_omega_plus 2) 3 (iter (f_omega_plus 1) 2 (f_omega 16))
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Definition bb93 : TM := fun s sym =>
  match s, sym with
  (* State A (0): 2LI 1LE 2RA *)
  | 0, 0 => Some (mkAction 2 DL (Some 8))
  | 0, 1 => Some (mkAction 1 DL (Some 4))
  | 0, 2 => Some (mkAction 2 DR (Some 0))
  (* State B (1): 0LE 2LE 2RB *)
  | 1, 0 => Some (mkAction 0 DL (Some 4))
  | 1, 1 => Some (mkAction 2 DL (Some 4))
  | 1, 2 => Some (mkAction 2 DR (Some 1))
  (* State C (2): 1RF 1RC 2RB *)
  | 2, 0 => Some (mkAction 1 DR (Some 5))
  | 2, 1 => Some (mkAction 1 DR (Some 2))
  | 2, 2 => Some (mkAction 2 DR (Some 1))
  (* State D (3): 0RC 0LD 2RA *)
  | 3, 0 => Some (mkAction 0 DR (Some 2))
  | 3, 1 => Some (mkAction 0 DL (Some 3))
  | 3, 2 => Some (mkAction 2 DR (Some 0))
  (* State E (4): 1RC 2LE 1LG *)
  | 4, 0 => Some (mkAction 1 DR (Some 2))
  | 4, 1 => Some (mkAction 2 DL (Some 4))
  | 4, 2 => Some (mkAction 1 DL (Some 6))
  (* State F (5): 0LA 0LD 1RH *)
  | 5, 0 => Some (mkAction 0 DL (Some 0))
  | 5, 1 => Some (mkAction 0 DL (Some 3))
  | 5, 2 => Some (mkAction 1 DR (Some 7))
  (* State G (6): 1LD 2RA 2LG *)
  | 6, 0 => Some (mkAction 1 DL (Some 3))
  | 6, 1 => Some (mkAction 2 DR (Some 0))
  | 6, 2 => Some (mkAction 2 DL (Some 6))
  (* State H (7): 1RZ 2LA 2LI *)
  | 7, 0 => Some (mkAction 1 DR None)
  | 7, 1 => Some (mkAction 2 DL (Some 0))
  | 7, 2 => Some (mkAction 2 DL (Some 8))
  (* State I (8): 1RD 1LI 2LH *)
  | 8, 0 => Some (mkAction 1 DR (Some 3))
  | 8, 1 => Some (mkAction 1 DL (Some 8))
  | 8, 2 => Some (mkAction 2 DL (Some 7))
  | _, _ => None
  end.

Lemma bb93_valid : ValidTM 9 3 bb93.
Proof.
  split; intros s sym H1.
  - intro H2.
    destruct s as [|[|[|[|[|[|[|[|[|s]]]]]]]]]; try lia;
    destruct sym as [|[|[|sym]]]; try lia;
    simpl; try exact I; lia.
  - destruct s as [|[|[|[|[|[|[|[|[|s]]]]]]]]];
    try (destruct sym as [|[|[|sym]]]; try lia; reflexivity);
    reflexivity.
Qed.

Lemma step_D0_nil : forall a R,
  step bb93 (mkCfgR (Some 3) [] (0 :: a :: R)) = Some (mkCfgR (Some 2) [] (a :: R)).
Proof. reflexivity. Qed.

(* Basic loops *)

Lemma loop_A2_R : forall n L R,
  Reaches bb93 (mkCfgR (Some 0) L (rep n 2 R))
               (mkCfgR (Some 0) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb93 0 1 (Some 0) L 2 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_B2_R : forall n L R,
  Reaches bb93 (mkCfgR (Some 1) L (rep n 2 R))
               (mkCfgR (Some 1) (rep n 2 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb93 1 1 (Some 1) L 2 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_C1_R : forall n L R,
  Reaches bb93 (mkCfgR (Some 2) L (rep n 1 R))
               (mkCfgR (Some 2) (rep n 1 L) R) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_R bb93 2 0 (Some 2) L 1 _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_G2_L : forall n L R,
  Reaches bb93 (mkCfgR (Some 6) (rep n 2 L) (2 :: R))
               (mkCfgR (Some 6) L (2 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons bb93 6 1 2 2 (Some 6) _ _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_D1_L : forall n L b R,
  Reaches bb93 (mkCfgR (Some 3) (rep n 1 L) (1 :: b :: R))
               (mkCfgR (Some 3) L (1 :: rep n 0 (b :: R))) n.
Proof.
  induction n as [| k IH]; intros L b R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons_zero bb93 3 1 1 b (Some 3) _ _ eq_refl) |].
  unfold mkCfgR. simpl.
  replace (0 :: rep k 0 (b :: R)) with (rep k 0 (0 :: b :: R))
    by (rewrite rep_snoc_one; reflexivity).
  apply (IH L 0 (b :: R)).
Qed.

Lemma loop_I1_L : forall n L R,
  Reaches bb93 (mkCfgR (Some 8) (rep n 1 L) (1 :: R))
               (mkCfgR (Some 8) L (1 :: rep n 1 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons bb93 8 0 1 1 (Some 8) _ _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

Lemma loop_E1_L : forall n L R,
  Reaches bb93 (mkCfgR (Some 4) (rep n 1 L) (1 :: R))
               (mkCfgR (Some 4) L (1 :: rep n 2 R)) n.
Proof.
  induction n as [| k IH]; intros L R; [apply reaches_zero |].
  simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons bb93 4 1 1 1 (Some 4) _ _ eq_refl) |].
  rewrite <- rep_snoc_one. apply IH.
Qed.

(* Sweep E2 for k = 0: 1^a E> 2 R -> C> 1^(a+2) R *)
Lemma sweep_E2_zero : forall a j R,
  exists t, Reaches bb93
    (mkCfgR (Some 4) (rep a 1 []) (2 :: rep j 1 R))
    (mkCfgR (Some 2) [] (rep (a + 2 + j) 1 R)) t.
Proof.
  induction a as [| a' IH]; intros j R.
  - exists 3. simpl.
    eapply steps_succ; [apply (step_mkCfgR_L_nil bb93 4 0 2 (Some 6) _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil bb93 6 0 0 (Some 3) _ eq_refl) |].
    apply steps_one. apply (step_D0_nil _ _).
  - assert (Hs : Reaches bb93
      (mkCfgR (Some 4) (1 :: rep a' 1 []) (2 :: rep j 1 R))
      (mkCfgR (Some 4) (rep a' 1 []) (2 :: 1 :: rep j 1 R)) 3).
    { eapply steps_succ; [apply (step_mkCfgR_L_cons bb93 4 0 1 2 (Some 6) _ _ eq_refl) |].
      eapply steps_succ; [apply (step_mkCfgR_R bb93 6 1 (Some 0) _ 1 _ eq_refl) |].
      apply steps_one. apply (step_mkCfgR_L_cons bb93 0 0 2 1 (Some 4) _ _ eq_refl). }
    destruct (IH (S j) R) as [t2 H2].
    replace (S a' + 2 + j) with (a' + 2 + S j) by lia.
    exists (3 + t2). eapply reaches_trans; [exact Hs | exact H2].
Qed.

(* Sweep E2 for k >= 1: 1^a 2^(S k) E> 2 1^j R -> 1^1 2^(S k) B> 1^(a + j + 1) R *)
Lemma sweep_E2_pos : forall a k j R,
  exists t, Reaches bb93
    (mkCfgR (Some 4) (rep (S k) 2 (rep a 1 [])) (2 :: rep j 1 R))
    (mkCfgR (Some 1) (rep (S k) 2 [1]) (rep (a + j + 1) 1 R)) t.
Proof.
  induction a as [| a' IH]; intros k j R.
  - assert (H : Reaches bb93
      (mkCfgR (Some 4) (2 :: rep k 2 []) (2 :: rep j 1 R))
      (mkCfgR (Some 1) (rep (S k) 2 [1]) (rep (j + 1) 1 R))
      (1 + k + 1 + 1 + 1 + 1 + 1 + k)).
    { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|]|].
      - apply steps_one. apply (step_mkCfgR_L_cons bb93 4 0 2 2 (Some 6) _ _ eq_refl).
      - apply (loop_G2_L k [] (1 :: rep j 1 R)).
      - apply steps_one. apply (step_mkCfgR_L_nil bb93 6 1 2 (Some 6) _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_L_nil bb93 6 0 0 (Some 3) _ eq_refl).
      - apply steps_one. apply (step_D0_nil _ _).
      - apply steps_one. apply (step_mkCfgR_R bb93 2 0 (Some 2) [] 1 _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_R bb93 2 1 (Some 1) [1] 2 _ eq_refl).
      - replace (rep (S k) 2 [1]) with (rep k 2 [2; 1])
          by (replace (S k) with (k + 1) by lia; rewrite (rep_add k 1); reflexivity).
        replace (rep (j + 1) 1 R) with (1 :: rep j 1 R)
          by (replace (j + 1) with (S j) by lia; reflexivity).
        apply (loop_B2_R k [2; 1] (1 :: rep j 1 R)). }
    replace (0 + j + 1) with (j + 1) by lia.
    exists (1 + k + 1 + 1 + 1 + 1 + 1 + k). exact H.
  - assert (Hs : Reaches bb93
      (mkCfgR (Some 4) (2 :: rep k 2 (1 :: rep a' 1 [])) (2 :: rep j 1 R))
      (mkCfgR (Some 4) (2 :: rep k 2 (rep a' 1 [])) (2 :: 1 :: rep j 1 R))
      (1 + k + 1 + 1 + (S k) + 1)).
    { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
      - apply steps_one. apply (step_mkCfgR_L_cons bb93 4 0 2 2 (Some 6) _ _ eq_refl).
      - apply (loop_G2_L k (1 :: rep a' 1 []) (1 :: rep j 1 R)).
      - apply steps_one. apply (step_mkCfgR_L_cons bb93 6 1 1 2 (Some 6) _ _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_R bb93 6 1 (Some 0) (rep a' 1 []) 1 _ eq_refl).
      - apply (loop_A2_R (S k) (2 :: rep a' 1 []) (1 :: rep j 1 R)).
      - replace (rep (S k) 2 (2 :: rep a' 1 [])) with (2 :: 2 :: rep k 2 (rep a' 1 []))
          by (rewrite rep_snoc_one; reflexivity).
        apply steps_one. apply (step_mkCfgR_L_cons bb93 0 0 2 1 (Some 4) _ _ eq_refl). }
    destruct (IH k (S j) R) as [t2 H2].
    replace (S a' + j + 1) with (a' + S j + 1) by lia.
    exists (1 + k + 1 + 1 + (S k) + 1 + t2).
    eapply reaches_trans; [exact Hs | exact H2].
Qed.

(* Ackermann engine B3cfg a k R := 1^a 2^(S k) B> R *)
Definition B3cfg (a k : nat) (R : list nat) : Config :=
  mkCfgR (Some 1) (rep (S k) 2 (rep a 1 [])) R.

Fixpoint A3 (k : nat) : nat -> nat :=
  match k with
  | 0 => fun a => a + 2
  | S k' => fun a => iter (A3 k') (a + 1) 1
  end.

Lemma rule_B3_1 : forall k a R,
  exists t, Reaches bb93 (B3cfg a k (1 :: R)) (B3cfg (A3 k a) k R) t /\ A3 k a <= t.
Proof.
  induction k as [| k' IH]; intros a R.
  - unfold B3cfg. simpl.
    assert (H1 : Reaches bb93
      (mkCfgR (Some 1) (2 :: rep a 1 []) (1 :: R))
      (mkCfgR (Some 4) (rep a 1 []) (2 :: 2 :: R)) 1).
    { apply steps_one. apply (step_mkCfgR_L_cons bb93 1 1 2 1 (Some 4) _ _ eq_refl). }
    destruct (sweep_E2_zero a 0 (2 :: R)) as [t2 H2].
    assert (H3 : Reaches bb93
      (mkCfgR (Some 2) [] (rep (a + 2) 1 (2 :: R)))
      (mkCfgR (Some 1) (2 :: rep (a + 2) 1 []) R) ((a + 2) + 1)).
    { eapply reaches_trans.
      - apply (loop_C1_R (a + 2) [] (2 :: R)).
      - apply steps_one. apply (step_mkCfgR_R bb93 2 1 (Some 1) _ 2 _ eq_refl). }
    replace (a + 2 + 0) with (a + 2) in H2 by lia.
    exists (1 + t2 + ((a + 2) + 1)).
    split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | lia].
  - assert (Hrep : forall n x R0,
      exists t, Reaches bb93 (B3cfg x k' (rep n 1 R0)) (B3cfg (iter (A3 k') n x) k' R0) t /\
                (1 <= n -> iter (A3 k') n x <= t)).
    { induction n as [| p IHp]; intros x R0.
      - exists 0. split; [apply reaches_zero | lia].
      - destruct (IH x (rep p 1 R0)) as [t1 [H1 Hle1]].
        destruct (IHp (A3 k' x) R0) as [t2 [H2 Hle2]].
        replace (iter (A3 k') (S p) x) with (iter (A3 k') p (A3 k' x))
          by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
        exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
        intros _. destruct p as [| p']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia]. }
    assert (H1 : Reaches bb93 (B3cfg a (S k') (1 :: R))
      (mkCfgR (Some 4) (rep (S k') 2 (rep a 1 [])) (2 :: 2 :: R)) 1).
    { unfold B3cfg. apply steps_one. apply (step_mkCfgR_L_cons bb93 1 1 2 1 (Some 4) _ _ eq_refl). }
    destruct (sweep_E2_pos a k' 0 (2 :: R)) as [t2 H2].
    replace (a + 0 + 1) with (a + 1) in H2 by lia.
    destruct (Hrep (a + 1) 1 (2 :: R)) as [t3 [H3 Hle3]].
    assert (H4 : Reaches bb93 (B3cfg (iter (A3 k') (a + 1) 1) k' (2 :: R))
                              (B3cfg (iter (A3 k') (a + 1) 1) (S k') R) 1).
    { unfold B3cfg. apply steps_one. apply (step_mkCfgR_R bb93 1 1 (Some 1) _ 2 _ eq_refl). }
    exists (1 + t2 + t3 + 1).
    split.
    + eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4].
    + specialize (Hle3 ltac:(lia)). change (A3 (S k') a) with (iter (A3 k') (a + 1) 1). lia.
Qed.

Lemma rule_B3_1_rep : forall k n a R,
  exists t, Reaches bb93 (B3cfg a k (rep n 1 R)) (B3cfg (iter (A3 k) n a) k R) t /\
            (1 <= n -> iter (A3 k) n a <= t).
Proof.
  intros k n. induction n as [| p IH]; intros a R.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_B3_1 k a (rep p 1 R)) as [t1 [H1 Hle1]].
    destruct (IH (A3 k a) R) as [t2 [H2 Hle2]].
    replace (iter (A3 k) (S p) a) with (iter (A3 k) p (A3 k a))
      by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
    intros _. destruct p as [| p']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

(* Exit B3cfg a k (0 :: R) -> F> R *)
Fixpoint G0_aux (k : nat) : nat -> nat :=
  match k with
  | 0 => fun a => a + 3
  | S k' => fun a => G0_aux k' (iter (A3 k') (a + 1) 1)
  end.

Lemma rule_B3_0 : forall k a b R,
  exists t, Reaches bb93 (B3cfg a k (0 :: b :: R))
    (mkCfgR (Some 5) (rep (G0_aux k a) 1 []) (b :: R)) t /\ G0_aux k a <= t.
Proof.
  induction k as [| k' IH]; intros a b R.
  - unfold B3cfg. simpl.
    assert (H1 : Reaches bb93
      (mkCfgR (Some 1) (2 :: rep a 1 []) (0 :: b :: R))
      (mkCfgR (Some 4) (rep a 1 []) (2 :: 0 :: b :: R)) 1).
    { apply steps_one. apply (step_mkCfgR_L_cons_zero bb93 1 2 0 b (Some 4) _ _ eq_refl). }
    destruct (sweep_E2_zero a 0 (0 :: b :: R)) as [t2 H2].
    assert (H3 : Reaches bb93
      (mkCfgR (Some 2) [] (rep (a + 2) 1 (0 :: b :: R)))
      (mkCfgR (Some 5) (rep (a + 3) 1 []) (b :: R)) ((a + 2) + 1)).
    { eapply reaches_trans.
      - apply (loop_C1_R (a + 2) [] (0 :: b :: R)).
      - replace (rep (a + 3) 1 []) with (1 :: rep (a + 2) 1 [])
          by (replace (a + 3) with (S (a + 2)) by lia; reflexivity).
        apply steps_one. apply (step_mkCfgR_R bb93 2 0 (Some 5) _ 0 _ eq_refl). }
    replace (a + 2 + 0) with (a + 2) in H2 by lia.
    exists (1 + t2 + ((a + 2) + 1)).
    split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | lia].
  - assert (H1 : Reaches bb93 (B3cfg a (S k') (0 :: b :: R))
      (mkCfgR (Some 4) (rep (S k') 2 (rep a 1 [])) (2 :: 0 :: b :: R)) 1).
    { unfold B3cfg. apply steps_one. apply (step_mkCfgR_L_cons_zero bb93 1 2 0 b (Some 4) _ _ eq_refl). }
    destruct (sweep_E2_pos a k' 0 (0 :: b :: R)) as [t2 H2].
    replace (a + 0 + 1) with (a + 1) in H2 by lia.
    destruct (rule_B3_1_rep k' (a + 1) 1 (0 :: b :: R)) as [t3 [H3 _]].
    destruct (IH (iter (A3 k') (a + 1) 1) b R) as [t4 [H4 Hle4]].
    exists (1 + t2 + t3 + t4).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] |].
    change (G0_aux (S k') a) with (G0_aux k' (iter (A3 k') (a + 1) 1)). lia.
Qed.

(* F> 0 rule: 1^(m+1) F> 0 b R -> 1^(G0 m) F> b R *)
Definition Fcfg (m : nat) (R : list nat) : Config :=
  mkCfgR (Some 5) (rep m 1 []) R.

Definition G0 (m : nat) : nat :=
  match m with
  | 0 => 1
  | 1 => 3
  | S (S m') => G0_aux m' (A3 m' 1)
  end.

Lemma rule_F0 : forall m b R, 1 <= m ->
  exists t, Reaches bb93 (Fcfg m (0 :: b :: R)) (Fcfg (G0 m) (b :: R)) t /\ G0 m <= t.
Proof.
  intros m b R Hm.
  destruct m as [| [| m']]; [lia | |].
  - (* m = 1: 1^1 F> 0 b R -> 1^3 F> b R in 5 steps *)
    unfold Fcfg. simpl. exists 5. split; [| lia].
    eapply steps_succ; [apply (step_mkCfgR_L_cons_zero bb93 5 1 0 b (Some 0) _ _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil bb93 0 0 1 (Some 4) _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R bb93 4 0 (Some 2) [] 0 _ eq_refl) |].
    eapply steps_succ; [apply (step_mkCfgR_R bb93 2 0 (Some 2) [1] 1 _ eq_refl) |].
    apply steps_one. reflexivity.
  - (* m = S (S m'): 1^(m'+2) F> 0 b R -> B3cfg 1 m' (1 :: 0 :: b :: R) *)
    assert (H1 : Reaches bb93 (Fcfg (S (S m')) (0 :: b :: R))
      (B3cfg 1 m' (1 :: 0 :: b :: R)) (1 + 1 + m' + 1 + 1 + 1 + m')).
    { unfold Fcfg, B3cfg.
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|].
      - apply steps_one. apply (step_mkCfgR_L_cons_zero bb93 5 1 0 b (Some 0) _ _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_L_cons bb93 0 0 1 1 (Some 4) _ _ eq_refl).
      - apply (loop_E1_L m' [] (1 :: 0 :: b :: R)).
      - apply steps_one. apply (step_mkCfgR_L_nil bb93 4 1 1 (Some 4) _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_R bb93 4 0 (Some 2) [] 0 _ eq_refl).
      - apply steps_one. apply (step_mkCfgR_R bb93 2 1 (Some 1) [1] 2 _ eq_refl).
      - change (rep 1 1 []) with [1].
        replace (rep (S m') 2 [1]) with (rep m' 2 [2; 1])
          by (replace (S m') with (m' + 1) by lia; rewrite (rep_add m' 1); reflexivity).
        apply (loop_B2_R m' [2; 1] (1 :: 0 :: b :: R)). }
    destruct (rule_B3_1 m' 1 (0 :: b :: R)) as [t2 [H2 _]].
    destruct (rule_B3_0 m' (A3 m' 1) b R) as [t3 [H3 Hle3]].
    exists ((1 + 1 + m' + 1 + 1 + 1 + m') + t2 + t3).
    split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | simpl; lia].
Qed.

(* Growth of A3 and G0 *)
Lemma A3_ge_succ : forall k a, a + 2 <= A3 k a.
Proof.
  induction k as [| k' IH]; intro a; [simpl; lia |].
  simpl. assert (Hge : forall n, 2 * n + 1 <= iter (A3 k') n 1).
  { induction n as [| p IHp]; [simpl; lia |].
    simpl. pose proof (IH (iter (A3 k') p 1)). lia. }
  pose proof (Hge (a + 1)). lia.
Qed.

Lemma A3_mono : forall k x y, x <= y -> A3 k x <= A3 k y.
Proof.
  induction k as [| k' IH]; intros x y Hxy; [simpl; lia |].
  simpl. assert (Hstep : forall n, iter (A3 k') n 1 <= iter (A3 k') (S n) 1).
  { intro n. simpl. pose proof (A3_ge_succ k' (iter (A3 k') n 1)). lia. }
  assert (Hmn : forall a b, a <= b -> iter (A3 k') a 1 <= iter (A3 k') b 1).
  { intros a b Hab. induction Hab; [lia | eapply Nat.le_trans; [exact IHHab | apply Hstep]]. }
  apply Hmn. lia.
Qed.

Lemma A3_ge_double : forall k a, 1 <= k -> 2 * a + 1 <= A3 k a.
Proof.
  intros k a Hk. destruct k as [| k']; [lia |].
  simpl. assert (Hge : forall n, 2 * n + 1 <= iter (A3 k') n 1).
  { induction n as [| p IHp]; [simpl; lia |].
    simpl. pose proof (A3_ge_succ k' (iter (A3 k') p 1)). lia. }
  pose proof (Hge (a + 1)). lia.
Qed.

Lemma A3_ge_2_fFin : forall k a, 2 * fFin k a <= A3 k (2 * a).
Proof.
  induction k as [| k' IH]; intro a.
  - simpl. lia.
  - change (2 * iter (fFin k') a a <= A3 (S k') (2 * a)).
    assert (Hiter : forall j, 2 * iter (fFin k') j a <= iter (A3 k') j (2 * a)).
    { induction j as [| j' IHj]; [simpl; lia |].
      simpl. eapply Nat.le_trans; [| apply A3_mono; exact IHj].
      apply IH. }
    assert (Hinit : 2 * a + 1 <= iter (A3 k') a 1).
    { clear Hiter. induction a as [| p IHp]; [simpl; lia |].
      simpl. pose proof (A3_ge_succ k' (iter (A3 k') p 1)). lia. }
    change (2 * iter (fFin k') a a <= iter (A3 k') (2 * a + 1) 1).
    replace (2 * a + 1) with (S (a + a)) by lia.
    rewrite iter_succ, iter_add.
    pose proof (A3_ge_succ k' (iter (A3 k') a (iter (A3 k') a 1))) as Hd.
    assert (Harg : iter (A3 k') a (2 * a) <= iter (A3 k') a (iter (A3 k') a 1)).
    { apply iter_mono_arg; [exact (A3_mono k') | lia]. }
    pose proof (Hiter a). lia.
Qed.

Lemma A3_one_ge : forall k, 1 <= k -> 2 * k + 1 <= A3 k 1.
Proof.
  induction k as [| k' IH]; intro Hk; [lia |].
  destruct k' as [| k''].
  - simpl. lia.
  - change (2 * S (S k'') + 1 <= A3 (S k'') (A3 (S k'') 1)).
    pose proof (IH ltac:(lia)).
    pose proof (A3_ge_double (S k'') (A3 (S k'') 1) ltac:(lia)). lia.
Qed.

Lemma G0_aux_ge : forall k a, a + 3 <= G0_aux k a.
Proof.
  induction k as [| k' IH]; intro a; [simpl; lia |].
  change (a + 3 <= G0_aux k' (iter (A3 k') (a + 1) 1)).
  pose proof (IH (iter (A3 k') (a + 1) 1)).
  assert (Hge : 2 * (a + 1) + 1 <= iter (A3 k') (a + 1) 1).
  { clear IH H. induction (a + 1) as [| p IHp]; [simpl; lia |].
    simpl. pose proof (A3_ge_succ k' (iter (A3 k') p 1)). lia. }
  lia.
Qed.

Lemma G0_ge_succ : forall m, 1 <= m -> m + 2 <= G0 m.
Proof.
  intros m Hm. destruct m as [| [| m']]; [lia | simpl; lia |].
  simpl. pose proof (G0_aux_ge m' (A3 m' 1)).
  assert (H1 : m' + 1 <= A3 m' 1).
  { clear H. induction m' as [| j IH]; [simpl; lia |].
    simpl. pose proof (A3_ge_succ j (A3 j 1)). lia. }
  lia.
Qed.

Lemma G0_gt_2_f_omega : forall k, 1 <= k -> 2 * f_omega k < G0 (k + 2).
Proof.
  intros k Hk.
  replace (k + 2) with (S (S k)) by lia.
  change (2 * f_omega k < G0_aux k (A3 k 1)).
  destruct k as [| k']; [lia |].
  change (2 * f_omega (S k') < G0_aux k' (iter (A3 k') (A3 (S k') 1 + 1) 1)).
  pose proof (G0_aux_ge k' (iter (A3 k') (A3 (S k') 1 + 1) 1)) as Hg.
  assert (Hstep : forall n, iter (A3 k') n 1 <= iter (A3 k') (S n) 1).
  { intro n. simpl. pose proof (A3_ge_succ k' (iter (A3 k') n 1)). lia. }
  assert (Hmn : forall a b, a <= b -> iter (A3 k') a 1 <= iter (A3 k') b 1).
  { intros a b Hab. induction Hab; [lia | eapply Nat.le_trans; [exact IHHab | apply Hstep]]. }
  pose proof (A3_one_ge (S k') ltac:(lia)) as H1.
  assert (Hge : A3 (S k') (2 * S k') <= iter (A3 k') (A3 (S k') 1 + 1) 1).
  { change (iter (A3 k') (2 * S k' + 1) 1 <= iter (A3 k') (A3 (S k') 1 + 1) 1).
    apply Hmn. lia. }
  pose proof (A3_ge_2_fFin (S k') (S k')) as Hf.
  change (2 * fFin (S k') (S k') < G0_aux k' (iter (A3 k') (A3 (S k') 1 + 1) 1)).
  lia.
Qed.

(* F> 0^n, F> 1, F> 2, and Halt rules *)
Lemma rule_F0_rep : forall n m b R, 1 <= m ->
  exists t, Reaches bb93 (Fcfg m (rep n 0 (b :: R))) (Fcfg (iter G0 n m) (b :: R)) t /\
            (1 <= n -> iter G0 n m <= t).
Proof.
  induction n as [| p IH]; intros m b R Hm.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_F0 m (match p with 0 => b | S _ => 0 end)
                (match p with 0 => R | S p' => rep p' 0 (b :: R) end) Hm) as [t1 [H1 Hle1]].
    assert (Hgm : 1 <= G0 m) by (pose proof (G0_ge_succ m Hm); lia).
    destruct (IH (G0 m) b R Hgm) as [t2 [H2 Hle2]].
    replace (iter G0 (S p) m) with (iter G0 p (G0 m))
      by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split.
    + destruct p as [| p']; simpl in *; eapply reaches_trans; [exact H1 | exact H2 | exact H1 | exact H2].
    + intros _. destruct p as [| p']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

Definition G1 (m : nat) : nat := iter G0 m 1.

Lemma rule_F1 : forall m b R, 1 <= m ->
  exists t, Reaches bb93 (Fcfg m (1 :: b :: R)) (Fcfg (G1 m) (b :: R)) t /\ G1 m <= t.
Proof.
  intros m b R Hm. destruct m as [| m']; [lia |].
  assert (H1 : Reaches bb93 (Fcfg (S m') (1 :: b :: R)) (Fcfg 1 (rep (S m') 0 (b :: R))) (1 + m' + 1 + 1 + 1)).
  { unfold Fcfg.
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|].
    - apply steps_one. apply (step_mkCfgR_L_cons_zero bb93 5 1 1 b (Some 3) _ _ eq_refl).
    - apply (loop_D1_L m' [] 0 (b :: R)).
    - rewrite rep_snoc_one. apply steps_one. apply (step_mkCfgR_L_nil_zero bb93 3 1 0 (Some 3) _ eq_refl).
    - apply steps_one. apply (step_D0_nil _ _).
    - replace (0 :: rep m' 0 (b :: R)) with (rep (S m') 0 (b :: R)) by reflexivity.
      apply steps_one. apply (step_mkCfgR_R bb93 2 0 (Some 5) [] 0 _ eq_refl). }
  destruct (rule_F0_rep (S m') 1 b R ltac:(lia)) as [t2 [H2 Hle2]].
  exists ((1 + m' + 1 + 1 + 1) + t2).
  split; [eapply reaches_trans; [exact H1 | exact H2] | unfold G1; specialize (Hle2 ltac:(lia)); lia].
Qed.

Lemma rule_F1_rep : forall n m b R, 1 <= m ->
  exists t, Reaches bb93 (Fcfg m (rep n 1 (b :: R))) (Fcfg (iter G1 n m) (b :: R)) t /\
            (1 <= n -> iter G1 n m <= t).
Proof.
  induction n as [| p IH]; intros m b R Hm.
  - exists 0. split; [apply reaches_zero | lia].
  - destruct (rule_F1 m (match p with 0 => b | S _ => 1 end)
                (match p with 0 => R | S p' => rep p' 1 (b :: R) end) Hm) as [t1 [H1 Hle1]].
    assert (Hgm : 1 <= G1 m).
    { unfold G1. clear IH H1 Hle1. induction m as [| k IHk]; [lia |].
      destruct k as [| k']; [simpl; lia |].
      pose proof (IHk ltac:(lia)) as Hk1.
      change (1 <= G0 (iter G0 (S k') 1)). pose proof (G0_ge_succ (iter G0 (S k') 1) Hk1). lia. }
    destruct (IH (G1 m) b R Hgm) as [t2 [H2 Hle2]].
    replace (iter G1 (S p) m) with (iter G1 p (G1 m))
      by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
    exists (t1 + t2). split.
    + destruct p as [| p']; simpl in *; eapply reaches_trans; [exact H1 | exact H2 | exact H1 | exact H2].
    + intros _. destruct p as [| p']; [simpl in *; lia | specialize (Hle2 ltac:(lia)); lia].
Qed.

Definition G2 (m : nat) : nat := iter G1 m 3.

Lemma rule_F2_step : forall m R, 1 <= m ->
  exists t, Reaches bb93 (Fcfg m (2 :: 2 :: R)) (Fcfg (G2 m) (2 :: R)) t /\ G2 m <= t.
Proof.
  intros m R Hm. destruct m as [| m']; [lia |].
  assert (H1 : Reaches bb93 (Fcfg (S m') (2 :: 2 :: R))
    (Fcfg 1 (0 :: rep (S m') 1 (2 :: R))) (1 + 1 + (S m') + 1 + 1 + 1 + 1 + 1 + 1)).
  { unfold Fcfg.
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|]|]|].
    - apply steps_one. apply (step_mkCfgR_R bb93 5 0 (Some 7) _ 2 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_L_cons bb93 7 1 1 2 (Some 8) _ _ eq_refl).
    - apply (loop_I1_L (S m') [] (2 :: R)).
    - apply steps_one. apply (step_mkCfgR_L_nil bb93 8 0 1 (Some 8) _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_R bb93 8 0 (Some 3) [] 0 _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_L_cons_zero bb93 3 1 1 1 (Some 3) _ _ eq_refl).
    - apply steps_one. apply (step_mkCfgR_L_nil_zero bb93 3 1 0 (Some 3) _ eq_refl).
    - apply steps_one. apply (step_D0_nil _ _).
    - apply steps_one. apply (step_mkCfgR_R bb93 2 0 (Some 5) [] 0 _ eq_refl). }
  destruct (rule_F0 1 1 (rep m' 1 (2 :: R)) ltac:(lia)) as [t2 [H2 _]].
  destruct (rule_F1_rep (S m') 3 2 R ltac:(lia)) as [t3 [H3 Hle3]].
  exists ((1 + 1 + (S m') + 1 + 1 + 1 + 1 + 1 + 1) + t2 + t3).
  split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | unfold G2; specialize (Hle3 ltac:(lia)); lia].
Qed.

Lemma rule_F2_halt : forall m, exists t, HaltsIn bb93 (Fcfg m [2]) t /\ t = 2.
Proof.
  intro m. exists 2. split; [| reflexivity].
  exists (mkCfgR None (1 :: 1 :: rep m 1 []) []). split; [| reflexivity].
  eapply steps_succ; [apply (step_mkCfgR_R bb93 5 0 (Some 7) _ 2 _ eq_refl) |].
  apply steps_one. apply (step_mkCfgR_R_nil bb93 7 0 None _ eq_refl).
Qed.

Lemma A3_step_k : forall k a, A3 k a <= A3 (S k) a.
Proof.
  intros k a.
  assert (Hge : a <= iter (A3 k) a 1).
  { induction a as [| p IHp]; [simpl; lia |].
    simpl. pose proof (A3_ge_succ k (iter (A3 k) p 1)). lia. }
  change (A3 k a <= iter (A3 k) (a + 1) 1). replace (a + 1) with (S a) by lia. simpl. apply A3_mono. exact Hge.
Qed.

Lemma G0_aux_mono_a : forall k x y, x <= y -> G0_aux k x <= G0_aux k y.
Proof.
  induction k as [| k' IH]; intros x y Hxy; [simpl; lia |].
  simpl. apply IH.
  assert (Hstep : forall n, iter (A3 k') n 1 <= iter (A3 k') (S n) 1).
  { intro n. simpl. pose proof (A3_ge_succ k' (iter (A3 k') n 1)). lia. }
  assert (Hmn : forall a b, a <= b -> iter (A3 k') a 1 <= iter (A3 k') b 1).
  { intros a b Hab. induction Hab; [lia | eapply Nat.le_trans; [exact IHHab | apply Hstep]]. }
  apply Hmn. lia.
Qed.

Lemma G0_aux_step_k : forall k a, G0_aux k a <= G0_aux (S k) a.
Proof.
  intros k a. change (G0_aux k a <= G0_aux k (iter (A3 k) (a + 1) 1)).
  apply G0_aux_mono_a.
  assert (Hge : a + 1 <= iter (A3 k) (a + 1) 1).
  { induction (a + 1) as [| p IHp]; [simpl; lia |].
    simpl. pose proof (A3_ge_succ k (iter (A3 k) p 1)). lia. }
  lia.
Qed.

Lemma G0_mono : forall x y, x <= y -> G0 x <= G0 y.
Proof.
  intros x y Hxy. induction Hxy; [lia |].
  eapply Nat.le_trans; [exact IHHxy |].
  destruct m as [| [| m']]; simpl; [lia | pose proof (G0_aux_ge 0 (A3 0 1)); lia |].
  eapply Nat.le_trans; [apply G0_aux_mono_a; apply A3_step_k | apply G0_aux_step_k].
Qed.

Lemma G1_mono : forall x y, x <= y -> G1 x <= G1 y.
Proof.
  intros x y Hxy. unfold G1.
  assert (Hge1 : forall n, 1 <= iter G0 n 1).
  { induction n as [| p IHp]; [simpl; lia |].
    simpl. pose proof (G0_ge_succ (iter G0 p 1) IHp). lia. }
  assert (Hstep : forall n, iter G0 n 1 <= iter G0 (S n) 1).
  { intro n. simpl. pose proof (G0_ge_succ (iter G0 n 1) (Hge1 n)). lia. }
  induction Hxy; [lia | eapply Nat.le_trans; [exact IHHxy | apply Hstep]].
Qed.

Lemma G1_ge_double : forall m, 1 <= m -> 2 * m + 1 <= G1 m.
Proof.
  intros m Hm. unfold G1. induction m as [| p IHp]; [lia |].
  destruct p as [| p'].
  - simpl. lia.
  - pose proof (IHp ltac:(lia)) as Hp.
    change (2 * S (S p') + 1 <= G0 (iter G0 (S p') 1)).
    pose proof (G0_ge_succ (iter G0 (S p') 1) ltac:(lia)). lia.
Qed.

Lemma G2_mono : forall x y, x <= y -> G2 x <= G2 y.
Proof.
  intros x y Hxy. unfold G2.
  assert (Hge1 : forall n, 1 <= iter G1 n 3).
  { induction n as [| p IHp]; [simpl; lia |].
    simpl. pose proof (G1_ge_double (iter G1 p 3) IHp). lia. }
  assert (Hstep : forall n, iter G1 n 3 <= iter G1 (S n) 3).
  { intro n. simpl. pose proof (G1_ge_double (iter G1 n 3) (Hge1 n)). lia. }
  induction Hxy; [lia | eapply Nat.le_trans; [exact IHHxy | apply Hstep]].
Qed.

Lemma G1_gt_2_f_omega_plus_1 : forall m, 2 <= m -> 2 * f_omega_plus 1 m < G1 (2 * m).
Proof.
  intros m Hm.
  rewrite f_omega_plus_succ_eq.
  assert (Hiter : forall j, 2 <= iter f_omega j m /\ 2 * iter f_omega j m <= iter G0 j (2 * m)).
  { induction j as [| j' [IH1 IH2]]; [simpl; lia |].
    simpl. split.
    - pose proof (fgh_ge_self _ (fOmegaMul_props 1 0) (iter f_omega j' m)).
      change (iter f_omega j' m <= f_omega (iter f_omega j' m)) in H. lia.
    - assert (H2 : iter f_omega j' m + 2 <= iter G0 j' (2 * m)) by lia.
      eapply Nat.le_trans; [| apply G0_mono; exact H2].
      pose proof (G0_gt_2_f_omega (iter f_omega j' m) ltac:(lia)). lia. }
  assert (Hinit : 2 * m <= iter G0 m 1).
  { clear Hiter. pose proof (G1_ge_double m ltac:(lia)) as Hg. unfold G1 in Hg. lia. }
  unfold G1.
  replace (2 * m) with (m + m) by lia.
  rewrite iter_add.
  assert (Harg : iter G0 m (2 * m) <= iter G0 m (iter G0 m 1)).
  { apply iter_mono_arg; [exact G0_mono | exact Hinit]. }
  destruct (Hiter m) as [_ Hm2].
  (* Need strict < : use G0 (y + 2) > 2 * f_omega y at the last step! *)
  destruct m as [| m']; [lia |].
  destruct (Hiter m') as [Hm1' Hm2'].
  assert (Hstrict : 2 * iter f_omega (S m') (S m') < iter G0 (S m') (2 * S m')).
  { simpl.
    assert (H2 : iter f_omega m' (S m') + 2 <= iter G0 m' (2 * S m')) by lia.
    eapply Nat.lt_le_trans; [apply (G0_gt_2_f_omega (iter f_omega m' (S m')) ltac:(lia)) | apply G0_mono; exact H2]. }
  change (2 * iter f_omega (S m') (S m') < iter G0 (S m') (iter G0 (S m') 1)). lia.
Qed.

Lemma G2_gt_2_f_omega_plus_2 : forall m, 2 <= m -> 2 * f_omega_plus 2 m < G2 (2 * m).
Proof.
  intros m Hm.
  rewrite f_omega_plus_succ_eq.
  assert (Hiter : forall j, 2 <= iter (f_omega_plus 1) j m /\
                            2 * iter (f_omega_plus 1) j m <= iter G1 j (2 * m)).
  { induction j as [| j' [IH1 IH2]]; [simpl; lia |].
    simpl. split.
    - pose proof (fgh_ge_self _ (fOmegaMul_props 1 1) (iter (f_omega_plus 1) j' m)).
      change (iter (f_omega_plus 1) j' m <= f_omega_plus 1 (iter (f_omega_plus 1) j' m)) in H. lia.
    - eapply Nat.le_trans; [| apply G1_mono; exact IH2].
      pose proof (G1_gt_2_f_omega_plus_1 (iter (f_omega_plus 1) j' m) IH1). lia. }
  assert (Hinit : 2 * m <= iter G1 m 3).
  { clear Hiter Hm. induction m as [| p IHp]; [simpl; lia |].
    destruct p as [| p'].
    - change (2 * 1 <= G1 3). pose proof (G1_ge_double 3 ltac:(lia)). lia.
    - change (2 * S (S p') <= G1 (iter G1 (S p') 3)).
      pose proof (G1_ge_double (iter G1 (S p') 3) ltac:(lia)). lia. }
  unfold G2.
  replace (2 * m) with (m + m) by lia.
  rewrite iter_add.
  assert (Harg : iter G1 m (2 * m) <= iter G1 m (iter G1 m 3)).
  { apply iter_mono_arg; [exact G1_mono | exact Hinit]. }
  destruct m as [| m']; [lia |].
  destruct (Hiter m') as [Hm1' Hm2'].
  assert (Hstrict : 2 * iter (f_omega_plus 1) (S m') (S m') < iter G1 (S m') (2 * S m')).
  { simpl.
    eapply Nat.lt_le_trans; [apply (G1_gt_2_f_omega_plus_1 (iter (f_omega_plus 1) m' (S m')) Hm1') | apply G1_mono; exact Hm2']. }
  lia.
Qed.

Lemma G2_chain_gt : forall X Y, 2 <= X -> 2 * X < Y ->
  iter (f_omega_plus 2) 3 (iter (f_omega_plus 1) 2 X) < G2 (G2 (G2 (G1 (G1 Y)))).
Proof.
  intros X Y HX HXY.
  assert (H1 : 2 * f_omega_plus 1 X < G1 Y).
  { eapply Nat.lt_le_trans; [apply (G1_gt_2_f_omega_plus_1 X HX) | apply G1_mono; lia]. }
  set (X1 := f_omega_plus 1 X).
  assert (HX1 : 2 <= X1) by (unfold X1; pose proof (fgh_ge_self _ (fOmegaMul_props 1 1) X) as H; change (X <= f_omega_plus 1 X) in H; lia).
  assert (H2 : 2 * f_omega_plus 1 X1 < G1 (G1 Y)).
  { eapply Nat.lt_le_trans; [apply (G1_gt_2_f_omega_plus_1 X1 HX1) | apply G1_mono; lia]. }
  set (X2 := f_omega_plus 1 X1).
  assert (HX2 : 2 <= X2) by (unfold X2; pose proof (fgh_ge_self _ (fOmegaMul_props 1 1) X1) as H; change (X1 <= f_omega_plus 1 X1) in H; lia).
  assert (H3 : 2 * f_omega_plus 2 X2 < G2 (G1 (G1 Y))).
  { eapply Nat.lt_le_trans; [apply (G2_gt_2_f_omega_plus_2 X2 HX2) | apply G2_mono; lia]. }
  set (X3 := f_omega_plus 2 X2).
  assert (HX3 : 2 <= X3) by (unfold X3; pose proof (fgh_ge_self _ (fOmegaMul_props 1 2) X2) as H; change (X2 <= f_omega_plus 2 X2) in H; lia).
  assert (H4 : 2 * f_omega_plus 2 X3 < G2 (G2 (G1 (G1 Y)))).
  { eapply Nat.lt_le_trans; [apply (G2_gt_2_f_omega_plus_2 X3 HX3) | apply G2_mono; lia]. }
  set (X4 := f_omega_plus 2 X3).
  assert (HX4 : 2 <= X4) by (unfold X4; pose proof (fgh_ge_self _ (fOmegaMul_props 1 2) X3) as H; change (X3 <= f_omega_plus 2 X3) in H; lia).
  assert (H5 : 2 * f_omega_plus 2 X4 < G2 (G2 (G2 (G1 (G1 Y))))).
  { eapply Nat.lt_le_trans; [apply (G2_gt_2_f_omega_plus_2 X4 HX4) | apply G2_mono; lia]. }
  unfold X4, X3, X2, X1 in H5. simpl. lia.
Qed.

Lemma bb93_bootstrap : Reaches bb93 initConfig (Fcfg 3 [1; 1; 1; 2; 2; 2; 2]) 44.
Proof. unfold Reaches, initConfig, Fcfg, mkCfgR, rep. vm_compute. reflexivity. Qed.

Lemma G1_3_eq : G1 3 = G0 16.
Proof.
  unfold G1.
  rewrite iter_succ, iter_succ, iter_succ, iter_zero.
  assert (H1 : G0 1 = 3) by reflexivity.
  assert (H3 : G0 3 = 16) by (vm_compute; reflexivity).
  rewrite H1, H3. reflexivity.
Qed.

Lemma f_omega_ge_self_n : forall n, n <= f_omega n.
Proof.
  intro n. pose proof (fgh_ge_self _ (fOmegaMul_props 1 0) n) as H.
  change (n <= f_omega n) in H. exact H.
Qed.

Theorem bb93_halts_gt_f_omega_plus_2_3_f_omega_plus_1_2_f_omega_14 :
  ValidTM 9 3 bb93 /\
  exists t, HaltsIn bb93 initConfig t /\
            iter (f_omega_plus 2) 3 (iter (f_omega_plus 1) 2 (f_omega 14)) < t.
Proof.
  split; [exact bb93_valid |].
  pose proof bb93_bootstrap as Hb.
  destruct (rule_F1_rep 3 3 2 [2; 2; 2] ltac:(lia)) as [t1 [H1 _]].
  set (M1 := iter G1 3 3).
  assert (HM1 : 1 <= M1).
  { unfold M1. rewrite iter_succ, iter_succ, iter_succ, iter_zero.
    pose proof (G1_ge_double 3 ltac:(lia)).
    pose proof (G1_ge_double (G1 3) ltac:(lia)).
    pose proof (G1_ge_double (G1 (G1 3)) ltac:(lia)). lia. }
  destruct (rule_F2_step M1 [2; 2] HM1) as [t2 [H2 _]].
  assert (HM2 : 1 <= G2 M1).
  { pose proof (G2_mono 1 M1 HM1).
    assert (H11 : 1 <= G2 1) by (unfold G2; rewrite iter_succ, iter_zero; pose proof (G1_ge_double 3 ltac:(lia)); lia). lia. }
  destruct (rule_F2_step (G2 M1) [2] HM2) as [t3 [H3 _]].
  assert (HM3 : 1 <= G2 (G2 M1)).
  { pose proof (G2_mono 1 (G2 M1) HM2).
    assert (H11 : 1 <= G2 1) by (unfold G2; rewrite iter_succ, iter_zero; pose proof (G1_ge_double 3 ltac:(lia)); lia). lia. }
  destruct (rule_F2_step (G2 (G2 M1)) [] HM3) as [t4 [H4 Hle4]].
  destruct (rule_F2_halt (G2 (G2 (G2 M1)))) as [t5 [[cf [H5 Hst]] _]].
  assert (Hall : Reaches bb93 initConfig cf (44 + t1 + t2 + t3 + t4 + t5)).
  { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact Hb | exact H1] | exact H2] | exact H3] | exact H4] | exact H5]. }
  assert (HX : 2 <= f_omega 14) by (pose proof (f_omega_ge_self_n 14); lia).
  assert (HXY : 2 * f_omega 14 < G1 3).
  { rewrite G1_3_eq. apply (G0_gt_2_f_omega 14 ltac:(lia)). }
  pose proof (G2_chain_gt (f_omega 14) (G1 3) HX HXY) as Hfb.
  assert (HMeq : M1 = G1 (G1 (G1 3))) by (unfold M1; rewrite iter_succ, iter_succ, iter_succ, iter_zero; reflexivity).
  rewrite HMeq in Hle4.
  exists (44 + t1 + t2 + t3 + t4 + t5).
  split; [exists cf; split; [exact Hall | exact Hst] | lia].
Qed.

Print Assumptions bb93_halts_gt_f_omega_plus_2_3_f_omega_plus_1_2_f_omega_14.
