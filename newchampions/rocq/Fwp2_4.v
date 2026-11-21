(*
  rocq/Fwp2_4.v
  Reusable, axiom-free Rocq 9.1 formalization of the 8-state 4-symbol f_{ω^2} core (A..H).
  Powers BB(10,4), BB(12..18,4), and BB(11,5) (with A<->B swap).
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

Record Fwp2_4Core (tm : TM) : Prop := mkFwp2_4Core {
  f4_A0 : tm 0 0 = Some (mkAction 1 DL (Some 3));
  f4_A1 : tm 0 1 = Some (mkAction 2 DR (Some 6));
  f4_A2 : tm 0 2 = Some (mkAction 2 DL (Some 0));
  f4_A3 : tm 0 3 = Some (mkAction 3 DL (Some 6));
  f4_B1 : tm 1 1 = Some (mkAction 2 DL (Some 7));
  f4_B2 : tm 1 2 = Some (mkAction 2 DR (Some 1));
  f4_B3 : tm 1 3 = Some (mkAction 2 DR (Some 5));
  f4_C1 : tm 2 1 = Some (mkAction 1 DR (Some 2));
  f4_C2 : tm 2 2 = Some (mkAction 2 DR (Some 1));
  f4_C3 : tm 2 3 = Some (mkAction 3 DL (Some 6));
  f4_D0 : tm 3 0 = Some (mkAction 0 DR (Some 2));
  f4_D1 : tm 3 1 = Some (mkAction 1 DR (Some 2));
  f4_D2 : tm 3 2 = Some (mkAction 1 DL (Some 3));
  f4_D3 : tm 3 3 = Some (mkAction 3 DR (Some 3));
  f4_E0 : tm 4 0 = Some (mkAction 3 DR (Some 3));
  f4_E1 : tm 4 1 = Some (mkAction 1 DL (Some 4));
  f4_E2 : tm 4 2 = Some (mkAction 1 DL (Some 4));
  f4_E3 : tm 4 3 = Some (mkAction 3 DL (Some 4));
  f4_F1 : tm 5 1 = Some (mkAction 3 DL (Some 3));
  f4_F2 : tm 5 2 = Some (mkAction 2 DL (Some 4));
  f4_F3 : tm 5 3 = Some (mkAction 3 DL (Some 4));
  f4_G0 : tm 6 0 = Some (mkAction 1 DR (Some 6));
  f4_G1 : tm 6 1 = Some (mkAction 1 DL (Some 7));
  f4_G2 : tm 6 2 = Some (mkAction 2 DR (Some 6));
  f4_G3 : tm 6 3 = Some (mkAction 3 DL (Some 6));
  f4_H0 : tm 7 0 = Some (mkAction 1 DR (Some 2));
  f4_H1 : tm 7 1 = Some (mkAction 2 DL (Some 7));
  f4_H2 : tm 7 2 = Some (mkAction 1 DL (Some 0));
  f4_H3 : tm 7 3 = Some (mkAction 1 DL (Some 4))
}.

Definition B4cfg (k a b : nat) (R : list nat) : Config :=
  mkCfgR (Some 1) (rep (S b) 2 (rep a 1 (rep k 3 []))) R.

Definition F4cfg (k a b : nat) (R : list nat) : Config :=
  mkCfgR (Some 5) (rep (S b) 2 (rep a 1 (rep k 3 []))) R.

Definition C4cfg (k a : nat) (R : list nat) : Config :=
  mkCfgR (Some 2) (rep a 1 (rep k 3 [])) R.

(* Exact 3-level FGH function computed by Fwp2_4 *)
Fixpoint F4B (k : nat) : nat -> nat -> nat :=
  match k with
  | 0 =>
      fix go0 (b : nat) : nat -> nat :=
        match b with
        | 0 => fun a => a + 2
        | S b' => fun a => iter (go0 b') (a + 1) 1
        end
  | S k' =>
      fix gos (b : nat) : nat -> nat :=
        match b with
        | 0 => fun a => iter (fun s => F4B k' (s - 1) 1 + s) (a + 1) 1 + 1
        | S b' => fun a => iter (gos b') (a + 1) 1
        end
  end.

Section Fwp2_4Lemmas.
  Variable tm : TM.
  Hypothesis hc : Fwp2_4Core tm.

  Lemma f4_step_D0 : forall a R,
    step tm (mkCfgR (Some 3) [] (0 :: a :: R)) = Some (mkCfgR (Some 2) [] (a :: R)).
  Proof.
    intros a R. unfold step, mkCfgR. simpl. rewrite (f4_D0 tm hc). reflexivity.
  Qed.

  Lemma f4_loop_B2_R : forall n L R,
    Reaches tm (mkCfgR (Some 1) L (rep n 2 R)) (mkCfgR (Some 1) (rep n 2 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_R tm 1 1 (Some 1) L 2 _ (f4_B2 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_C1_R : forall n L R,
    Reaches tm (mkCfgR (Some 2) L (rep n 1 R)) (mkCfgR (Some 2) (rep n 1 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) L 1 _ (f4_C1 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_D2_L : forall n L R,
    Reaches tm (mkCfgR (Some 3) (rep n 2 L) (2 :: R)) (mkCfgR (Some 3) L (2 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 3 0 2 2 (Some 3) _ _ (f4_D2 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_D3_R : forall n L R,
    Reaches tm (mkCfgR (Some 3) L (rep n 3 R)) (mkCfgR (Some 3) (rep n 3 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_R tm 3 2 (Some 3) L 3 _ (f4_D3 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_E2_L : forall n L R,
    Reaches tm (mkCfgR (Some 4) (rep n 2 L) (2 :: R)) (mkCfgR (Some 4) L (2 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 4 0 2 2 (Some 4) _ _ (f4_E2 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_E1_L : forall n L R,
    Reaches tm (mkCfgR (Some 4) (rep n 1 L) (1 :: R)) (mkCfgR (Some 4) L (1 :: rep n 1 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 4 0 1 1 (Some 4) _ _ (f4_E1 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_E3_L : forall n L R,
    Reaches tm (mkCfgR (Some 4) (rep n 3 L) (3 :: R)) (mkCfgR (Some 4) L (3 :: rep n 3 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 4 2 3 3 (Some 4) _ _ (f4_E3 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_G2_R : forall n L R,
    Reaches tm (mkCfgR (Some 6) L (rep n 2 R)) (mkCfgR (Some 6) (rep n 2 L) R) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_R tm 6 1 (Some 6) L 2 _ (f4_G2 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_H1_L : forall n L R,
    Reaches tm (mkCfgR (Some 7) (rep n 1 L) (1 :: R)) (mkCfgR (Some 7) L (1 :: rep n 2 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 1 1 1 (Some 7) _ _ (f4_H1 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  Lemma f4_loop_A2_L : forall n L R,
    Reaches tm (mkCfgR (Some 0) (rep n 2 L) (2 :: R)) (mkCfgR (Some 0) L (2 :: rep n 2 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 0 1 2 2 (Some 0) _ _ (f4_A2 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  (* Base entry: 0^inf A> 3 R -> F4cfg 0 3 1 R in 23 steps *)
  Lemma f4_A3_base : forall R,
    Reaches tm (mkCfgR (Some 0) [] (3 :: R)) (F4cfg 0 3 1 R) 23.
  Proof.
    intro R. unfold F4cfg.
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 0 2 3 (Some 6) _ (f4_A3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 6 0 (Some 6) [] 0 _ (f4_G0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 2 1 3 (Some 6) _ _ (f4_G3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 6 0 1 (Some 7) _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 2 2 1 3 (Some 6) _ _ (f4_C3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 1 1 (Some 7) _ _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 1 1 (Some 7) _ (f4_H1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1] 2 _ (f4_C2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 0 1 2 (Some 0) _ _ (f4_H2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 0 1 (Some 6) [] 1 _ (f4_A1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 0 2 (Some 0) _ (f4_H2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 0 0 0 (Some 3) _ (f4_A0 tm hc)) |].
    eapply steps_succ; [apply (f4_step_D0 1 _) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1; 1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1; 1; 1] 2 _ (f4_C2 tm hc)) |].
    apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 5) [2; 1; 1; 1] 3 _ (f4_B3 tm hc)).
  Qed.

  (* Base entry from C>: 0^inf C> 3 R -> F4cfg 0 3 1 R in 23 steps (since C3 = A3 = 3LG) *)
  Lemma f4_C3_base : forall R,
    Reaches tm (mkCfgR (Some 2) [] (3 :: R)) (F4cfg 0 3 1 R) 23.
  Proof.
    intro R. unfold F4cfg.
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 2 2 3 (Some 6) _ (f4_C3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 6 0 (Some 6) [] 0 _ (f4_G0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 2 1 3 (Some 6) _ _ (f4_G3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 6 0 1 (Some 7) _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 2 2 1 3 (Some 6) _ _ (f4_C3 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 1 1 (Some 7) _ _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 1 1 (Some 7) _ (f4_H1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1] 2 _ (f4_C2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 0 1 2 (Some 0) _ _ (f4_H2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 0 1 (Some 6) [] 1 _ (f4_A1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 0 2 (Some 0) _ (f4_H2 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_L_nil tm 0 0 0 (Some 3) _ (f4_A0 tm hc)) |].
    eapply steps_succ; [apply (f4_step_D0 1 _) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1; 1] 1 _ (f4_C1 tm hc)) |].
    eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1; 1; 1] 2 _ (f4_C2 tm hc)) |].
    apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 5) [2; 1; 1; 1] 3 _ (f4_B3 tm hc)).
  Qed.

  (* Helper: 3^k H> 3 R -> 3^(S k) 1 C> R *)
  Lemma f4_H3_to_C : forall k R,
    exists t, Reaches tm (mkCfgR (Some 7) (rep k 3 []) (3 :: R))
                         (mkCfgR (Some 2) (1 :: rep (S k) 3 []) R) t.
  Proof.
    intros k R. destruct k as [| k''].
    - exists 3.
      eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 0 3 (Some 4) _ (f4_H3 tm hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R tm 4 2 (Some 3) [] 0 _ (f4_E0 tm hc)) |].
      apply steps_one. apply (step_mkCfgR_R tm 3 0 (Some 2) [3] 1 _ (f4_D1 tm hc)).
    - exists (1 + k'' + 1 + 1 + S k'' + 1).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 3 3 (Some 4) _ _ (f4_H3 tm hc)).
      + apply (f4_loop_E3_L k'' [] (1 :: R)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 4 2 3 (Some 4) _ (f4_E3 tm hc)).
      + apply steps_one. apply (step_mkCfgR_R tm 4 2 (Some 3) [] 0 _ (f4_E0 tm hc)).
      + apply (f4_loop_D3_R (S k'') [3] (1 :: R)).
      + replace (rep (S k'') 3 [3]) with (rep (S (S k'')) 3 [])
          by (replace (S (S k'')) with (S k'' + 1) by lia; rewrite (rep_add (S k'') 1); reflexivity).
        apply steps_one. apply (step_mkCfgR_R tm 3 0 (Some 2) _ 1 _ (f4_D1 tm hc)).
  Qed.

  (* Helper: 3^k E> 1 R -> 3^(S k) 1 C> R *)
  Lemma f4_E1_to_C : forall k R,
    exists t, Reaches tm (mkCfgR (Some 4) (rep k 3 []) (1 :: R))
                         (mkCfgR (Some 2) (1 :: rep (S k) 3 []) R) t.
  Proof.
    intros k R. destruct k as [| k''].
    - exists 3.
      eapply steps_succ; [apply (step_mkCfgR_L_nil tm 4 0 1 (Some 4) _ (f4_E1 tm hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_R tm 4 2 (Some 3) [] 0 _ (f4_E0 tm hc)) |].
      apply steps_one. apply (step_mkCfgR_R tm 3 0 (Some 2) [3] 1 _ (f4_D1 tm hc)).
    - exists (1 + k'' + 1 + 1 + S k'' + 1).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 4 0 3 1 (Some 4) _ _ (f4_E1 tm hc)).
      + apply (f4_loop_E3_L k'' [] (1 :: R)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 4 2 3 (Some 4) _ (f4_E3 tm hc)).
      + apply steps_one. apply (step_mkCfgR_R tm 4 2 (Some 3) [] 0 _ (f4_E0 tm hc)).
      + apply (f4_loop_D3_R (S k'') [3] (1 :: R)).
      + replace (rep (S k'') 3 [3]) with (rep (S (S k'')) 3 [])
          by (replace (S (S k'')) with (S k'' + 1) by lia; rewrite (rep_add (S k'') 1); reflexivity).
        apply steps_one. apply (step_mkCfgR_R tm 3 0 (Some 2) _ 1 _ (f4_D1 tm hc)).
  Qed.

  (* Rule 1: C4cfg k (a + 2) (3 :: R) -> B4cfg k 1 a (1 :: 3 :: R) *)
  Lemma f4_rule_C3 : forall k a R,
    exists t, Reaches tm (C4cfg k (a + 2) (3 :: R)) (B4cfg k 1 a (1 :: 3 :: R)) t.
  Proof.
    intros k a R. unfold C4cfg, B4cfg.
    replace (a + 2) with (S (S a)) by lia.
    destruct k as [| k'].
    - exists (1 + 1 + a + 1 + 1 + 1 + a).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 2 2 1 3 (Some 6) _ _ (f4_C3 tm hc)).
      + apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 1 1 (Some 7) _ _ (f4_G1 tm hc)).
      + apply (f4_loop_H1_L a [] (1 :: 3 :: R)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 7 1 1 (Some 7) _ (f4_H1 tm hc)).
      + apply steps_one. apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)).
      + apply steps_one. apply (step_mkCfgR_R tm 2 1 (Some 1) [1] 2 _ (f4_C2 tm hc)).
      + change (rep 1 1 (rep 0 3 [])) with [1].
        replace (rep (S a) 2 [1]) with (rep a 2 [2; 1])
          by (replace (S a) with (a + 1) by lia; rewrite (rep_add a 1); reflexivity).
        apply (f4_loop_B2_R a [2; 1] (1 :: 3 :: R)).
    - assert (H1 : Reaches tm
        (mkCfgR (Some 2) (1 :: 1 :: rep a 1 (3 :: rep k' 3 [])) (3 :: R))
        (mkCfgR (Some 7) (rep k' 3 []) (3 :: rep (S a) 2 (1 :: 3 :: R)))
        (1 + 1 + a + 1)).
      { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
        - apply steps_one. apply (step_mkCfgR_L_cons tm 2 2 1 3 (Some 6) _ _ (f4_C3 tm hc)).
        - apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 1 1 (Some 7) _ _ (f4_G1 tm hc)).
        - apply (f4_loop_H1_L a (3 :: rep k' 3 []) (1 :: 3 :: R)).
        - apply steps_one. apply (step_mkCfgR_L_cons tm 7 1 3 1 (Some 7) _ _ (f4_H1 tm hc)). }
      destruct (f4_H3_to_C k' (rep (S a) 2 (1 :: 3 :: R))) as [t2 H2].
      assert (H3 : Reaches tm
        (mkCfgR (Some 2) (1 :: rep (S k') 3 []) (rep (S a) 2 (1 :: 3 :: R)))
        (mkCfgR (Some 1) (rep (S a) 2 (1 :: rep (S k') 3 [])) (1 :: 3 :: R))
        (1 + a)).
      { eapply reaches_trans.
        - apply steps_one. apply (step_mkCfgR_R tm 2 1 (Some 1) _ 2 _ (f4_C2 tm hc)).
        - replace (rep (S a) 2 (1 :: rep (S k') 3 [])) with (rep a 2 (2 :: 1 :: rep (S k') 3 []))
            by (replace (S a) with (a + 1) by lia; rewrite (rep_add a 1); reflexivity).
          apply (f4_loop_B2_R a (2 :: 1 :: rep (S k') 3 []) (1 :: 3 :: R)). }
      exists ((1 + 1 + a + 1) + t2 + (1 + a)).
      eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  Qed.

  (* Rule 3: F4cfg k a b (1 :: R) -> C4cfg k (a + b + 1) (3 :: R) *)
  Lemma f4_rule_F1 : forall k a b R,
    1 <= a ->
    exists t, Reaches tm (F4cfg k a b (1 :: R)) (C4cfg k (a + b + 1) (3 :: R)) t.
  Proof.
    intros k a b R Ha. destruct a as [| a']; [lia |].
    unfold F4cfg, C4cfg.
    exists (1 + b + 1 + 1 + (b + 1)).
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|].
    - apply steps_one. apply (step_mkCfgR_L_cons tm 5 2 2 1 (Some 3) _ _ (f4_F1 tm hc)).
    - apply (f4_loop_D2_L b (1 :: rep a' 1 (rep k 3 [])) (3 :: R)).
    - apply steps_one. apply (step_mkCfgR_L_cons tm 3 0 1 2 (Some 3) _ _ (f4_D2 tm hc)).
    - apply steps_one. apply (step_mkCfgR_R tm 3 0 (Some 2) _ 1 _ (f4_D1 tm hc)).
    - replace (1 :: rep b 1 (3 :: R)) with (rep (b + 1) 1 (3 :: R))
        by (replace (b + 1) with (S b) by lia; reflexivity).
      replace (rep (S a' + b + 1) 1 (rep k 3 [])) with (rep (b + 1) 1 (1 :: rep a' 1 (rep k 3 [])))
        by (replace (S a' + b + 1) with ((b + 1) + S a') by lia; rewrite (rep_add (b + 1) (S a')); reflexivity).
      apply (f4_loop_C1_R (b + 1) (1 :: rep a' 1 (rep k 3 [])) (3 :: R)).
  Qed.

  (* Rule 4: F4cfg k a b (2 :: R) -> B4cfg (S k) (a + b + 1) 0 R *)
  Lemma f4_rule_F2 : forall k a b R,
    1 <= a ->
    exists t, Reaches tm (F4cfg k a b (2 :: R)) (B4cfg (S k) (a + b + 1) 0 R) t /\ a + b + 1 <= t.
  Proof.
    intros k a b R Ha. destruct a as [| a']; [lia |].
    unfold F4cfg, B4cfg.
    assert (H1 : Reaches tm
      (mkCfgR (Some 5) (2 :: rep b 2 (1 :: rep a' 1 (rep k 3 []))) (2 :: R))
      (mkCfgR (Some 4) (rep k 3 []) (1 :: rep (a' + b + 1) 1 (2 :: R)))
      (1 + b + 1 + a')).
    { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
      - apply steps_one. apply (step_mkCfgR_L_cons tm 5 1 2 2 (Some 4) _ _ (f4_F2 tm hc)).
      - apply (f4_loop_E2_L b (1 :: rep a' 1 (rep k 3 [])) (2 :: R)).
      - apply steps_one. apply (step_mkCfgR_L_cons tm 4 0 1 2 (Some 4) _ _ (f4_E2 tm hc)).
      - replace (rep (a' + b + 1) 1 (2 :: R)) with (rep a' 1 (1 :: rep b 1 (2 :: R)))
          by (replace (a' + b + 1) with (a' + S b) by lia; rewrite rep_add; reflexivity).
        apply (f4_loop_E1_L a' (rep k 3 []) (1 :: rep b 1 (2 :: R))). }
    destruct (f4_E1_to_C k (rep (a' + b + 1) 1 (2 :: R))) as [t2 H2].
    assert (H3 : Reaches tm
      (mkCfgR (Some 2) (1 :: rep (S k) 3 []) (rep (a' + b + 1) 1 (2 :: R)))
      (mkCfgR (Some 1) (2 :: rep (S a' + b + 1) 1 (rep (S k) 3 [])) R)
      ((a' + b + 1) + 1)).
    { eapply reaches_trans.
      - apply (f4_loop_C1_R (a' + b + 1) (1 :: rep (S k) 3 []) (2 :: R)).
      - replace (rep (S a' + b + 1) 1 (rep (S k) 3 [])) with (rep (a' + b + 1) 1 (1 :: rep (S k) 3 []))
          by (replace (S a' + b + 1) with ((a' + b + 1) + 1) by lia; rewrite (rep_add (a' + b + 1) 1); reflexivity).
        apply steps_one. apply (step_mkCfgR_R tm 2 1 (Some 1) _ 2 _ (f4_C2 tm hc)). }
    exists ((1 + b + 1 + a') + t2 + ((a' + b + 1) + 1)).
    split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | lia].
  Qed.

  (* Rule 5: F4cfg k a b (3 :: R) -> C4cfg (S k) (a + b + 1) (3 :: R) *)
  Lemma f4_rule_F3 : forall k a b R,
    1 <= a ->
    exists t, Reaches tm (F4cfg k a b (3 :: R)) (C4cfg (S k) (a + b + 1) (3 :: R)) t.
  Proof.
    intros k a b R Ha. destruct a as [| a']; [lia |].
    unfold F4cfg, C4cfg.
    assert (H1 : Reaches tm
      (mkCfgR (Some 5) (2 :: rep b 2 (1 :: rep a' 1 (rep k 3 []))) (3 :: R))
      (mkCfgR (Some 4) (rep k 3 []) (1 :: rep (a' + b + 1) 1 (3 :: R)))
      (1 + b + 1 + a')).
    { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
      - apply steps_one. apply (step_mkCfgR_L_cons tm 5 2 2 3 (Some 4) _ _ (f4_F3 tm hc)).
      - apply (f4_loop_E2_L b (1 :: rep a' 1 (rep k 3 [])) (3 :: R)).
      - apply steps_one. apply (step_mkCfgR_L_cons tm 4 0 1 2 (Some 4) _ _ (f4_E2 tm hc)).
      - replace (rep (a' + b + 1) 1 (3 :: R)) with (rep a' 1 (1 :: rep b 1 (3 :: R)))
          by (replace (a' + b + 1) with (a' + S b) by lia; rewrite rep_add; reflexivity).
        apply (f4_loop_E1_L a' (rep k 3 []) (1 :: rep b 1 (3 :: R))). }
    destruct (f4_E1_to_C k (rep (a' + b + 1) 1 (3 :: R))) as [t2 H2].
    assert (H3 : Reaches tm
      (mkCfgR (Some 2) (1 :: rep (S k) 3 []) (rep (a' + b + 1) 1 (3 :: R)))
      (mkCfgR (Some 2) (rep (S a' + b + 1) 1 (rep (S k) 3 [])) (3 :: R))
      (a' + b + 1)).
    { replace (rep (S a' + b + 1) 1 (rep (S k) 3 [])) with (rep (a' + b + 1) 1 (1 :: rep (S k) 3 []))
        by (replace (S a' + b + 1) with ((a' + b + 1) + 1) by lia; rewrite (rep_add (a' + b + 1) 1); reflexivity).
      apply (f4_loop_C1_R (a' + b + 1) (1 :: rep (S k) 3 []) (3 :: R)). }
    exists ((1 + b + 1 + a') + t2 + (a' + b + 1)).
    eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3].
  Qed.

  (* Sweep H2 for b = 0, k = 0: 1^a H> 2 1^j R -> C> 1^(a+j+2) R *)
  Lemma f4_sweep_H2_00 : forall a j R,
    exists t, Reaches tm
      (mkCfgR (Some 7) (rep a 1 []) (2 :: rep j 1 R))
      (mkCfgR (Some 2) [] (rep (a + 2 + j) 1 R)) t.
  Proof.
    induction a as [| a' IH]; intros j R.
    - exists 3. simpl.
      eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 0 2 (Some 0) _ (f4_H2 tm hc)) |].
      eapply steps_succ; [apply (step_mkCfgR_L_nil tm 0 0 0 (Some 3) _ (f4_A0 tm hc)) |].
      apply steps_one. apply (f4_step_D0 1 _).
    - assert (Hs : Reaches tm
        (mkCfgR (Some 7) (1 :: rep a' 1 []) (2 :: rep j 1 R))
        (mkCfgR (Some 7) (rep a' 1 []) (2 :: 1 :: rep j 1 R)) 3).
      { eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 0 1 2 (Some 0) _ _ (f4_H2 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 0 1 (Some 6) _ 1 _ (f4_A1 tm hc)) |].
        apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)). }
      destruct (IH (S j) R) as [t2 H2].
      replace (S a' + 2 + j) with (a' + 2 + S j) by lia.
      exists (3 + t2). eapply reaches_trans; [exact Hs | exact H2].
  Qed.

  (* Sweep H2 for b = 0, k = S k': 3^(S k') 1^a H> 2 1^j R -> 3^k' A> 3 1^(a+j+1) R *)
  Lemma f4_sweep_H2_S0 : forall k a j R,
    exists t, Reaches tm
      (mkCfgR (Some 7) (rep a 1 (rep (S k) 3 [])) (2 :: rep j 1 R))
      (mkCfgR (Some 0) (rep k 3 []) (3 :: rep (a + j + 1) 1 R)) t.
  Proof.
    induction a as [| a' IH]; intros j R.
    - exists 1. replace (0 + j + 1) with (S j) by lia. simpl.
      apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 3 2 (Some 0) _ _ (f4_H2 tm hc)).
    - assert (Hs : Reaches tm
        (mkCfgR (Some 7) (1 :: rep a' 1 (rep (S k) 3 [])) (2 :: rep j 1 R))
        (mkCfgR (Some 7) (rep a' 1 (rep (S k) 3 [])) (2 :: 1 :: rep j 1 R)) 3).
      { eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 0 1 2 (Some 0) _ _ (f4_H2 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 0 1 (Some 6) _ 1 _ (f4_A1 tm hc)) |].
        apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)). }
      destruct (IH (S j) R) as [t2 H2].
      replace (S a' + j + 1) with (a' + S j + 1) by lia.
      exists (3 + t2). eapply reaches_trans; [exact Hs | exact H2].
  Qed.

  Lemma f4_loop_G3_L : forall n L R,
    Reaches tm (mkCfgR (Some 6) (rep n 3 L) (3 :: R)) (mkCfgR (Some 6) L (3 :: rep n 3 R)) n.
  Proof.
    induction n as [| k IH]; intros L R; [apply reaches_zero |].
    simpl. eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 2 3 3 (Some 6) _ _ (f4_G3 tm hc)) |].
    rewrite <- rep_snoc_one. apply IH.
  Qed.

  (* General entry: 3^k A> 3 R -> F4cfg 0 3 1 (rep k 3 R) *)
  Lemma f4_A3_gen : forall k R,
    exists t, Reaches tm (mkCfgR (Some 0) (rep k 3 []) (3 :: R)) (F4cfg 0 3 1 (rep k 3 R)) t.
  Proof.
    intros k R. destruct k as [| k'].
    - exists 23. apply f4_A3_base.
    - exists (1 + k' + 1 + 22).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 0 2 3 3 (Some 6) _ _ (f4_A3 tm hc)).
      + apply (f4_loop_G3_L k' [] (3 :: R)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 6 2 3 (Some 6) _ (f4_G3 tm hc)).
      + unfold F4cfg.
        replace (3 :: rep k' 3 (3 :: R)) with (3 :: rep (S k') 3 R)
          by (rewrite rep_snoc_one; reflexivity).
        eapply steps_succ; [apply (step_mkCfgR_R tm 6 0 (Some 6) [] 0 _ (f4_G0 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 2 1 3 (Some 6) _ _ (f4_G3 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil tm 6 0 1 (Some 7) _ (f4_G1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 2 2 1 3 (Some 6) _ _ (f4_C3 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 1 1 (Some 7) _ _ (f4_G1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 1 1 (Some 7) _ (f4_H1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 7 0 (Some 2) [] 0 _ (f4_H0 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1] 2 _ (f4_C2 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 7 0 1 2 (Some 0) _ _ (f4_H2 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 0 1 (Some 6) [] 1 _ (f4_A1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil tm 7 0 2 (Some 0) _ (f4_H2 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_L_nil tm 0 0 0 (Some 3) _ (f4_A0 tm hc)) |].
        eapply steps_succ; [apply (f4_step_D0 1 _) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [] 1 _ (f4_C1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1] 1 _ (f4_C1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 0 (Some 2) [1; 1] 1 _ (f4_C1 tm hc)) |].
        eapply steps_succ; [apply (step_mkCfgR_R tm 2 1 (Some 1) [1; 1; 1] 2 _ (f4_C2 tm hc)) |].
        apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 5) [2; 1; 1; 1] 3 _ (f4_B3 tm hc)).
  Qed.

  (* Sweep H2 for b = S b', k = S k': 3^(S k') 1^a 2^(S b') H> 2 1^j R -> 3^k' A> 3 2^(S b') 1^(a+j+1) R *)
  Lemma f4_sweep_H2_SS : forall k a b j R,
    exists t, Reaches tm
      (mkCfgR (Some 7) (rep (S b) 2 (rep a 1 (rep (S k) 3 []))) (2 :: rep j 1 R))
      (mkCfgR (Some 0) (rep k 3 []) (3 :: rep (S b) 2 (rep (a + j + 1) 1 R))) t.
  Proof.
    intros k. induction a as [| a' IH]; intros b j R.
    - exists (1 + b + 1).
      replace (0 + j + 1) with (S j) by lia.
      eapply reaches_trans; [eapply reaches_trans |].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 2 2 (Some 0) _ _ (f4_H2 tm hc)).
      + apply (f4_loop_A2_L b (3 :: rep k 3 []) (1 :: rep j 1 R)).
      + apply steps_one. apply (step_mkCfgR_L_cons tm 0 1 3 2 (Some 0) _ _ (f4_A2 tm hc)).
    - assert (Hs : Reaches tm
        (mkCfgR (Some 7) (2 :: rep b 2 (1 :: rep a' 1 (rep (S k) 3 []))) (2 :: rep j 1 R))
        (mkCfgR (Some 7) (2 :: rep b 2 (rep a' 1 (rep (S k) 3 []))) (2 :: 1 :: rep j 1 R))
        (1 + b + 1 + 1 + S b + 1)).
      { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
        - apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 2 2 (Some 0) _ _ (f4_H2 tm hc)).
        - apply (f4_loop_A2_L b (1 :: rep a' 1 (rep (S k) 3 [])) (1 :: rep j 1 R)).
        - apply steps_one. apply (step_mkCfgR_L_cons tm 0 1 1 2 (Some 0) _ _ (f4_A2 tm hc)).
        - apply steps_one. apply (step_mkCfgR_R tm 0 1 (Some 6) (rep a' 1 (rep (S k) 3 [])) 1 _ (f4_A1 tm hc)).
        - apply (f4_loop_G2_R (S b) (2 :: rep a' 1 (rep (S k) 3 [])) (1 :: rep j 1 R)).
        - replace (rep (S b) 2 (2 :: rep a' 1 (rep (S k) 3 []))) with (2 :: 2 :: rep b 2 (rep a' 1 (rep (S k) 3 [])))
            by (rewrite rep_snoc_one; reflexivity).
          apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)). }
      destruct (IH b (S j) R) as [t2 H2].
      replace (S a' + j + 1) with (a' + S j + 1) by lia.
      exists (1 + b + 1 + 1 + S b + 1 + t2).
      eapply reaches_trans; [exact Hs | exact H2].
  Qed.

  (* Sweep H2 for b = S b', k = 0: 1^a 2^(S b') H> 2 1^j R -> B4cfg 0 1 b' (rep (a+j+1) 1 R) *)
  Lemma f4_sweep_H2_0S : forall a b j R,
    exists t, Reaches tm
      (mkCfgR (Some 7) (rep (S b) 2 (rep a 1 [])) (2 :: rep j 1 R))
      (B4cfg 0 1 b (rep (a + j + 1) 1 R)) t.
  Proof.
    induction a as [| a' IH]; intros b j R.
    - unfold B4cfg.
      exists (1 + b + 1 + 1 + 1 + 1 + 1 + b).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|]|]|].
      + apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 2 2 (Some 0) _ _ (f4_H2 tm hc)).
      + apply (f4_loop_A2_L b [] (1 :: rep j 1 R)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 0 1 2 (Some 0) _ (f4_A2 tm hc)).
      + apply steps_one. apply (step_mkCfgR_L_nil tm 0 0 0 (Some 3) _ (f4_A0 tm hc)).
      + apply steps_one. apply (f4_step_D0 1 _).
      + apply steps_one. apply (step_mkCfgR_R tm 2 0 (Some 2) [] 1 _ (f4_C1 tm hc)).
      + apply steps_one. apply (step_mkCfgR_R tm 2 1 (Some 1) [1] 2 _ (f4_C2 tm hc)).
      + change (rep 1 1 (rep 0 3 [])) with [1].
        replace (rep (S b) 2 [1]) with (rep b 2 [2; 1])
          by (replace (S b) with (b + 1) by lia; rewrite (rep_add b 1); reflexivity).
        replace (0 + j + 1) with (S j) by lia.
        apply (f4_loop_B2_R b [2; 1] (1 :: rep j 1 R)).
    - assert (Hs : Reaches tm
        (mkCfgR (Some 7) (2 :: rep b 2 (1 :: rep a' 1 [])) (2 :: rep j 1 R))
        (mkCfgR (Some 7) (2 :: rep b 2 (rep a' 1 [])) (2 :: 1 :: rep j 1 R))
        (1 + b + 1 + 1 + S b + 1)).
      { eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans |]|]|]|].
        - apply steps_one. apply (step_mkCfgR_L_cons tm 7 0 2 2 (Some 0) _ _ (f4_H2 tm hc)).
        - apply (f4_loop_A2_L b (1 :: rep a' 1 []) (1 :: rep j 1 R)).
        - apply steps_one. apply (step_mkCfgR_L_cons tm 0 1 1 2 (Some 0) _ _ (f4_A2 tm hc)).
        - apply steps_one. apply (step_mkCfgR_R tm 0 1 (Some 6) (rep a' 1 []) 1 _ (f4_A1 tm hc)).
        - apply (f4_loop_G2_R (S b) (2 :: rep a' 1 []) (1 :: rep j 1 R)).
        - replace (rep (S b) 2 (2 :: rep a' 1 [])) with (2 :: 2 :: rep b 2 (rep a' 1 []))
            by (rewrite rep_snoc_one; reflexivity).
          apply steps_one. apply (step_mkCfgR_L_cons tm 6 0 2 1 (Some 7) _ _ (f4_G1 tm hc)). }
      destruct (IH b (S j) R) as [t2 H2].
      replace (S a' + j + 1) with (a' + S j + 1) by lia.
      exists (1 + b + 1 + 1 + S b + 1 + t2).
      eapply reaches_trans; [exact Hs | exact H2].
  Qed.

  (* FGH growth of F4B *)
  Lemma F4B_ge_succ : forall k b a, a + 2 <= F4B k b a.
  Proof.
    induction k as [| k' IHk].
    - induction b as [| b' IHb]; intro a; [simpl; lia |].
      change (a + 2 <= iter (F4B 0 b') (a + 1) 1).
      assert (Hge : forall n, 2 * n + 1 <= iter (F4B 0 b') n 1).
      { induction n as [| p IHp]; [simpl; lia |].
        rewrite iter_succ. pose proof (IHb (iter (F4B 0 b') p 1)). lia. }
      pose proof (Hge (a + 1)). lia.
    - induction b as [| b' IHb]; intro a.
      + change (a + 2 <= iter (fun s => F4B k' (s - 1) 1 + s) (a + 1) 1 + 1).
        assert (Hge : forall n, 2 * n + 1 <= iter (fun s => F4B k' (s - 1) 1 + s) n 1).
        { induction n as [| p IHp]; [simpl; lia |].
          rewrite iter_succ. pose proof (IHk (iter (fun s => F4B k' (s - 1) 1 + s) p 1 - 1) 1). lia. }
        pose proof (Hge (a + 1)). lia.
      + change (a + 2 <= iter (F4B (S k') b') (a + 1) 1).
        assert (Hge : forall n, 2 * n + 1 <= iter (F4B (S k') b') n 1).
        { induction n as [| p IHp]; [simpl; lia |].
          rewrite iter_succ. pose proof (IHb (iter (F4B (S k') b') p 1)). lia. }
        pose proof (Hge (a + 1)). lia.
  Qed.

  Lemma F4B_mono_a : forall k b x y, x <= y -> F4B k b x <= F4B k b y.
  Proof.
    intros k b x y Hxy. destruct k as [| k'].
    - destruct b as [| b']; [simpl; lia |].
      change (iter (F4B 0 b') (x + 1) 1 <= iter (F4B 0 b') (y + 1) 1).
      assert (Hstep : forall n, iter (F4B 0 b') n 1 <= iter (F4B 0 b') (S n) 1).
      { intro n. rewrite iter_succ. pose proof (F4B_ge_succ 0 b' (iter (F4B 0 b') n 1)). lia. }
      assert (Hmn : forall p q, p <= q -> iter (F4B 0 b') p 1 <= iter (F4B 0 b') q 1).
      { intros p q Hpq. induction Hpq; [lia | eapply Nat.le_trans; [exact IHHpq | apply Hstep]]. }
      apply Hmn. lia.
    - destruct b as [| b'].
      + change (iter (fun s => F4B k' (s - 1) 1 + s) (x + 1) 1 + 1 <= iter (fun s => F4B k' (s - 1) 1 + s) (y + 1) 1 + 1).
        assert (Hstep : forall n, iter (fun s => F4B k' (s - 1) 1 + s) n 1 <= iter (fun s => F4B k' (s - 1) 1 + s) (S n) 1).
        { intro n. rewrite iter_succ. lia. }
        assert (Hmn : forall p q, p <= q -> iter (fun s => F4B k' (s - 1) 1 + s) p 1 <= iter (fun s => F4B k' (s - 1) 1 + s) q 1).
        { intros p q Hpq. induction Hpq; [lia | eapply Nat.le_trans; [exact IHHpq | apply Hstep]]. }
        pose proof (Hmn (x + 1) (y + 1) ltac:(lia)). lia.
      + change (iter (F4B (S k') b') (x + 1) 1 <= iter (F4B (S k') b') (y + 1) 1).
        assert (Hstep : forall n, iter (F4B (S k') b') n 1 <= iter (F4B (S k') b') (S n) 1).
        { intro n. rewrite iter_succ. pose proof (F4B_ge_succ (S k') b' (iter (F4B (S k') b') n 1)). lia. }
        assert (Hmn : forall p q, p <= q -> iter (F4B (S k') b') p 1 <= iter (F4B (S k') b') q 1).
        { intros p q Hpq. induction Hpq; [lia | eapply Nat.le_trans; [exact IHHpq | apply Hstep]]. }
        apply Hmn. lia.
  Qed.

  (* Main B4 execution property at level k *)
  Definition f4_B_level (k : nat) : Prop :=
    forall b a R, 1 <= a ->
      exists a' t, Reaches tm (B4cfg k a b (1 :: R)) (B4cfg k a' b R) t /\
                   F4B k b a <= a' /\ a' <= t.

  Lemma f4_B_rep : forall k, f4_B_level k ->
    forall b n a R, 1 <= a ->
      exists a' t, Reaches tm (B4cfg k a b (rep n 1 R)) (B4cfg k a' b R) t /\
                   iter (F4B k b) n a <= a' /\ (1 <= n -> a' <= t).
  Proof.
    intros k Hk b n. induction n as [| p IH]; intros a R Ha.
    - exists a, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
    - destruct (Hk b a (rep p 1 R) Ha) as [a1 [t1 [H1 [Hge1 Hle1]]]].
      destruct p as [| p'].
      + exists a1, t1. split; [exact H1 | split; [simpl; exact Hge1 | intros _; exact Hle1]].
      + assert (Ha1 : 1 <= a1) by (pose proof (F4B_ge_succ k b a); lia).
        destruct (IH a1 R Ha1) as [a2 [t2 [H2 [Hge2 Hle2]]]].
        exists a2, (t1 + t2).
        split; [eapply reaches_trans; [exact H1 | exact H2] |].
        split.
        * replace (iter (F4B k b) (S (S p')) a) with (iter (F4B k b) (S p') (F4B k b a))
            by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
          eapply Nat.le_trans; [apply iter_mono_arg; [exact (F4B_mono_a k b) | exact Hge1] | exact Hge2].
        * intros _. specialize (Hle2 ltac:(lia)). lia.
  Qed.

  Lemma f4_B_0 : f4_B_level 0.
  Proof.
    unfold f4_B_level. intro b. induction b as [| b' IH]; intros a R Ha.
    - unfold B4cfg.
      assert (H1 : Reaches tm (mkCfgR (Some 1) (2 :: rep a 1 []) (1 :: R))
                              (mkCfgR (Some 7) (rep a 1 []) (2 :: 2 :: R)) 1).
      { apply steps_one. apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)). }
      destruct (f4_sweep_H2_00 a 0 (2 :: R)) as [t2 H2].
      assert (H3 : Reaches tm (mkCfgR (Some 2) [] (rep (a + 2) 1 (2 :: R)))
                              (mkCfgR (Some 1) (2 :: rep (a + 2) 1 []) R) ((a + 2) + 1)).
      { eapply reaches_trans.
        - apply (f4_loop_C1_R (a + 2) [] (2 :: R)).
        - apply steps_one. apply (step_mkCfgR_R tm 2 1 (Some 1) _ 2 _ (f4_C2 tm hc)). }
      replace (a + 2 + 0) with (a + 2) in H2 by lia.
      exists (a + 2), (1 + t2 + ((a + 2) + 1)).
      split; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | simpl; lia].
    - assert (H1 : Reaches tm (B4cfg 0 a (S b') (1 :: R))
                              (mkCfgR (Some 7) (rep (S b') 2 (rep a 1 [])) (2 :: 2 :: R)) 1).
      { unfold B4cfg. apply steps_one. apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)). }
      destruct (f4_sweep_H2_0S a b' 0 (2 :: R)) as [t2 H2].
      replace (a + 0 + 1) with (a + 1) in H2 by lia.
      assert (Hrep : forall n x R0, 1 <= x ->
        exists a' t, Reaches tm (B4cfg 0 x b' (rep n 1 R0)) (B4cfg 0 a' b' R0) t /\
                     iter (F4B 0 b') n x <= a' /\ (1 <= n -> a' <= t)).
      { induction n as [| p IHp]; intros x R0 Hx.
        - exists x, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
        - destruct (IH x (rep p 1 R0) Hx) as [a1 [t1 [Ha1 [Hge1 Hle1]]]].
          destruct p as [| p'].
          + exists a1, t1. split; [exact Ha1 | split; [simpl; exact Hge1 | intros _; exact Hle1]].
          + assert (Hx1 : 1 <= a1) by (pose proof (F4B_ge_succ 0 b' x); lia).
            destruct (IHp a1 R0 Hx1) as [a2 [t2' [Ha2 [Hge2 Hle2]]]].
            exists a2, (t1 + t2').
            split; [eapply reaches_trans; [exact Ha1 | exact Ha2] |].
            split.
            * replace (iter (F4B 0 b') (S (S p')) x) with (iter (F4B 0 b') (S p') (F4B 0 b' x))
                by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
              eapply Nat.le_trans; [apply iter_mono_arg; [exact (F4B_mono_a 0 b') | exact Hge1] | exact Hge2].
            * intros _. specialize (Hle2 ltac:(lia)). lia. }
      destruct (Hrep (a + 1) 1 (2 :: R) ltac:(lia)) as [a' [t3 [H3 [Hge3 Hle3]]]].
      assert (H4 : Reaches tm (B4cfg 0 a' b' (2 :: R)) (B4cfg 0 a' (S b') R) 1).
      { unfold B4cfg. apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 1) _ 2 _ (f4_B2 tm hc)). }
      exists a', (1 + t2 + t3 + 1).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] |].
      change (F4B 0 (S b') a) with (iter (F4B 0 b') (a + 1) 1).
      specialize (Hle3 ltac:(lia)). lia.
  Qed.

  (* F4 on 1 step at level k, given f4_B_level k *)
  Lemma f4_F1_step : forall k, f4_B_level k ->
    forall a b R, 1 <= a ->
      exists a' b' t, Reaches tm (F4cfg k a b (1 :: R)) (F4cfg k a' b' R) t /\
                     F4B k (a + b - 1) 1 <= a' /\ b' = a + b /\ 1 <= a' /\ a' <= t.
  Proof.
    intros k Hk a b R Ha.
    destruct (f4_rule_F1 k a b R Ha) as [t1 H1].
    replace (a + b + 1) with ((a + b - 1) + 2) in H1 by lia.
    destruct (f4_rule_C3 k (a + b - 1) R) as [t2 H2].
    destruct (Hk (a + b - 1) 1 (3 :: R) ltac:(lia)) as [a' [t3 [H3 [Hge3 Hle3]]]].
    assert (H4 : Reaches tm (B4cfg k a' (a + b - 1) (3 :: R)) (F4cfg k a' (a + b) R) 1).
    { unfold B4cfg, F4cfg. replace (S (a + b)) with (S (S (a + b - 1))) by lia.
      apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 5) _ 3 _ (f4_B3 tm hc)). }
    exists a', (a + b), (t1 + t2 + t3 + 1).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] |].
    pose proof (F4B_ge_succ k (a + b - 1) 1). lia.
  Qed.

  (* F4 on 3 step: F4cfg k a b (3 :: R) -> F4cfg (S k) a' b' R, given f4_B_level (S k) *)
  Lemma f4_F3_step : forall k, f4_B_level (S k) ->
    forall a b R, 1 <= a ->
      exists a' b' t, Reaches tm (F4cfg k a b (3 :: R)) (F4cfg (S k) a' b' R) t /\
                     F4B (S k) (a + b - 1) 1 <= a' /\ b' = a + b /\ 1 <= a' /\ a' <= t.
  Proof.
    intros k Hk a b R Ha.
    destruct (f4_rule_F3 k a b R Ha) as [t1 H1].
    replace (a + b + 1) with ((a + b - 1) + 2) in H1 by lia.
    destruct (f4_rule_C3 (S k) (a + b - 1) R) as [t2 H2].
    destruct (Hk (a + b - 1) 1 (3 :: R) ltac:(lia)) as [a' [t3 [H3 [Hge3 Hle3]]]].
    assert (H4 : Reaches tm (B4cfg (S k) a' (a + b - 1) (3 :: R)) (F4cfg (S k) a' (a + b) R) 1).
    { unfold B4cfg, F4cfg. replace (S (a + b)) with (S (S (a + b - 1))) by lia.
      apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 5) _ 3 _ (f4_B3 tm hc)). }
    exists a', (a + b), (t1 + t2 + t3 + 1).
    split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] |].
    pose proof (F4B_ge_succ (S k) (a + b - 1) 1). lia.
  Qed.

  (* A3_gen full: 3^k A> 3 R -> F4cfg k a' b' R, given f4_B_level j for all j <= k *)
  Lemma f4_A3_full : forall k, (forall j, j <= k -> f4_B_level j) ->
    forall R, exists a' b' t, Reaches tm (mkCfgR (Some 0) (rep k 3 []) (3 :: R)) (F4cfg k a' b' R) t /\
                              1 <= a' /\ a' <= t.
  Proof.
    intros k Hall R. destruct k as [| k'].
    - exists 3, 1, 23. split; [apply f4_A3_base | lia].
    - destruct (f4_A3_gen (S k') R) as [t0 H0].
      assert (Hclimb : forall m j a b R0, j + m = S k' -> 1 <= a ->
        exists a' b' t, Reaches tm (F4cfg j a b (rep m 3 R0)) (F4cfg (S k') a' b' R0) t /\
                        1 <= a' /\ (1 <= m -> a' <= t)).
      { induction m as [| m' IHm]; intros j a b R0 Hjm Ha.
        - replace j with (S k') by lia. exists a, b, 0. split; [apply reaches_zero | lia].
        - destruct (f4_F3_step j (Hall (S j) ltac:(lia)) a b (rep m' 3 R0) Ha) as [a1 [b1 [t1 [H1 [_ [_ [Ha1 Hle1]]]]]]].
          destruct m' as [| m''].
          + replace (S j) with (S k') in H1 by lia. exists a1, b1, t1. split; [exact H1 | split; [exact Ha1 | intros _; exact Hle1]].
          + destruct (IHm (S j) a1 b1 R0 ltac:(lia) Ha1) as [a2 [b2 [t2 [H2 [Ha2 Hle2]]]]].
            exists a2, b2, (t1 + t2). split; [eapply reaches_trans; [exact H1 | exact H2] |].
            split; [exact Ha2 | intros _; specialize (Hle2 ltac:(lia)); lia]. }
      destruct (Hclimb (S k') 0 3 1 R ltac:(lia) ltac:(lia)) as [a' [b' [t1 [H1 [Ha' Hle']]]]].
      exists a', b', (t0 + t1). split; [eapply reaches_trans; [exact H0 | exact H1] | specialize (Hle' ltac:(lia)); lia].
  Qed.

  Lemma F4B_step_b : forall k b a, F4B k b a <= F4B k (S b) a.
  Proof.
    intros k b a.
    assert (Hge : a <= iter (F4B k b) a 1).
    { induction a as [| p IHp]; [simpl; lia |].
      rewrite iter_succ. pose proof (F4B_ge_succ k b (iter (F4B k b) p 1)). lia. }
    assert (Heq : F4B k (S b) a = iter (F4B k b) (a + 1) 1) by (destruct k; reflexivity).
    rewrite Heq. replace (a + 1) with (S a) by lia. rewrite iter_succ.
    apply F4B_mono_a. exact Hge.
  Qed.

  Lemma F4B_mono_b : forall k b1 b2 a, b1 <= b2 -> F4B k b1 a <= F4B k b2 a.
  Proof.
    intros k b1 b2 a Hb. induction Hb; [lia | eapply Nat.le_trans; [exact IHHb | apply F4B_step_b]].
  Qed.

  (* Step from level <= k to level S k *)
  Lemma f4_B_step : forall k, (forall j, j <= k -> f4_B_level j) -> f4_B_level (S k).
  Proof.
    intros k Hall. unfold f4_B_level. intro b. induction b as [| b' IH]; intros a R Ha.
    - (* b = 0 *)
      assert (H1 : Reaches tm (B4cfg (S k) a 0 (1 :: R))
                              (mkCfgR (Some 7) (rep a 1 (rep (S k) 3 [])) (2 :: 2 :: R)) 1).
      { unfold B4cfg. apply steps_one. apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)). }
      destruct (f4_sweep_H2_S0 k a 0 (2 :: R)) as [t2 H2].
      replace (a + 0 + 1) with (a + 1) in H2 by lia.
      destruct (f4_A3_full k Hall (rep (a + 1) 1 (2 :: R))) as [a0 [b0 [t3 [H3 [Ha0 _]]]]].
      assert (Hstep_mono : forall u v, u <= v -> F4B k (u - 1) 1 + u <= F4B k (v - 1) 1 + v).
      { intros u v Huv. pose proof (F4B_mono_b k (u - 1) (v - 1) 1 ltac:(lia)). lia. }
      assert (HrepF : forall n x y R0, 1 <= x ->
        exists x' y' t, Reaches tm (F4cfg k x y (rep n 1 R0)) (F4cfg k x' y' R0) t /\
                        1 <= x' /\
                        iter (fun s => F4B k (s - 1) 1 + s) n (x + y) <= x' + y').
      { induction n as [| p IHp]; intros x y R0 Hx.
        - exists x, y, 0. split; [apply reaches_zero | split; [exact Hx | simpl; lia]].
        - destruct (f4_F1_step k (Hall k ltac:(lia)) x y (rep p 1 R0) Hx) as [x1 [y1 [t1' [H1' [Hge1 [Hy1 [Hx1 _]]]]]]].
          destruct (IHp x1 y1 R0 Hx1) as [x2 [y2 [t2' [H2' [Hx2 Hge2]]]]].
          exists x2, y2, (t1' + t2').
          split; [eapply reaches_trans; [exact H1' | exact H2'] |].
          split; [exact Hx2 |].
          replace (iter (fun s => F4B k (s - 1) 1 + s) (S p) (x + y))
            with (iter (fun s => F4B k (s - 1) 1 + s) p (F4B k (x + y - 1) 1 + (x + y)))
            by (replace (S p) with (p + 1) by lia; rewrite iter_add; reflexivity).
          eapply Nat.le_trans; [| exact Hge2].
          apply iter_mono_arg; [exact Hstep_mono | lia]. }
      destruct (HrepF (a + 1) a0 b0 (2 :: R) Ha0) as [x' [y' [t4 [H4 [Hx' Hge4]]]]].
      destruct (f4_rule_F2 k x' y' R Hx') as [t5 [H5 Hle5]].
      exists (x' + y' + 1), (1 + t2 + t3 + t4 + t5).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] |].
      split.
      + change (iter (fun s => F4B k (s - 1) 1 + s) (a + 1) 1 + 1 <= x' + y' + 1).
        assert (Harg : iter (fun s => F4B k (s - 1) 1 + s) (a + 1) 1 <= iter (fun s => F4B k (s - 1) 1 + s) (a + 1) (a0 + b0)).
        { apply iter_mono_arg; [exact Hstep_mono | lia]. }
        lia.
      + lia.
    - (* b = S b' *)
      assert (H1 : Reaches tm (B4cfg (S k) a (S b') (1 :: R))
                              (mkCfgR (Some 7) (rep (S b') 2 (rep a 1 (rep (S k) 3 []))) (2 :: 2 :: R)) 1).
      { unfold B4cfg. apply steps_one. apply (step_mkCfgR_L_cons tm 1 1 2 1 (Some 7) _ _ (f4_B1 tm hc)). }
      destruct (f4_sweep_H2_SS k a b' 0 (2 :: R)) as [t2 H2].
      replace (a + 0 + 1) with (a + 1) in H2 by lia.
      destruct (f4_A3_full k Hall (rep (S b') 2 (rep (a + 1) 1 (2 :: R)))) as [a0 [b0 [t3 [H3 [Ha0 _]]]]].
      destruct (f4_rule_F2 k a0 b0 (rep b' 2 (rep (a + 1) 1 (2 :: R))) Ha0) as [t4 [H4 _]].
      assert (H5 : Reaches tm (B4cfg (S k) (a0 + b0 + 1) 0 (rep b' 2 (rep (a + 1) 1 (2 :: R))))
                              (B4cfg (S k) (a0 + b0 + 1) b' (rep (a + 1) 1 (2 :: R))) b').
      { unfold B4cfg.
        replace (rep (S b') 2 (rep (a0 + b0 + 1) 1 (rep (S k) 3 [])))
          with (rep b' 2 (2 :: rep (a0 + b0 + 1) 1 (rep (S k) 3 [])))
          by (replace (S b') with (b' + 1) by lia; rewrite (rep_add b' 1); reflexivity).
        apply (f4_loop_B2_R b' (2 :: rep (a0 + b0 + 1) 1 (rep (S k) 3 [])) (rep (a + 1) 1 (2 :: R))). }
      assert (Hrep : forall n x R0, 1 <= x ->
        exists a' t, Reaches tm (B4cfg (S k) x b' (rep n 1 R0)) (B4cfg (S k) a' b' R0) t /\
                     iter (F4B (S k) b') n x <= a' /\ (1 <= n -> a' <= t)).
      { induction n as [| p IHp]; intros x R0 Hx.
        - exists x, 0. split; [apply reaches_zero | split; [simpl; lia | lia]].
        - destruct (IH x (rep p 1 R0) Hx) as [a1 [t1' [Ha1 [Hge1 Hle1]]]].
          destruct p as [| p'].
          + exists a1, t1'. split; [exact Ha1 | split; [simpl; exact Hge1 | intros _; exact Hle1]].
          + assert (Hx1 : 1 <= a1) by (pose proof (F4B_ge_succ (S k) b' x); lia).
            destruct (IHp a1 R0 Hx1) as [a2 [t2' [Ha2 [Hge2 Hle2]]]].
            exists a2, (t1' + t2').
            split; [eapply reaches_trans; [exact Ha1 | exact Ha2] |].
            split.
            * replace (iter (F4B (S k) b') (S (S p')) x) with (iter (F4B (S k) b') (S p') (F4B (S k) b' x))
                by (replace (S (S p')) with (S p' + 1) by lia; rewrite iter_add; reflexivity).
              eapply Nat.le_trans; [apply iter_mono_arg; [exact (F4B_mono_a (S k) b') | exact Hge1] | exact Hge2].
            * intros _. specialize (Hle2 ltac:(lia)). lia. }
      destruct (Hrep (a + 1) (a0 + b0 + 1) (2 :: R) ltac:(lia)) as [a' [t6 [H6 [Hge6 Hle6]]]].
      assert (H7 : Reaches tm (B4cfg (S k) a' b' (2 :: R)) (B4cfg (S k) a' (S b') R) 1).
      { unfold B4cfg. apply steps_one. apply (step_mkCfgR_R tm 1 1 (Some 1) _ 2 _ (f4_B2 tm hc)). }
      exists a', (1 + t2 + t3 + t4 + b' + t6 + 1).
      split; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [exact H1 | exact H2] | exact H3] | exact H4] | exact H5] | exact H6] | exact H7] |].
      change (F4B (S k) (S b') a) with (iter (F4B (S k) b') (a + 1) 1).
      assert (Harg : iter (F4B (S k) b') (a + 1) 1 <= iter (F4B (S k) b') (a + 1) (a0 + b0 + 1)).
      { apply iter_mono_arg; [exact (F4B_mono_a (S k) b') | lia]. }
      specialize (Hle6 ltac:(lia)). lia.
  Qed.

  Lemma f4_B_all : forall k, f4_B_level k.
  Proof.
    assert (Hall : forall n j, j <= n -> f4_B_level j).
    { induction n as [| n' IH]; intros j Hj.
      - replace j with 0 by lia. exact f4_B_0.
      - destruct (Nat.eq_dec j (S n')) as [-> | Hne].
        + apply f4_B_step. exact IH.
        + apply IH. lia. }
    intro k. exact (Hall k k (Nat.le_refl k)).
  Qed.

  (* Main theorem: 0^inf C> 3^m R -> F4cfg (m-1) a b R, and same from A> *)
  Lemma f4_rule_C3_rep : forall m R, 1 <= m ->
    exists a b t, Reaches tm (mkCfgR (Some 2) [] (rep m 3 R)) (F4cfg (m - 1) a b R) t /\
                  1 <= a /\
                  (2 <= m -> F4B (m - 1) 3 1 <= a) /\
                  a <= t.
  Proof.
    intros m R Hm. destruct m as [| m']; [lia |].
    replace (S m' - 1) with m' by lia.
    destruct m' as [| m''].
    - exists 3, 1, 23. split; [apply f4_C3_base | lia].
    - pose proof (f4_C3_base (rep (S m'') 3 R)) as H0.
      assert (Hclimb : forall n j a b R0, j + n = S m'' -> 1 <= a -> 3 <= a + b - 1 ->
        exists a' b' t, Reaches tm (F4cfg j a b (rep n 3 R0)) (F4cfg (S m'') a' b' R0) t /\
                        1 <= a' /\
                        (1 <= n -> F4B (S m'') 3 1 <= a') /\
                        (1 <= n -> a' <= t)).
      { induction n as [| n' IHn]; intros j a b R0 Hjn Ha Hab.
        - replace j with (S m'') by lia. exists a, b, 0. split; [apply reaches_zero | lia].
        - destruct (f4_F3_step j (f4_B_all (S j)) a b (rep n' 3 R0) Ha) as [a1 [b1 [t1 [H1 [Hge1 [Hb1 [Ha1 Hle1]]]]]]].
          destruct n' as [| n''].
          + replace (S j) with (S m'') in H1, Hge1 by lia.
            exists a1, b1, t1. split; [exact H1 | split; [exact Ha1 | split; [intros _| intros _; exact Hle1]]].
            eapply Nat.le_trans; [apply F4B_mono_b; exact Hab | exact Hge1].
          + destruct (IHn (S j) a1 b1 R0 ltac:(lia) Ha1 ltac:(lia)) as [a2 [b2 [t2 [H2 [Ha2 [Hge2 Hle2]]]]]].
            exists a2, b2, (t1 + t2).
            split; [eapply reaches_trans; [exact H1 | exact H2] |].
            split; [exact Ha2 | split; [intros _; apply Hge2; lia | intros _; specialize (Hle2 ltac:(lia)); lia]]. }
      destruct (Hclimb (S m'') 0 3 1 R ltac:(lia) ltac:(lia) ltac:(lia)) as [a' [b' [t1 [H1 [Ha' [Hge' Hle']]]]]].
      exists a', b', (23 + t1).
      split; [eapply reaches_trans; [exact H0 | exact H1] |].
      specialize (Hge' ltac:(lia)). specialize (Hle' ltac:(lia)). lia.
  Qed.

  Lemma f4_rule_A3_rep : forall m R, 1 <= m ->
    exists a b t, Reaches tm (mkCfgR (Some 0) [] (rep m 3 R)) (F4cfg (m - 1) a b R) t /\
                  1 <= a /\
                  (2 <= m -> F4B (m - 1) 3 1 <= a) /\
                  a <= t.
  Proof.
    intros m R Hm. destruct m as [| m']; [lia |].
    replace (S m' - 1) with m' by lia.
    destruct m' as [| m''].
    - exists 3, 1, 23. split; [apply f4_A3_base | lia].
    - pose proof (f4_A3_base (rep (S m'') 3 R)) as H0.
      destruct (f4_rule_C3_rep (S (S m'')) R ltac:(lia)) as [a' [b' [t' _]]].
      (* Reuse exact same Hclimb via f4_F3_step *)
      assert (Hclimb : forall n j a b R0, j + n = S m'' -> 1 <= a -> 3 <= a + b - 1 ->
        exists a' b' t, Reaches tm (F4cfg j a b (rep n 3 R0)) (F4cfg (S m'') a' b' R0) t /\
                        1 <= a' /\
                        (1 <= n -> F4B (S m'') 3 1 <= a') /\
                        (1 <= n -> a' <= t)).
      { induction n as [| n' IHn]; intros j a b R0 Hjn Ha Hab.
        - replace j with (S m'') by lia. exists a, b, 0. split; [apply reaches_zero | lia].
        - destruct (f4_F3_step j (f4_B_all (S j)) a b (rep n' 3 R0) Ha) as [a1 [b1 [t1 [H1 [Hge1 [Hb1 [Ha1 Hle1]]]]]]].
          destruct n' as [| n''].
          + replace (S j) with (S m'') in H1, Hge1 by lia.
            exists a1, b1, t1. split; [exact H1 | split; [exact Ha1 | split; [intros _| intros _; exact Hle1]]].
            eapply Nat.le_trans; [apply F4B_mono_b; exact Hab | exact Hge1].
          + destruct (IHn (S j) a1 b1 R0 ltac:(lia) Ha1 ltac:(lia)) as [a2 [b2 [t2 [H2 [Ha2 [Hge2 Hle2]]]]]].
            exists a2, b2, (t1 + t2).
            split; [eapply reaches_trans; [exact H1 | exact H2] |].
            split; [exact Ha2 | split; [intros _; apply Hge2; lia | intros _; specialize (Hle2 ltac:(lia)); lia]]. }
      destruct (Hclimb (S m'') 0 3 1 R ltac:(lia) ltac:(lia) ltac:(lia)) as [a1 [b1 [t1 [H1 [Ha1 [Hge1 Hle1]]]]]].
      exists a1, b1, (23 + t1).
      split; [eapply reaches_trans; [exact H0 | exact H1] |].
      specialize (Hge1 ltac:(lia)). specialize (Hle1 ltac:(lia)). lia.
  Qed.

  (* FGH lower bound: 2 * fOmegaMul k b a <= F4B k b (2 * a) *)
  Lemma F4B_ge_2_fOmegaMul : forall k b a, 2 * fOmegaMul k b a <= F4B k b (2 * a).
  Proof.
    induction k as [| k' IHk].
    - induction b as [| b' IHb]; intro a.
      + simpl. lia.
      + change (2 * iter (fOmegaMul 0 b') a a <= iter (F4B 0 b') (2 * a + 1) 1).
        assert (Hiter : forall j, 2 * iter (fOmegaMul 0 b') j a <= iter (F4B 0 b') j (2 * a)).
        { induction j as [| j' IHj]; [simpl; lia |].
          rewrite !iter_succ. eapply Nat.le_trans; [| apply F4B_mono_a; exact IHj]. apply IHb. }
        assert (Hinit : 2 * a + 1 <= iter (F4B 0 b') a 1).
        { clear Hiter. induction a as [| p IHp]; [simpl; lia |].
          rewrite iter_succ. pose proof (F4B_ge_succ 0 b' (iter (F4B 0 b') p 1)). lia. }
        replace (2 * a + 1) with (S (a + a)) by lia.
        rewrite iter_succ, iter_add.
        pose proof (F4B_ge_succ 0 b' (iter (F4B 0 b') a (iter (F4B 0 b') a 1))).
        assert (Harg : iter (F4B 0 b') a (2 * a) <= iter (F4B 0 b') a (iter (F4B 0 b') a 1)).
        { apply iter_mono_arg; [exact (F4B_mono_a 0 b') | lia]. }
        pose proof (Hiter a). lia.
    - induction b as [| b' IHb]; intro a.
      + (* fOmegaMul (S k') 0 a = fOmegaMul k' a a <= F4B (S k') 0 (2 * a) *)
        destruct a as [| a'].
        * assert (Hf0 : forall j, fOmegaMul j 0 0 = 1).
          { induction j; [reflexivity | exact IHj]. }
          change (2 * fOmegaMul k' 0 0 <= iter (fun s => F4B k' (s - 1) 1 + s) 1 1 + 1).
          rewrite Hf0, iter_succ, iter_zero.
          pose proof (F4B_ge_succ k' 0 1). lia.
        * set (a := S a').
          change (2 * fOmegaMul k' a a <= iter (fun s => F4B k' (s - 1) 1 + s) (2 * a + 1) 1 + 1).
          assert (Hge_s : forall n, 2 * n + 1 <= iter (fun s => F4B k' (s - 1) 1 + s) n 1).
          { induction n as [| p IHp]; [simpl; lia |].
            rewrite iter_succ. pose proof (F4B_ge_succ k' (iter (fun s => F4B k' (s - 1) 1 + s) p 1 - 1) 1). lia. }
          replace (2 * a + 1) with (S (2 * a)) by lia.
          rewrite iter_succ.
          set (S0 := iter (fun s => F4B k' (s - 1) 1 + s) (2 * a) 1).
          assert (HS0 : 4 * a + 1 <= S0) by (unfold S0; pose proof (Hge_s (2 * a)); lia).
          assert (Hone : forall j, 2 * j + 1 <= F4B k' j 1).
          { induction j as [| j' IHj].
            - pose proof (F4B_ge_succ k' 0 1). lia.
            - assert (Heq : F4B k' (S j') 1 = F4B k' j' (F4B k' j' 1)) by (destruct k'; reflexivity).
              rewrite Heq. pose proof (F4B_ge_succ k' j' (F4B k' j' 1)). lia. }
          assert (Hstep1 : F4B k' a (2 * a) <= F4B k' (S a) 1).
          { assert (Heq : F4B k' (S a) 1 = F4B k' a (F4B k' a 1)) by (destruct k'; reflexivity).
            rewrite Heq. apply F4B_mono_a. pose proof (Hone a). lia. }
          assert (Hstep2 : F4B k' (S a) 1 <= F4B k' (S0 - 1) 1).
          { apply F4B_mono_b. subst a. lia. }
          pose proof (IHk a a). lia.
      + change (2 * iter (fOmegaMul (S k') b') a a <= iter (F4B (S k') b') (2 * a + 1) 1).
        assert (Hiter : forall j, 2 * iter (fOmegaMul (S k') b') j a <= iter (F4B (S k') b') j (2 * a)).
        { induction j as [| j' IHj]; [simpl; lia |].
          rewrite !iter_succ. eapply Nat.le_trans; [| apply F4B_mono_a; exact IHj]. apply IHb. }
        assert (Hinit : 2 * a + 1 <= iter (F4B (S k') b') a 1).
        { clear Hiter. induction a as [| p IHp]; [simpl; lia |].
          rewrite iter_succ. pose proof (F4B_ge_succ (S k') b' (iter (F4B (S k') b') p 1)). lia. }
        replace (2 * a + 1) with (S (a + a)) by lia.
        rewrite iter_succ, iter_add.
        pose proof (F4B_ge_succ (S k') b' (iter (F4B (S k') b') a (iter (F4B (S k') b') a 1))).
        assert (Harg : iter (F4B (S k') b') a (2 * a) <= iter (F4B (S k') b') a (iter (F4B (S k') b') a 1)).
        { apply iter_mono_arg; [exact (F4B_mono_a (S k') b') | lia]. }
        pose proof (Hiter a). lia.
  Qed.

  Lemma F4B_gt_f_omega2 : forall m, 2 <= m -> f_omega2 m < F4B m 3 1.
  Proof.
    intros m Hm.
    (* f_omega2 m = fOmegaMul m 0 m; and 2 * fOmegaMul m 0 m <= F4B m 0 (2 * m) <= F4B m 1 (2 * m)...
       Even simpler: F4B m 1 1 = F4B m 0 (F4B m 0 1), and F4B m 0 1 >= 2 * m?
       Wait: F4B m 0 1 >= 2 * m + 1 for m >= 1? Let's check:
       F4B m 3 1 = F4B m 2 (F4B m 2 1) >= F4B m 0 (2 * m) if F4B m 2 1 >= 2 * m!
       Actually F4B_ge_2_fOmegaMul m 0 m gives 2 * fOmegaMul m 0 m <= F4B m 0 (2 * m),
       and F4B m 1 (2 * m) >= F4B m 0 (2 * m). We just need 2 * m <= F4B m 2 1! *)
    assert (Hone0 : forall k, 2 * k + 1 <= F4B k 0 1).
    { induction k as [| k' IHk]; [simpl; lia |].
      change (2 * S k' + 1 <= iter (fun s => F4B k' (s - 1) 1 + s) 2 1 + 1).
      rewrite iter_succ, iter_succ, iter_zero.
      replace (1 - 1) with 0 by lia.
      pose proof (F4B_ge_succ k' 0 1).
      pose proof (F4B_mono_b k' 0 (F4B k' 0 1 + 1 - 1) 1 ltac:(lia)).
      pose proof (F4B_ge_succ k' (F4B k' 0 1 + 1 - 1) 1). lia. }
    assert (H1 : F4B m 0 (2 * m) <= F4B m 1 1).
    { assert (Heq : F4B m 1 1 = F4B m 0 (F4B m 0 1)) by (destruct m; reflexivity).
      rewrite Heq. apply F4B_mono_a. pose proof (Hone0 m). lia. }
    assert (H2 : F4B m 1 1 <= F4B m 3 1) by (apply F4B_mono_b; lia).
    pose proof (F4B_ge_2_fOmegaMul m 0 m) as Hf.
    change (fOmegaMul m 0 m < F4B m 3 1).
    pose proof (fgh_ge_self _ (fOmegaMul_props m 0) m). lia.
  Qed.

  Lemma f4_G3_base : forall R,
    Reaches tm (mkCfgR (Some 6) [] (3 :: R)) (F4cfg 0 3 1 R) 23.
  Proof.
    intro R.
    pose proof (f4_C3_base R) as Hc.
    unfold Reaches in *.
    change (match step tm (mkCfgR (Some 2) [] (3 :: R)) with Some c1 => steps tm 22 c1 | None => None end = Some (F4cfg 0 3 1 R)) in Hc.
    change (match step tm (mkCfgR (Some 6) [] (3 :: R)) with Some c1 => steps tm 22 c1 | None => None end = Some (F4cfg 0 3 1 R)).
    cbn [step mkCfgR cfg_st cfg_cur] in Hc |- *.
    rewrite (f4_C3 tm hc) in Hc. rewrite (f4_G3 tm hc). exact Hc.
  Qed.

  Lemma f4_rule_G3_rep : forall m R, 1 <= m ->
    exists a b t, Reaches tm (mkCfgR (Some 6) [] (rep m 3 R)) (F4cfg (m - 1) a b R) t /\
                  1 <= a /\
                  (2 <= m -> F4B (m - 1) 3 1 <= a) /\
                  a <= t.
  Proof.
    intros m R Hm. destruct m as [| m']; [lia |].
    replace (S m' - 1) with m' by lia.
    destruct m' as [| m''].
    - exists 3, 1, 23. split; [apply f4_G3_base | lia].
    - pose proof (f4_G3_base (rep (S m'') 3 R)) as H0.
      assert (Hclimb : forall n j a b R0, j + n = S m'' -> 1 <= a -> 3 <= a + b - 1 ->
        exists a' b' t, Reaches tm (F4cfg j a b (rep n 3 R0)) (F4cfg (S m'') a' b' R0) t /\
                        1 <= a' /\
                        (1 <= n -> F4B (S m'') 3 1 <= a') /\
                        (1 <= n -> a' <= t)).
      { induction n as [| n' IHn]; intros j a b R0 Hjn Ha Hab.
        - replace j with (S m'') by lia. exists a, b, 0. split; [apply reaches_zero | lia].
        - destruct (f4_F3_step j (f4_B_all (S j)) a b (rep n' 3 R0) Ha) as [a1 [b1 [t1 [H1 [Hge1 [Hb1 [Ha1 Hle1]]]]]]].
          destruct n' as [| n''].
          + replace (S j) with (S m'') in H1, Hge1 by lia.
            exists a1, b1, t1. split; [exact H1 | split; [exact Ha1 | split; [intros _| intros _; exact Hle1]]].
            eapply Nat.le_trans; [apply F4B_mono_b; exact Hab | exact Hge1].
          + destruct (IHn (S j) a1 b1 R0 ltac:(lia) Ha1 ltac:(lia)) as [a2 [b2 [t2 [H2 [Ha2 [Hge2 Hle2]]]]]].
            exists a2, b2, (t1 + t2).
            split; [eapply reaches_trans; [exact H1 | exact H2] |].
            split; [exact Ha2 | split; [intros _; apply Hge2; lia | intros _; specialize (Hle2 ltac:(lia)); lia]]. }
      destruct (Hclimb (S m'') 0 3 1 R ltac:(lia) ltac:(lia) ltac:(lia)) as [a1 [b1 [t1 [H1 [Ha1 [Hge1 Hle1]]]]]].
      exists a1, b1, (23 + t1).
      split; [eapply reaches_trans; [exact H0 | exact H1] |].
      specialize (Hge1 ltac:(lia)). specialize (Hle1 ltac:(lia)). lia.
  Qed.

End Fwp2_4Lemmas.
