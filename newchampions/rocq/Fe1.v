(*
  rocq/Fe1.v
  Formal, axiom-free Rocq 9.1 verification of:
    1. Wythagoras' f_{ε_0} Kirby-Paris Hydra core (16-state fe0_5_16 and 17-state fe0_5)
    2. Loader3229's f_{ε_1} mixed ()/[] Hydra cores:
       - fe1_6 (21 states, 6 symbols)
       - fe1_7 (20 states, 7 symbols)
       - fe1_8 (19 states, 8 symbols)
    3. Exact System-T higher-order functional semantics (HType k, semTree, semForest)
       proving termination and > f_{ε_0}(n - 3) / > f_{ε_1}(n - 3) runtime bounds.
*)

From Stdlib Require Import Arith List Lia.
From BB Require Import TM FGH Kropitz.
Import ListNotations.

(* ========================================================================= *)
(* Part 1: System-T Higher-Order Functional Hierarchy up to ε_0 and ε_1      *)
(* ========================================================================= *)

Inductive Kind : Type :=
  | KP : Kind   (* '(' = symbol 2 *)
  | KB : Kind.  (* '[' = symbol 5 *)

Inductive Tree : Type :=
  | Node : Kind -> list Tree -> Tree.

Fixpoint BaseType (k : nat) : Type :=
  match k with
  | 0 => nat
  | S k' => BaseType k' -> BaseType k'
  end.

Definition HType (k : nat) : Type := BaseType k -> BaseType k.

Fixpoint iter_poly {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter_poly f n' x)
  end.

Lemma iter_poly_add : forall {A : Type} (f : A -> A) a b x,
  iter_poly f (a + b) x = iter_poly f a (iter_poly f b x).
Proof.
  intros A f a. induction a as [| a' IH]; intros b x; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Fixpoint eval_succ (k : nat) : (nat -> HType k) -> HType k :=
  match k with
  | 0 => fun G (m : nat) => G m (S m)
  | S k' => fun G (x : HType k') => eval_succ k' (fun m => G m x)
  end.

Definition stepH (k : nat) (x : HType k) : HType k :=
  eval_succ k (fun m => iter_poly x (S m)).

Definition baseP (k : nat) : HType k :=
  match k with
  | 0 => S
  | S k' => stepH k'
  end.

Fixpoint chainH (d : nat) (k : nat) : HType k :=
  match d with
  | 0 => baseP k
  | S d' => chainH d' (S k) (baseP k)
  end.

Definition bracketH (k : nat) : HType k :=
  eval_succ k (fun m => chainH (m - 1) k).

Fixpoint chainB_H (d : nat) (k : nat) : HType k :=
  match d with
  | 0 => bracketH k
  | S d' => chainB_H d' (S k) (bracketH k)
  end.

Fixpoint semTree (t : Tree) (k : nat) : HType k :=
  match t with
  | Node KP cs =>
    (fix semF (l : list Tree) : HType (S k) :=
       match l with
       | [] => fun x => x
       | u :: rest => fun x => semF rest (semTree u (S k) x)
       end) cs (baseP k)
  | Node KB cs =>
    (fix semF (l : list Tree) : HType (S k) :=
       match l with
       | [] => fun x => x
       | u :: rest => fun x => semF rest (semTree u (S k) x)
       end) cs (bracketH k)
  end.

Fixpoint semForest (cs : list Tree) (k : nat) : HType (S k) :=
  match cs with
  | [] => fun x => x
  | u :: rest => fun x => semForest rest k (semTree u (S k) x)
  end.

Fixpoint semTopForest (cs : list Tree) (m : nat) : nat :=
  match cs with
  | [] => m
  | u :: rest => semTopForest rest (semTree u 0 m)
  end.

(* Fast-Growing Hierarchy at ε_0 and ε_1 via the canonical Hydra chains *)
Definition f_epsilon0 (n : nat) : nat := chainH (n + 2) 0 1.
Definition f_epsilon1 (n : nat) : nat := chainB_H (n + 2) 0 1.

(* Pointwise Ordering and Monotonicity across all finite types HType k *)
Fixpoint MonoH (k : nat) : HType k -> Prop :=
  match k with
  | 0 => fun (f : nat -> nat) =>
      (forall x, S x <= f x) /\
      (forall x y, x <= y -> f x <= f y)
  | S k' => fun (F : HType k' -> HType k') =>
      (forall g, MonoH k' g -> MonoH k' (F g)) /\
      (forall g, MonoH k' g ->
         (fix LeH (j : nat) : HType j -> HType j -> Prop :=
            match j with
            | 0 => fun f1 f2 =>
                (forall x, f1 x <= f2 x) /\
                (forall x y, x <= y -> f1 x <= f2 y)
            | S j' => fun F1 F2 =>
                forall h1 h2, MonoH j' h1 -> MonoH j' h2 ->
                  LeH j' h1 h2 -> LeH j' (F1 h1) (F2 h2)
            end) k' g (F g)) /\
      (forall g1 g2, MonoH k' g1 -> MonoH k' g2 ->
         (fix LeH (j : nat) : HType j -> HType j -> Prop :=
            match j with
            | 0 => fun f1 f2 =>
                (forall x, f1 x <= f2 x) /\
                (forall x y, x <= y -> f1 x <= f2 y)
            | S j' => fun F1 F2 =>
                forall h1 h2, MonoH j' h1 -> MonoH j' h2 ->
                  LeH j' h1 h2 -> LeH j' (F1 h1) (F2 h2)
            end) k' g1 g2 ->
         (fix LeH (j : nat) : HType j -> HType j -> Prop :=
            match j with
            | 0 => fun f1 f2 =>
                (forall x, f1 x <= f2 x) /\
                (forall x y, x <= y -> f1 x <= f2 y)
            | S j' => fun F1 F2 =>
                forall h1 h2, MonoH j' h1 -> MonoH j' h2 ->
                  LeH j' h1 h2 -> LeH j' (F1 h1) (F2 h2)
            end) k' (F g1) (F g2))
  end.

Fixpoint LeH (k : nat) : HType k -> HType k -> Prop :=
  match k with
  | 0 => fun f1 f2 =>
      (forall x, f1 x <= f2 x) /\
      (forall x y, x <= y -> f1 x <= f2 y)
  | S k' => fun F1 F2 =>
      forall h1 h2, MonoH k' h1 -> MonoH k' h2 ->
        LeH k' h1 h2 -> LeH k' (F1 h1) (F2 h2)
  end.

Lemma LeH_refl : forall k (f : HType k), MonoH k f -> LeH k f f.
Proof.
  induction k as [| k' IH]; intros f Hf; simpl in *.
  - destruct Hf as [Hinc Hmono]. split; [intro x; lia | exact Hmono].
  - destruct Hf as [_ [_ Hle]]. intros h1 h2 H1 H2 H12. apply Hle; assumption.
Qed.

Lemma LeH_trans : forall k (f1 f2 f3 : HType k),
  MonoH k f1 -> MonoH k f2 -> MonoH k f3 ->
  LeH k f1 f2 -> LeH k f2 f3 -> LeH k f1 f3.
Proof.
  induction k as [| k' IH]; intros f1 f2 f3 H1 H2 H3 H12 H23; simpl in *.
  - destruct H12 as [Ha1 Hb1]; destruct H23 as [Ha2 Hb2].
    split.
    + intro x. specialize (Ha1 x); specialize (Ha2 x); lia.
    + intros x y Hxy. eapply Nat.le_trans; [apply (Hb1 x y Hxy) | apply Ha2].
  - intros h1 h2 Hh1 Hh2 Hh12.
    destruct H1 as [H1m _]; destruct H2 as [H2m _]; destruct H3 as [H3m _].
    eapply IH.
    + apply H1m; exact Hh1.
    + apply H2m; exact Hh1.
    + apply H3m; exact Hh2.
    + apply H12; [exact Hh1 | exact Hh1 | apply LeH_refl; exact Hh1].
    + apply H23; assumption.
Qed.

Lemma iter_poly_MonoH : forall k (n : nat) (f : HType k),
  1 <= n -> MonoH k f -> MonoH k (iter_poly f n).
Proof.
  intros k n. induction n as [| n' IH]; intros f Hn Hf; [lia |].
  destruct n' as [| n'']; [simpl; exact Hf |].
  assert (Hpos : 1 <= S n'') by lia.
  specialize (IH f Hpos Hf).
  destruct k as [| k']; simpl in *.
  - destruct Hf as [Hfi Hfm]; destruct IH as [HIi HIm].
    split.
    + intro x. eapply Nat.le_trans; [apply (HIi x) | apply Nat.lt_le_incl, Hfi].
    + intros x y Hxy. apply Hfm, HIm, Hxy.
  - destruct Hf as [Hfm [Hfg Hfle]]; destruct IH as [HIm [HIg HIle]].
    split; [| split].
    + intros g Hg. apply Hfm, HIm, Hg.
    + intros g Hg. eapply LeH_trans with (f2 := iter_poly f (S n'') g).
      * exact Hg.
      * apply HIm; exact Hg.
      * apply Hfm, HIm; exact Hg.
      * apply HIg; exact Hg.
      * apply Hfg, HIm; exact Hg.
    + intros g1 g2 Hg1 Hg2 H12.
      apply Hfle; [apply HIm; exact Hg1 | apply HIm; exact Hg2 | apply HIle; assumption].
Qed.

Lemma iter_poly_LeH : forall k (n1 n2 : nat) (f1 f2 : HType k),
  1 <= n1 -> n1 <= n2 ->
  MonoH k f1 -> MonoH k f2 -> LeH k f1 f2 ->
  LeH k (iter_poly f1 n1) (iter_poly f2 n2).
Proof.
  intros k n1 n2 f1 f2 Hn1 H12 Hf1 Hf2 Hle.
  assert (Hstep1 : LeH k (iter_poly f1 n1) (iter_poly f2 n1)).
  { clear Hn1 H12. induction n1 as [| m IH]; simpl.
    - destruct k as [| k']; simpl.
      + split; intros; lia.
      + intros h1 h2 _ _ Hh. exact Hh.
    - destruct m as [| m'].
      + simpl. exact Hle.
      + assert (Hm : 1 <= S m') by lia.
        destruct k as [| k']; simpl in *.
        * destruct Hle as [_ Hfm]; destruct IH as [HIa HIb].
          split.
          -- intro x. apply Hfm, HIa.
          -- intros x y Hxy. apply Hfm, HIb, Hxy.
        * intros h1 h2 Hh1 Hh2 Hh12.
          apply Hle.
          -- apply (proj1 (iter_poly_MonoH (S k') (S m') f1 Hm Hf1)); exact Hh1.
          -- apply (proj1 (iter_poly_MonoH (S k') (S m') f2 Hm Hf2)); exact Hh2.
          -- apply IH; assumption. }
  induction H12 as [| m Hle_m IHm].
  - exact Hstep1.
  - eapply LeH_trans with (f2 := iter_poly f2 m).
    + apply iter_poly_MonoH; assumption.
    + apply iter_poly_MonoH; [lia | exact Hf2].
    + apply iter_poly_MonoH; [lia | exact Hf2].
    + exact IHm.
    + clear Hstep1 IHm.
      assert (Hm2 : MonoH k (iter_poly f2 m)) by (apply iter_poly_MonoH; [lia | exact Hf2]).
      destruct k as [| k']; simpl in *.
      * destruct Hf2 as [Hfi Hfm]; destruct Hm2 as [Hmi Hmm].
        split.
        -- intro x. apply Nat.lt_le_incl, Hfi.
        -- intros x y Hxy. eapply Nat.le_trans; [apply (Hmm x y Hxy) | apply Nat.lt_le_incl, Hfi].
      * intros h1 h2 Hh1 Hh2 Hh12.
        destruct Hf2 as [Hfm [Hfg Hfle]]; destruct Hm2 as [Hmm [Hmg Hmle]].
        eapply LeH_trans with (f2 := iter_poly f2 m h2).
        -- apply Hmm; exact Hh1.
        -- apply Hmm; exact Hh2.
        -- apply Hfm, Hmm; exact Hh2.
        -- apply Hmle; assumption.
        -- apply Hfg, Hmm; exact Hh2.
Qed.

Lemma eval_succ_MonoH_and_LeH : forall k (G1 G2 : nat -> HType k),
  (forall m, MonoH k (G1 m)) ->
  (forall m, MonoH k (G2 m)) ->
  (forall m1 m2, m1 <= m2 -> LeH k (G1 m1) (G2 m2)) ->
  LeH k (eval_succ k G1) (eval_succ k G2) /\
  ((forall m1 m2, m1 <= m2 -> LeH k (G1 m1) (G1 m2)) ->
   MonoH k (eval_succ k G1) /\ LeH k (G1 0) (eval_succ k G1)).
Proof.
  induction k as [| k' IH]; intros G1 G2 HG1 HG2 HG12.
  - simpl. split.
    + split.
      * intro x. exact (proj2 (HG12 x x ltac:(lia)) (S x) (S x) ltac:(lia)).
      * intros x y Hxy. exact (proj2 (HG12 x y Hxy) (S x) (S y) ltac:(lia)).
    + intro HG11. split.
      * split.
        -- intro x. pose proof (proj1 (HG1 x) (S x)). lia.
        -- intros x y Hxy. exact (proj2 (HG11 x y Hxy) (S x) (S y) ltac:(lia)).
      * split.
        -- intro x. exact (proj2 (HG11 0 x ltac:(lia)) x (S x) ltac:(lia)).
        -- intros x y Hxy. exact (proj2 (HG11 0 y ltac:(lia)) x (S y) ltac:(lia)).
  - simpl. split.
    + intros h1 h2 Hh1 Hh2 Hh12.
      apply (proj1 (IH (fun m => G1 m h1) (fun m => G2 m h2)
                       (fun m => proj1 (HG1 m) h1 Hh1)
                       (fun m => proj1 (HG2 m) h2 Hh2)
                       (fun m1 m2 Hm => HG12 m1 m2 Hm h1 h2 Hh1 Hh2 Hh12))).
    + intro HG11. split.
      * split; [| split].
        -- intros g Hg.
           apply (proj1 (proj2 (IH (fun m => G1 m g) (fun m => G1 m g)
                                   (fun m => proj1 (HG1 m) g Hg)
                                   (fun m => proj1 (HG1 m) g Hg)
                                   (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))
                               (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))).
        -- intros g Hg.
           eapply LeH_trans with (f2 := G1 0 g).
           ++ exact Hg.
           ++ apply (proj1 (HG1 0) g Hg).
           ++ apply (proj1 (proj2 (IH (fun m => G1 m g) (fun m => G1 m g)
                                      (fun m => proj1 (HG1 m) g Hg)
                                      (fun m => proj1 (HG1 m) g Hg)
                                      (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))
                                  (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))).
           ++ apply (proj1 (proj2 (HG1 0)) g Hg).
           ++ apply (proj2 (proj2 (IH (fun m => G1 m g) (fun m => G1 m g)
                                      (fun m => proj1 (HG1 m) g Hg)
                                      (fun m => proj1 (HG1 m) g Hg)
                                      (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))
                                  (fun m1 m2 Hm => HG11 m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)))).
        -- intros g1 g2 Hg1 Hg2 H12.
           apply (proj1 (IH (fun m => G1 m g1) (fun m => G1 m g2)
                            (fun m => proj1 (HG1 m) g1 Hg1)
                            (fun m => proj1 (HG1 m) g2 Hg2)
                            (fun m1 m2 Hm => HG11 m1 m2 Hm g1 g2 Hg1 Hg2 H12))).
      * intros h1 h2 Hh1 Hh2 Hh12.
        eapply LeH_trans with (f2 := G1 0 h2).
        -- apply (proj1 (HG1 0) h1 Hh1).
        -- apply (proj1 (HG1 0) h2 Hh2).
        -- apply (proj1 (proj2 (IH (fun m => G1 m h2) (fun m => G1 m h2)
                                   (fun m => proj1 (HG1 m) h2 Hh2)
                                   (fun m => proj1 (HG1 m) h2 Hh2)
                                   (fun m1 m2 Hm => HG11 m1 m2 Hm h2 h2 Hh2 Hh2 (LeH_refl k' h2 Hh2)))
                               (fun m1 m2 Hm => HG11 m1 m2 Hm h2 h2 Hh2 Hh2 (LeH_refl k' h2 Hh2)))).
        -- apply (proj2 (proj2 (HG1 0)) h1 h2 Hh1 Hh2 Hh12).
        -- apply (proj2 (proj2 (IH (fun m => G1 m h2) (fun m => G1 m h2)
                                   (fun m => proj1 (HG1 m) h2 Hh2)
                                   (fun m => proj1 (HG1 m) h2 Hh2)
                                   (fun m1 m2 Hm => HG11 m1 m2 Hm h2 h2 Hh2 Hh2 (LeH_refl k' h2 Hh2)))
                               (fun m1 m2 Hm => HG11 m1 m2 Hm h2 h2 Hh2 Hh2 (LeH_refl k' h2 Hh2)))).
Qed.

Lemma stepH_MonoH : forall k, MonoH (S k) (stepH k).
Proof.
  intro k. unfold stepH. split; [| split].
  - intros g Hg.
    apply (proj1 (proj2 (eval_succ_MonoH_and_LeH k (fun m => iter_poly g (S m)) (fun m => iter_poly g (S m))
                          (fun m => iter_poly_MonoH k (S m) g ltac:(lia) Hg)
                          (fun m => iter_poly_MonoH k (S m) g ltac:(lia) Hg)
                          (fun m1 m2 Hm => iter_poly_LeH k (S m1) (S m2) g g ltac:(lia) ltac:(lia) Hg Hg (LeH_refl k g Hg)))
                        (fun m1 m2 Hm => iter_poly_LeH k (S m1) (S m2) g g ltac:(lia) ltac:(lia) Hg Hg (LeH_refl k g Hg)))).
  - intros g Hg.
    change g with (iter_poly g 1) at 1.
    apply (proj2 (proj2 (eval_succ_MonoH_and_LeH k (fun m => iter_poly g (S m)) (fun m => iter_poly g (S m))
                          (fun m => iter_poly_MonoH k (S m) g ltac:(lia) Hg)
                          (fun m => iter_poly_MonoH k (S m) g ltac:(lia) Hg)
                          (fun m1 m2 Hm => iter_poly_LeH k (S m1) (S m2) g g ltac:(lia) ltac:(lia) Hg Hg (LeH_refl k g Hg)))
                        (fun m1 m2 Hm => iter_poly_LeH k (S m1) (S m2) g g ltac:(lia) ltac:(lia) Hg Hg (LeH_refl k g Hg)))).
  - intros g1 g2 Hg1 Hg2 H12.
    apply (proj1 (eval_succ_MonoH_and_LeH k (fun m => iter_poly g1 (S m)) (fun m => iter_poly g2 (S m))
                   (fun m => iter_poly_MonoH k (S m) g1 ltac:(lia) Hg1)
                   (fun m => iter_poly_MonoH k (S m) g2 ltac:(lia) Hg2)
                   (fun m1 m2 Hm => iter_poly_LeH k (S m1) (S m2) g1 g2 ltac:(lia) ltac:(lia) Hg1 Hg2 H12))).
Qed.

Lemma baseP_MonoH : forall k, MonoH k (baseP k).
Proof.
  destruct k as [| k']; simpl.
  - split; intros; lia.
  - apply stepH_MonoH.
Qed.

Lemma chainH_MonoH : forall d k, MonoH k (chainH d k).
Proof.
  induction d as [| d' IH]; intro k; simpl.
  - apply baseP_MonoH.
  - apply (proj1 (IH (S k))), baseP_MonoH.
Qed.

Lemma chainH_LeH_succ : forall d k, LeH k (chainH d k) (chainH (S d) k).
Proof.
  induction d as [| d' IH]; intro k.
  - simpl. apply (proj1 (proj2 (stepH_MonoH k))), baseP_MonoH.
  - change (LeH k (chainH d' (S k) (baseP k)) (chainH (S d') (S k) (baseP k))).
    apply (IH (S k)); [apply baseP_MonoH | apply baseP_MonoH | apply LeH_refl, baseP_MonoH].
Qed.

Lemma chainH_LeH_mono : forall d1 d2 k, d1 <= d2 -> LeH k (chainH d1 k) (chainH d2 k).
Proof.
  intros d1 d2 k Hd. induction Hd as [| d Hle IH].
  - apply LeH_refl, chainH_MonoH.
  - eapply LeH_trans.
    + apply chainH_MonoH.
    + apply chainH_MonoH.
    + apply chainH_MonoH.
    + exact IH.
    + apply chainH_LeH_succ.
Qed.

Lemma bracketH_MonoH : forall k, MonoH k (bracketH k).
Proof.
  intro k. unfold bracketH.
  apply (proj1 (proj2 (eval_succ_MonoH_and_LeH k (fun m => chainH (m - 1) k) (fun m => chainH (m - 1) k)
                        (fun m => chainH_MonoH (m - 1) k)
                        (fun m => chainH_MonoH (m - 1) k)
                        (fun m1 m2 Hm => chainH_LeH_mono (m1 - 1) (m2 - 1) k ltac:(lia)))
                      (fun m1 m2 Hm => chainH_LeH_mono (m1 - 1) (m2 - 1) k ltac:(lia)))).
Qed.

Lemma chainB_H_MonoH : forall d k, MonoH k (chainB_H d k).
Proof.
  induction d as [| d' IH]; intro k; simpl.
  - apply bracketH_MonoH.
  - apply (proj1 (IH (S k))), bracketH_MonoH.
Qed.

(* ========================================================================= *)
(* Part 2: Tape Movement Primitives (cfgL, walk_R_map, walk_L_rev_cfgL)      *)
(* ========================================================================= *)

Definition cfgL (st : nat) (L_with_cur : list nat) (R : list nat) : Config :=
  match L_with_cur with
  | [] => mkCfgR (Some st) [] (0 :: R)
  | a :: L' => mkCfgR (Some st) L' (a :: R)
  end.

Lemma step_to_cfgL : forall tm q st' w L cur R,
  1 <= w ->
  tm q cur = Some (mkAction w DL (Some st')) ->
  step tm (mkCfgR (Some q) L (cur :: R)) = Some (cfgL st' L (w :: R)).
Proof.
  intros tm q st' w L cur R Hw Ht.
  destruct w as [| w']; [lia |].
  destruct L as [| a L']; simpl.
  - apply step_mkCfgR_L_nil; exact Ht.
  - apply step_mkCfgR_L_cons; exact Ht.
Qed.

Lemma step_to_cfgL_zero_nil : forall tm q st' a L cur,
  tm q cur = Some (mkAction 0 DL (Some st')) ->
  step tm (mkCfgR (Some q) (a :: L) [cur]) = Some (cfgL st' (a :: L) []).
Proof.
  intros tm q st' a L cur Ht.
  unfold step, mkCfgR, cfgL; simpl; rewrite Ht; reflexivity.
Qed.

Lemma step_to_cfgL_zero_cons : forall tm q st' L cur b R,
  tm q cur = Some (mkAction 0 DL (Some st')) ->
  step tm (mkCfgR (Some q) L (cur :: b :: R)) = Some (cfgL st' L (0 :: b :: R)).
Proof.
  intros tm q st' L cur b R Ht.
  destruct L as [| a L']; simpl.
  - apply step_mkCfgR_L_nil_zero; exact Ht.
  - apply step_mkCfgR_L_cons_zero; exact Ht.
Qed.

Lemma reaches_one : forall tm c1 c2,
  step tm c1 = Some c2 -> Reaches tm c1 c2 1.
Proof. intros tm c1 c2 H. apply steps_one; exact H. Qed.

Lemma walk_R_map : forall tm q (f : nat -> nat) (xs : list nat) L R,
  (forall c, In c xs -> 1 <= f c /\ tm q c = Some (mkAction (f c) DR (Some q))) ->
  Reaches tm (mkCfgR (Some q) L (xs ++ R))
             (mkCfgR (Some q) (rev (map f xs) ++ L) R)
             (length xs).
Proof.
  intros tm q f xs. induction xs as [| x xs' IH]; intros L R Hxs; simpl.
  - apply reaches_zero.
  - destruct (Hxs x (or_introl eq_refl)) as [Hfx Htx].
    destruct (f x) as [| w'] eqn:Efx; [lia |].
    apply (steps_succ tm (length xs') _ (mkCfgR (Some q) (S w' :: L) (xs' ++ R))).
    + apply step_mkCfgR_R; exact Htx.
    + rewrite <- app_assoc; simpl.
      apply IH. intros c Hc. apply Hxs, or_intror, Hc.
Qed.

Lemma walk_R : forall tm q (xs : list nat) L R,
  (forall c, In c xs -> 1 <= c /\ tm q c = Some (mkAction c DR (Some q))) ->
  Reaches tm (mkCfgR (Some q) L (xs ++ R))
             (mkCfgR (Some q) (rev xs ++ L) R)
             (length xs).
Proof.
  intros tm q xs L R Hxs.
  pose proof (walk_R_map tm q (fun c => c) xs L R Hxs) as H.
  rewrite map_id in H. exact H.
Qed.

Lemma walk_L_rev_cfgL : forall tm q (ys : list nat) L_tail R,
  (forall c, In c ys -> 1 <= c /\ tm q c = Some (mkAction c DL (Some q))) ->
  Reaches tm (cfgL q (rev ys ++ L_tail) R)
             (cfgL q L_tail (ys ++ R))
             (length ys).
Proof.
  intros tm q ys. induction ys as [| y ys' IH]; intros L_tail R Hys; simpl.
  - apply reaches_zero.
  - rewrite <- app_assoc; simpl.
    replace (S (length ys')) with (length ys' + 1) by lia.
    eapply reaches_trans.
    + apply IH. intros c Hc. apply Hys, or_intror, Hc.
    + apply reaches_one. simpl.
      destruct (Hys y (or_introl eq_refl)) as [Hy Hty].
      apply step_to_cfgL; assumption.
Qed.

(* ========================================================================= *)
(* Part 3: Unified Hydra Core Specification & Phase Lemmas                   *)
(* ========================================================================= *)

Record HydraCore (tm : TM) (allow5 : bool)
  (stA stB1 stO stR stS stT stU stJRet : nat)
  (symB_mark symB_delim symB_temp sym2_mark sym5_mark : nat) : Prop := mkHydraCore {
  (* Bounds on parameterized symbols *)
  hc_delim_pos : allow5 = true -> 1 <= symB_delim /\ 1 <= symB_mark;
  (* State B (1) *)
  hc_B0 : tm 1 0 = Some (mkAction 1 DR None);
  hc_B1 : tm 1 1 = Some (mkAction 1 DR (Some 1));
  hc_B2 : tm 1 2 = Some (mkAction 2 DL (Some stB1));
  hc_B4 : allow5 = true -> tm 1 4 = Some (mkAction 1 DR (Some 1));
  hc_B5 : allow5 = true -> tm 1 5 = Some (mkAction 5 DL (Some stB1));
  (* State stB1 (counter boundary marker) *)
  hc_B1_1 : tm stB1 1 = Some (mkAction 4 DR (Some 2));
  (* State C (2) *)
  hc_C0 : tm 2 0 = Some (mkAction 0 DL (Some 8));
  hc_C2 : tm 2 2 = Some (mkAction 2 DR (Some 2));
  hc_C3 : tm 2 3 = Some (mkAction 3 DR (Some 2));
  hc_C4 : tm 2 4 = Some (mkAction 2 DR (Some 2));
  hc_C5 : allow5 = true -> tm 2 5 = Some (mkAction 5 DR (Some 2));
  hc_Cd : allow5 = true -> tm 2 symB_delim = Some (mkAction 5 DR (Some 2));
  (* State stA (parent search left) *)
  hc_A2 : tm stA 2 = Some (mkAction 0 DR (Some 5));
  hc_A3 : tm stA 3 = Some (mkAction 0 DR (Some 3));
  hc_A4 : tm stA 4 = Some (mkAction 1 DL (Some 13));
  hc_A5 : allow5 = true -> tm stA 5 = Some (mkAction symB_mark DR (Some 5));
  (* State D (3) *)
  hc_D0 : tm 3 0 = Some (mkAction 1 DL (Some 4));
  hc_D1 : tm 3 1 = Some (mkAction 1 DR (Some 3));
  hc_D2 : tm 3 2 = Some (mkAction 2 DR (Some 3));
  hc_D3 : tm 3 3 = Some (mkAction 3 DR (Some 3));
  hc_D5 : allow5 = true -> tm 3 5 = Some (mkAction 5 DR (Some 3));
  (* State E (4) *)
  hc_E0 : tm 4 0 = Some (mkAction 3 DL (Some stA));
  hc_E1 : tm 4 1 = Some (mkAction 1 DL (Some 4));
  hc_E2 : tm 4 2 = Some (mkAction 2 DL (Some 4));
  hc_E3 : tm 4 3 = Some (mkAction 3 DL (Some 4));
  hc_E5 : allow5 = true -> tm 4 5 = Some (mkAction 5 DL (Some 4));
  (* State F (5) *)
  hc_F0 : tm 5 0 = Some (mkAction 0 DL (Some 6));
  hc_F1 : tm 5 1 = Some (mkAction 1 DR (Some 5));
  hc_F2 : tm 5 2 = Some (mkAction 2 DR (Some 5));
  hc_F3 : tm 5 3 = Some (mkAction 3 DR (Some 5));
  hc_F4 : allow5 = true -> tm 5 4 = Some (mkAction symB_delim DL (Some stJRet));
  hc_F5 : allow5 = true -> tm 5 5 = Some (mkAction 5 DR (Some 5));
  (* State G (6) *)
  hc_G0 : tm 6 0 = Some (mkAction 0 DR (Some 8));
  hc_G1 : tm 6 1 = Some (mkAction 0 DL (Some 7));
  hc_G3 : tm 6 3 = Some (mkAction 3 DR (Some 8));
  hc_Gm : allow5 = true -> tm 6 symB_mark = Some (mkAction symB_mark DR (Some 8));
  (* State H (7) *)
  hc_H0 : tm 7 0 = Some (mkAction 2 DL (Some stA));
  hc_H1 : tm 7 1 = Some (mkAction 1 DL (Some 7));
  hc_H2 : tm 7 2 = Some (mkAction 2 DL (Some 7));
  hc_H3 : tm 7 3 = Some (mkAction 3 DL (Some 7));
  hc_H5 : allow5 = true -> tm 7 5 = Some (mkAction 5 DL (Some 7));
  hc_Hm : allow5 = true -> tm 7 symB_mark = Some (mkAction 5 DL (Some stA));
  (* State I (8) *)
  hc_I0 : tm 8 0 = Some (mkAction 3 DR (Some 15));
  hc_I2 : tm 8 2 = Some (mkAction 0 DL (Some stA));
  hc_I3 : tm 8 3 = Some (mkAction 0 DL (Some 8));
  hc_I5 : allow5 = true -> tm 8 5 = Some (mkAction 2 DL (Some stS));
  (* State J (9) *)
  hc_J0 : tm 9 0 = Some (mkAction 2 DR (Some stO));
  hc_J2 : tm 9 2 = Some (mkAction 2 DL (Some 9));
  hc_J3 : tm 9 3 = Some (mkAction 3 DL (Some 9));
  hc_J5 : allow5 = true -> tm 9 5 = Some (mkAction 5 DL (Some 9));
  hc_Jm : allow5 = true -> tm 9 symB_mark = Some (mkAction symB_temp DR (Some 5));
  hc_Jd : allow5 = true -> tm 9 symB_delim = Some (mkAction symB_temp DR (Some 5));
  (* State stJRet *)
  hc_JRt : allow5 = true -> tm stJRet symB_temp = Some (mkAction 5 DR (Some stO));
  hc_JR2 : allow5 = true -> tm stJRet 2 = Some (mkAction 2 DL (Some stJRet));
  hc_JR3 : allow5 = true -> tm stJRet 3 = Some (mkAction 3 DL (Some stJRet));
  hc_JR5 : allow5 = true -> tm stJRet 5 = Some (mkAction 5 DL (Some stJRet));
  (* State K (10) *)
  hc_K0 : tm 10 0 = Some (mkAction 2 DL (Some stU));
  hc_K2 : tm 10 2 = Some (mkAction 2 DR (Some 10));
  hc_K3 : tm 10 3 = Some (mkAction 3 DR (Some 10));
  hc_K4 : tm 10 4 = Some (mkAction 4 DR (Some 10));
  hc_K5 : allow5 = true -> tm 10 5 = Some (mkAction 5 DR (Some 10));
  hc_Kd : allow5 = true -> tm 10 symB_delim = Some (mkAction symB_delim DR (Some 10));
  (* State stU (return from K) *)
  hc_Um : tm stU sym2_mark = Some (mkAction 2 DR (Some stO));
  hc_U2 : tm stU 2 = Some (mkAction 2 DL (Some stU));
  hc_U3 : tm stU 3 = Some (mkAction 3 DL (Some stU));
  hc_U4 : tm stU 4 = Some (mkAction 4 DL (Some stU));
  hc_U5 : allow5 = true -> tm stU 5 = Some (mkAction 5 DL (Some stU));
  hc_Ud : allow5 = true -> tm stU symB_delim = Some (mkAction symB_delim DL (Some stU));
  (* State L (11) *)
  hc_L0 : tm 11 0 = Some (mkAction 3 DR (Some stO));
  hc_L2 : tm 11 2 = Some (mkAction 2 DL (Some 11));
  hc_L3 : tm 11 3 = Some (mkAction 3 DL (Some 11));
  hc_L4 : tm 11 4 = Some (mkAction 4 DL (Some 11));
  hc_L5 : allow5 = true -> tm 11 5 = Some (mkAction 5 DL (Some 11));
  hc_Ld : allow5 = true -> tm 11 symB_delim = Some (mkAction symB_delim DL (Some 11));
  (* State M (12) *)
  hc_M0 : tm 12 0 = Some (mkAction 3 DL (Some 11));
  hc_M2 : tm 12 2 = Some (mkAction 2 DR (Some 12));
  hc_M3 : tm 12 3 = Some (mkAction 3 DR (Some 12));
  hc_M4 : tm 12 4 = Some (mkAction 4 DR (Some 12));
  hc_M5 : allow5 = true -> tm 12 5 = Some (mkAction 5 DR (Some 12));
  hc_Md : allow5 = true -> tm 12 symB_delim = Some (mkAction symB_delim DR (Some 12));
  (* State N (13) *)
  hc_N0 : tm 13 0 = Some (mkAction 1 DR (Some 1));
  hc_N1 : tm 13 1 = Some (mkAction 1 DL (Some 13));
  hc_N2 : tm 13 2 = Some (mkAction 2 DL (Some 13));
  hc_N3 : tm 13 3 = Some (mkAction 3 DL (Some 13));
  hc_N4 : tm 13 4 = Some (mkAction 1 DL (Some 14));
  hc_N5 : allow5 = true -> tm 13 5 = Some (mkAction 5 DL (Some 13));
  (* State V (14: counter check) *)
  hc_V0 : tm 14 0 = Some (mkAction 1 DR (Some 1));
  hc_V1 : tm 14 1 = Some (mkAction 4 DR (Some 15));
  (* State stO (copy scan right) *)
  hc_O2 : tm stO 2 = Some (mkAction sym2_mark DR (Some 10));
  hc_O3 : tm stO 3 = Some (mkAction 0 DR (Some 12));
  hc_O4 : tm stO 4 = Some (mkAction 4 DL (Some 13));
  hc_O5 : allow5 = true -> tm stO 5 = Some (mkAction sym5_mark DR (Some 16));
  hc_Od : allow5 = true -> tm stO symB_delim = Some (mkAction symB_delim DL (Some 13));
  (* State P (15) *)
  hc_P0 : tm 15 0 = Some (mkAction 4 DL (Some 9));
  hc_P1 : tm 15 1 = Some (mkAction 1 DR (Some 15));
  hc_P2 : tm 15 2 = Some (mkAction 2 DR (Some 15));
  hc_P3 : tm 15 3 = Some (mkAction 3 DR (Some 15));
  hc_P4 : tm 15 4 = Some (mkAction 0 DR (Some 15));
  hc_P5 : allow5 = true -> tm 15 5 = Some (mkAction 5 DR (Some 15));
  hc_Pd : allow5 = true -> tm 15 symB_delim = Some (mkAction symB_delim DR (Some 15));
  (* State Q (16: copy 5 right) *)
  hc_Q0 : allow5 = true -> tm 16 0 = Some (mkAction 5 DL (Some stR));
  hc_Q2 : allow5 = true -> tm 16 2 = Some (mkAction 2 DR (Some 16));
  hc_Q3 : allow5 = true -> tm 16 3 = Some (mkAction 3 DR (Some 16));
  hc_Q4 : allow5 = true -> tm 16 4 = Some (mkAction 4 DR (Some 16));
  hc_Q5 : allow5 = true -> tm 16 5 = Some (mkAction 5 DR (Some 16));
  hc_Qd : allow5 = true -> tm 16 symB_delim = Some (mkAction symB_delim DR (Some 16));
  (* State stR (return from Q) *)
  hc_Rm : allow5 = true -> tm stR sym5_mark = Some (mkAction 5 DR (Some stO));
  hc_R2 : allow5 = true -> tm stR 2 = Some (mkAction 2 DL (Some stR));
  hc_R3 : allow5 = true -> tm stR 3 = Some (mkAction 3 DL (Some stR));
  hc_R4 : allow5 = true -> tm stR 4 = Some (mkAction 4 DL (Some stR));
  hc_R5 : allow5 = true -> tm stR 5 = Some (mkAction 5 DL (Some stR));
  hc_Rd : allow5 = true -> tm stR symB_delim = Some (mkAction symB_delim DL (Some stR));
  (* State stS (expander scan left) *)
  hc_S0 : allow5 = true -> tm stS 0 = Some (mkAction 1 DR (Some 1));
  hc_S1 : allow5 = true -> tm stS 1 = Some (mkAction 4 DR (Some stT));
  hc_S2 : allow5 = true -> tm stS 2 = Some (mkAction 2 DL (Some stS));
  hc_S3 : allow5 = true -> tm stS 3 = Some (mkAction 3 DL (Some stS));
  hc_S4 : allow5 = true -> tm stS 4 = Some (mkAction 4 DL (Some stS));
  hc_S5 : allow5 = true -> tm stS 5 = Some (mkAction 5 DL (Some stS));
  (* State stT (expander scan right) *)
  hc_T0 : allow5 = true -> tm stT 0 = Some (mkAction 2 DL (Some stS));
  hc_T2 : allow5 = true -> tm stT 2 = Some (mkAction 2 DR (Some stT));
  hc_T3 : allow5 = true -> tm stT 3 = Some (mkAction 3 DR (Some stT));
  hc_T4 : allow5 = true -> tm stT 4 = Some (mkAction 4 DR (Some stT));
  hc_T5 : allow5 = true -> tm stT 5 = Some (mkAction 5 DR (Some stT))
}.

(* Standard Concrete Core Specializations *)
Definition Fe0_5_16Core (tm : TM) : Prop :=
  HydraCore tm false 0 2 14 11 13 15 11 9 4 4 0 1 0.

Definition Fe1_6Core (tm : TM) : Prop :=
  HydraCore tm true 14 8 0 17 18 19 20 17 4 1 0 0 0.

Definition Fe1_7Core (tm : TM) : Prop :=
  HydraCore tm true 0 2 14 17 18 19 11 9 6 6 1 1 0.

Definition Fe1_8Core (tm : TM) : Prop :=
  HydraCore tm true 0 2 14 11 17 18 11 9 6 6 1 1 7.

(* Hydra Symbol & Raw Tape Relations *)
Definition IsOp (allow5 : bool) (c : nat) : Prop :=
  c = 2 \/ (allow5 = true /\ c = 5).

Definition IsHydraSym (allow5 : bool) (c : nat) : Prop :=
  IsOp allow5 c \/ c = 3.

Lemma IsHydraSym_pos : forall allow5 c, IsHydraSym allow5 c -> 1 <= c.
Proof.
  intros allow5 c [[-> | [_ ->]] | ->]; lia.
Qed.

Inductive RawCell (allow5 : bool) (symB_delim : nat) : nat -> nat -> Prop :=
  | rc_id  : forall c, IsHydraSym allow5 c -> RawCell allow5 symB_delim c c
  | rc_4   : RawCell allow5 symB_delim 4 2
  | rc_del : allow5 = true -> RawCell allow5 symB_delim symB_delim 5.

Lemma RawCell_clean : forall allow5 d (s : list nat),
  Forall (IsHydraSym allow5) s -> Forall2 (RawCell allow5 d) s s.
Proof.
  intros allow5 d s Hs. induction Hs as [| x xs Hx Hxs IH]; constructor; [apply rc_id; exact Hx | exact IH].
Qed.

Lemma Forall2_app_raw : forall allow5 d r1 s1 r2 s2,
  Forall2 (RawCell allow5 d) r1 s1 ->
  Forall2 (RawCell allow5 d) r2 s2 ->
  Forall2 (RawCell allow5 d) (r1 ++ r2) (s1 ++ s2).
Proof.
  intros allow5 d r1 s1 r2 s2 H1 H2.
  induction H1; simpl; [exact H2 | constructor; assumption].
Qed.

Definition ValidHydraTape (allow5 : bool) (symB_delim : nat) (R_raw s : list nat) : Prop :=
  match R_raw, s with
  | [], [] => True
  | op :: r_tl, op' :: s_tl =>
      op = op' /\ IsOp allow5 op /\ Forall2 (RawCell allow5 symB_delim) r_tl s_tl
  | _, _ => False
  end.

Lemma ValidHydraTape_clean : forall allow5 d op s_tl,
  IsOp allow5 op ->
  Forall (IsHydraSym allow5) s_tl ->
  ValidHydraTape allow5 d (op :: s_tl) (op :: s_tl).
Proof.
  intros allow5 d op s_tl Hop Htl. simpl.
   repeat split; [exact Hop | apply RawCell_clean; exact Htl].
Qed.

Lemma ValidHydraTape_app : forall allow5 d R1 s1 R2 s2,
  s1 <> [] ->
  ValidHydraTape allow5 d R1 s1 ->
  Forall2 (RawCell allow5 d) R2 s2 ->
  ValidHydraTape allow5 d (R1 ++ R2) (s1 ++ s2).
Proof.
  intros allow5 d [| r1 r1_tl] [| op1 s1_tl] R2 s2 Hs1 H1 H2; try contradiction; simpl in *.
  destruct H1 as [-> [Hop Htl]].
  repeat split; [exact Hop | apply Forall2_app_raw; assumption].
Qed.

Lemma walk_R_rep : forall tm q n c w L R,
  1 <= w ->
  tm q c = Some (mkAction w DR (Some q)) ->
  Reaches tm (mkCfgR (Some q) L (rep n c R))
             (mkCfgR (Some q) (rep n w L) R) n.
Proof.
  intros tm q n. induction n as [| n' IH]; intros c w L R Hw Ht; simpl.
  - apply reaches_zero.
  - destruct w as [| w']; [lia |].
    apply (steps_succ tm n' _ (mkCfgR (Some q) (S w' :: L) (rep n' c R))).
    + apply step_mkCfgR_R; exact Ht.
    + rewrite <- rep_snoc_one. apply IH; [lia | exact Ht].
Qed.

Lemma walk_L_rep : forall tm q n c L R,
  1 <= c ->
  tm q c = Some (mkAction c DL (Some q)) ->
  Reaches tm (cfgL q (rep n c L) R)
             (cfgL q L (rep n c R)) n.
Proof.
  intros tm q n. induction n as [| n' IH]; intros c L R Hc Ht; simpl.
  - apply reaches_zero.
  - apply (steps_succ tm n' _ (cfgL q (rep n' c L) (c :: R))).
    + apply step_to_cfgL; assumption.
    + rewrite <- rep_snoc_one. apply IH; assumption.
Qed.

Section HydraRound.
  Variables (tm : TM) (allow5 : bool).
  Variables (stA stB1 stO stR stS stT stU stJRet : nat).
  Variables (symB_mark symB_delim symB_temp sym2_mark sym5_mark : nat).
  Hypothesis HC : HydraCore tm allow5 stA stB1 stO stR stS stT stU stJRet
                            symB_mark symB_delim symB_temp sym2_mark sym5_mark.

  Lemma C_sweep_raw : forall R_raw s L R,
    Forall2 (RawCell allow5 symB_delim) R_raw s ->
    exists t, Reaches tm (mkCfgR (Some 2) L (R_raw ++ R))
                         (mkCfgR (Some 2) (rev s ++ L) R) t.
  Proof.
    intros R_raw s L R Hraw. revert L R.
    induction Hraw as [| r c r_tl s_tl Hrc Htl IH]; intros L R; simpl.
    - exists 0. apply reaches_zero.
    - assert (Hstep : 1 <= c /\ tm 2 r = Some (mkAction c DR (Some 2))).
      { destruct Hrc as [c [[-> | [Ha ->]] | ->] | | Ha].
        - split; [lia | apply (hc_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
        - split; [lia | apply (hc_C5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
        - split; [lia | apply (hc_C3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
        - split; [lia | apply (hc_C4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
        - split; [lia | apply (hc_Cd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      destruct Hstep as [Hc Htr].
      destruct c as [| c']; [lia |].
      destruct (IH (S c' :: L) R) as [t Ht].
      exists (S t).
      apply (steps_succ tm t _ (mkCfgR (Some 2) (S c' :: L) (r_tl ++ R))).
      + apply step_mkCfgR_R; exact Htr.
      + rewrite <- app_assoc; simpl. exact Ht.
  Qed.

  Lemma I_strip_3 : forall k a L,
    exists t, Reaches tm (mkCfgR (Some 8) (rep k 3 (a :: L)) [3])
                         (mkCfgR (Some 8) L [a]) t.
  Proof.
    induction k as [| k' IH]; intros a L; simpl.
    - exists 1. apply reaches_one.
      unfold step, mkCfgR; simpl.
      rewrite (hc_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
    - destruct (IH a L) as [t Ht].
      exists (S t).
      apply (steps_succ tm t _ (mkCfgR (Some 8) (rep k' 3 (a :: L)) [3])).
      + unfold step, mkCfgR; simpl.
        rewrite (hc_I3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
      + exact Ht.
  Qed.

  Lemma C0_I_strip_3 : forall k a L,
    exists t, Reaches tm (mkCfgR (Some 2) (rep k 3 (a :: L)) [])
                         (mkCfgR (Some 8) L [a]) t.
  Proof.
    destruct k as [| k']; intros a L; simpl.
    - exists 1. apply reaches_one.
      unfold step, mkCfgR; simpl.
      rewrite (hc_C0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
    - destruct (I_strip_3 k' a L) as [t Ht].
      exists (S t).
      apply (steps_succ tm t _ (mkCfgR (Some 8) (rep k' 3 (a :: L)) [3])).
      + unfold step, mkCfgR; simpl.
        rewrite (hc_C0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
      + exact Ht.
  Qed.

  Lemma rev_rep_3 : forall k L,
    rev (rep k 3 []) ++ L = rep k 3 L.
  Proof.
    induction k as [| k' IH]; intro L; simpl.
    - reflexivity.
    - rewrite <- app_assoc; simpl. rewrite IH.
      rewrite rep_snoc_one; reflexivity.
  Qed.

  Lemma round_to_I : forall m' R_raw s_pre last_op k,
    ValidHydraTape allow5 symB_delim R_raw (s_pre ++ [last_op] ++ rep k 3 []) ->
    exists t, Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                         (mkCfgR (Some 8) (rev s_pre ++ 4 :: rep m' 1 []) [last_op]) t.
  Proof.
    intros m' R_raw s_pre last_op k Hvalid.
    remember (s_pre ++ [last_op] ++ rep k 3 []) as s_full eqn:Es.
    destruct R_raw as [| op r_tl]; destruct s_full as [| op' s_tl];
      simpl in Hvalid; try contradiction.
    { destruct s_pre; discriminate Es. }
    destruct Hvalid as [<- [Hop Hraw]].
    assert (Hstart : exists t0,
              Reaches tm (mkCfgR (Some 1) (1 :: rep m' 1 []) (op :: r_tl))
                         (mkCfgR (Some 2) (op :: 4 :: rep m' 1 []) r_tl) t0).
    { exists 3.
      destruct Hop as [-> | [Ha ->]].
      - apply (steps_succ tm 2 _ (mkCfgR (Some stB1) (rep m' 1 []) (1 :: 2 :: r_tl))).
        + apply step_mkCfgR_L_cons, (hc_B2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
        + apply (steps_succ tm 1 _ (mkCfgR (Some 2) (4 :: rep m' 1 []) (2 :: r_tl))).
          * apply step_mkCfgR_R, (hc_B1_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
          * apply reaches_one, step_mkCfgR_R, (hc_C2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
      - apply (steps_succ tm 2 _ (mkCfgR (Some stB1) (rep m' 1 []) (1 :: 5 :: r_tl))).
        + apply step_mkCfgR_L_cons, (hc_B5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
        + apply (steps_succ tm 1 _ (mkCfgR (Some 2) (4 :: rep m' 1 []) (5 :: r_tl))).
          * apply step_mkCfgR_R, (hc_B1_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
          * apply reaches_one, step_mkCfgR_R, (hc_C5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
    destruct Hstart as [t0 Ht0].
    pose proof (C_sweep_raw r_tl s_tl (op :: 4 :: rep m' 1 []) [] Hraw) as [t1 Ht1].
    rewrite app_nil_r in Ht1.
    assert (Hrev : rev s_tl ++ op :: 4 :: rep m' 1 [] =
                   rep k 3 (last_op :: rev s_pre ++ 4 :: rep m' 1 [])).
    { replace (rev s_tl ++ op :: 4 :: rep m' 1 []) with (rev (op :: s_tl) ++ 4 :: rep m' 1 [])
        by (simpl; rewrite <- app_assoc; reflexivity).
      rewrite Es.
      rewrite !rev_app_distr. simpl.
      rewrite <- !app_assoc; simpl.
      rewrite rev_rep_3. reflexivity. }
    rewrite Hrev in Ht1.
    destruct (C0_I_strip_3 k last_op (rev s_pre ++ 4 :: rep m' 1 [])) as [t2 Ht2].
    exists (t0 + t1 + t2).
    eapply reaches_trans; [eapply reaches_trans; [exact Ht0 | exact Ht1] | exact Ht2].
  Qed.

  Lemma rep_app_snoc : forall n s xs,
    rep n s [] ++ s :: xs = rep (S n) s xs.
  Proof.
    induction n as [| n' IH]; intros s xs; simpl.
    - reflexivity.
    - rewrite IH; reflexivity.
  Qed.

  Lemma Forall_rep : forall (P : nat -> Prop) n x xs,
    P x -> Forall P xs -> Forall P (rep n x xs).
  Proof.
    intros P n x xs Hx Hxs. induction n as [| n' IH]; simpl; [exact Hxs | constructor; assumption].
  Qed.

  Lemma Forall_app_iff : forall {A : Type} (P : A -> Prop) l1 l2,
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
  Proof.
    intros A P l1 l2 H1 H2. induction H1; simpl; [exact H2 | constructor; assumption].
  Qed.

  Lemma stS_skip_hydra : forall c,
    allow5 = true -> IsHydraSym true c ->
    1 <= c /\ tm stS c = Some (mkAction c DL (Some stS)).
  Proof.
    intros c Ha [[-> | [_ ->]] | ->]; split; try lia.
    - exact (hc_S2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_S5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_S3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
  Qed.

  Lemma stT_skip_hydra : forall c,
    allow5 = true -> IsHydraSym true c ->
    1 <= c /\ tm stT c = Some (mkAction c DR (Some stT)).
  Proof.
    intros c Ha [[-> | [_ ->]] | ->]; split; try lia.
    - exact (hc_T2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_T5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_T3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
  Qed.

  Lemma expand_loop : forall s_pre j r,
    allow5 = true ->
    Forall (IsHydraSym true) s_pre ->
    exists t,
      Reaches tm (cfgL stS (rep (S r) 4 (rep j 1 [])) (s_pre ++ rep (S r) 2 []))
                 (cfgL stS [] (rep (S (r + j)) 4 (s_pre ++ rep (S (r + j)) 2 []))) t.
  Proof.
    intros s_pre j. induction j as [| j' IH]; intros r Ha Hs.
    - rewrite Nat.add_0_r. exists (S r).
      apply walk_L_rep; [lia | exact (hc_S4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - replace (r + S j') with (S r + j') by lia.
      assert (Hbody : Forall (IsHydraSym true) (s_pre ++ rep (S r) 2 [])).
      { apply Forall_app_iff; [exact Hs |].
        apply Forall_rep; [left; left; reflexivity | constructor]. }
      pose proof (walk_L_rep tm stS (S r) 4 (1 :: rep j' 1 []) (s_pre ++ rep (S r) 2 [])
                    ltac:(lia) (hc_S4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)) as H1.
      simpl in H1.
      assert (H2 : Reaches tm (mkCfgR (Some stS) (rep j' 1 []) (1 :: 4 :: rep r 4 (s_pre ++ 2 :: rep r 2 [])))
                              (mkCfgR (Some stT) (4 :: rep j' 1 []) (rep (S r) 4 (s_pre ++ rep (S r) 2 []))) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_S1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      pose proof (walk_R_rep tm stT (S r) 4 4 (4 :: rep j' 1 []) (s_pre ++ rep (S r) 2 [])
                    ltac:(lia) (hc_T4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)) as H3.
      rewrite rep_snoc_one in H3.
      assert (H4 : Reaches tm (mkCfgR (Some stT) (rep (S (S r)) 4 (rep j' 1 [])) ((s_pre ++ rep (S r) 2 []) ++ []))
                              (mkCfgR (Some stT) (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [])
                              (length (s_pre ++ rep (S r) 2 []))).
      { apply walk_R. intros c Hc.
        apply stT_skip_hydra; [exact Ha |].
        rewrite Forall_forall in Hbody. apply Hbody; exact Hc. }
      rewrite app_nil_r in H4.
      assert (H5 : Reaches tm (mkCfgR (Some stT) (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [])
                              (cfgL stS (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [2]) 1).
      { apply reaches_one.
        change (mkCfgR (Some stT) (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [])
          with (mkCfgR (Some stT) (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [0]).
        apply step_to_cfgL; [lia | exact (hc_T0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      assert (H6 : Reaches tm (cfgL stS (rev (s_pre ++ rep (S r) 2 []) ++ rep (S (S r)) 4 (rep j' 1 [])) [2])
                              (cfgL stS (rep (S (S r)) 4 (rep j' 1 [])) ((s_pre ++ rep (S r) 2 []) ++ [2]))
                              (length (s_pre ++ rep (S r) 2 []))).
      { apply walk_L_rev_cfgL. intros c Hc.
        apply stS_skip_hydra; [exact Ha |].
        rewrite Forall_forall in Hbody. apply Hbody; exact Hc. }
      replace ((s_pre ++ rep (S r) 2 []) ++ [2]) with (s_pre ++ rep (S (S r)) 2 []) in H6
        by (rewrite <- app_assoc; f_equal; symmetry; apply (rep_app_snoc (S r) 2 [])).
      destruct (IH (S r) Ha Hs) as [t7 H7].
      eexists.
      eapply reaches_trans; [exact H1 |].
      eapply reaches_trans; [exact H2 |].
      eapply reaches_trans; [exact H3 |].
      eapply reaches_trans; [exact H4 |].
      eapply reaches_trans; [exact H5 |].
      eapply reaches_trans; [exact H6 | exact H7].
  Qed.

  Lemma round_expand_bracket : forall m' R_raw s_pre k,
    allow5 = true ->
    Forall (IsHydraSym true) s_pre ->
    ValidHydraTape true symB_delim R_raw (s_pre ++ [5] ++ rep k 3 []) ->
    exists t, S (S m') <= t /\
      Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                 (mkCfgR (Some 1) (rep (S (S m')) 1 []) (s_pre ++ rep (S m') 2 [])) t.
  Proof.
    intros m' R_raw s_pre k Ha Hs Hvalid.
    rewrite <- Ha in Hvalid.
    destruct (round_to_I m' R_raw s_pre 5 k Hvalid) as [t0 Ht0].
    assert (H1 : Reaches tm (mkCfgR (Some 8) (rev s_pre ++ 4 :: rep m' 1 []) [5])
                            (cfgL stS (rev s_pre ++ 4 :: rep m' 1 []) [2]) 1).
    { apply reaches_one, step_to_cfgL; [lia | exact (hc_I5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
    assert (H2 : Reaches tm (cfgL stS (rev s_pre ++ 4 :: rep m' 1 []) [2])
                            (cfgL stS (4 :: rep m' 1 []) (s_pre ++ [2])) (length s_pre)).
    { apply walk_L_rev_cfgL. intros c Hc.
      apply stS_skip_hydra; [exact Ha |].
      rewrite Forall_forall in Hs. apply Hs; exact Hc. }
    destruct (expand_loop s_pre m' 0 Ha Hs) as [t3 H3].
    simpl in H3.
    assert (H4 : Reaches tm (cfgL stS [] (rep (S m') 4 (s_pre ++ rep (S m') 2 [])))
                            (mkCfgR (Some 1) [1] (rep (S m') 4 (s_pre ++ rep (S m') 2 []))) 1).
    { apply reaches_one, step_mkCfgR_R, (hc_S0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
    pose proof (walk_R_rep tm 1 (S m') 4 1 [1] (s_pre ++ rep (S m') 2 [])
                  ltac:(lia) (hc_B4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)) as H5.
    rewrite rep_snoc_one in H5.
    exists (t0 + 1 + length s_pre + t3 + 1 + S m').
    split; [lia |].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans;
      [exact Ht0 | exact H1] | exact H2] | exact H3] | exact H4] | exact H5].
  Qed.

  Lemma step_mkCfgR_R_cons0 : forall q w nx a L cur R,
    tm q cur = Some (mkAction w DR nx) ->
    step tm (mkCfgR (Some q) (a :: L) (cur :: R)) = Some (mkCfgR nx (w :: a :: L) R).
  Proof.
    intros q w nx a L cur R Ht.
    destruct R; unfold step, mkCfgR; simpl; rewrite Ht; destruct w; reflexivity.
  Qed.

  Lemma non_nil_app : forall {A : Type} (l1 l2 : list A),
    l2 <> [] -> l1 ++ l2 <> [].
  Proof.
    intros A [| x l1'] l2 H2; simpl; [exact H2 | discriminate].
  Qed.

  Inductive Bal : list nat -> Prop :=
    | bal_nil  : Bal []
    | bal_node : forall B1 op B2,
        Bal B1 -> IsOp allow5 op -> Bal B2 ->
        Bal (B1 ++ [op] ++ B2 ++ [3]).

  Lemma Bal_HydraSym : forall B,
    Bal B -> Forall (IsHydraSym allow5) B.
  Proof.
    intros B HB. induction HB as [| B1 op B2 HB1 IHB1 Hop HB2 IHB2].
    - constructor.
    - apply Forall_app_iff; [exact IHB1 |].
      constructor; [left; exact Hop |].
      apply Forall_app_iff; [exact IHB2 |].
      constructor; [right; reflexivity | constructor].
  Qed.

  Lemma D_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 3 c = Some (mkAction c DR (Some 3)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_D2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_D5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_D3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma E_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 4 c = Some (mkAction c DL (Some 4)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma F_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 5 c = Some (mkAction c DR (Some 5)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_F2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_F5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_F3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma H_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 7 c = Some (mkAction c DL (Some 7)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_H5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_H3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma A_push_3 : forall L_rest R k,
    L_rest <> [] ->
    Forall (IsHydraSym allow5) R ->
    exists t,
      Reaches tm (cfgL stA (3 :: L_rest) (R ++ rep k 1 []))
                 (cfgL stA L_rest ((3 :: R) ++ rep (S k) 1 [])) t.
  Proof.
    intros L_rest R k HL HR.
    destruct L_rest as [| a L']; [contradiction |].
    assert (H1 : Reaches tm (cfgL stA (3 :: a :: L') (R ++ rep k 1 []))
                            (mkCfgR (Some 3) (0 :: a :: L') (R ++ rep k 1 [])) 1).
    { apply reaches_one, step_mkCfgR_R_cons0, (hc_A3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
    assert (H2 : Reaches tm (mkCfgR (Some 3) (0 :: a :: L') (R ++ rep k 1 []))
                            (mkCfgR (Some 3) (rev R ++ 0 :: a :: L') (rep k 1 [])) (length R)).
    { apply walk_R. intros c Hc. apply D_skip_hydra.
      rewrite Forall_forall in HR. apply HR; exact Hc. }
    pose proof (walk_R_rep tm 3 k 1 1 (rev R ++ 0 :: a :: L') []
                  ltac:(lia) (hc_D1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H3.
    assert (H4 : Reaches tm (mkCfgR (Some 3) (rep k 1 (rev R ++ 0 :: a :: L')) [])
                            (cfgL 4 (rep k 1 (rev R ++ 0 :: a :: L')) [1]) 1).
    { apply reaches_one.
      change (mkCfgR (Some 3) (rep k 1 (rev R ++ 0 :: a :: L')) [])
        with (mkCfgR (Some 3) (rep k 1 (rev R ++ 0 :: a :: L')) [0]).
      apply step_to_cfgL; [lia | exact (hc_D0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
    pose proof (walk_L_rep tm 4 k 1 (rev R ++ 0 :: a :: L') [1]
                  ltac:(lia) (hc_E1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H5.
    assert (H6 : Reaches tm (cfgL 4 (rev R ++ 0 :: a :: L') (rep k 1 [1]))
                            (cfgL 4 (0 :: a :: L') (R ++ rep (S k) 1 [])) (length R)).
    { replace (rep k 1 [1]) with (rep (S k) 1 []) by (rewrite rep_snoc_one; reflexivity).
      apply walk_L_rev_cfgL. intros c Hc. apply E_skip_hydra.
      rewrite Forall_forall in HR. apply HR; exact Hc. }
    assert (H7 : Reaches tm (cfgL 4 (0 :: a :: L') (R ++ rep (S k) 1 []))
                            (cfgL stA (a :: L') ((3 :: R) ++ rep (S k) 1 [])) 1).
    { apply reaches_one, step_to_cfgL; [lia | exact (hc_E0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
    eexists.
    eapply reaches_trans; [exact H1 |].
    eapply reaches_trans; [exact H2 |].
    eapply reaches_trans; [exact H3 |].
    eapply reaches_trans; [exact H4 |].
    eapply reaches_trans; [exact H5 |].
    eapply reaches_trans; [exact H6 | exact H7].
  Qed.

  Lemma A_pop_op : forall op L_rest R k,
    IsOp allow5 op ->
    L_rest <> [] ->
    Forall (IsHydraSym allow5) R ->
    exists t,
      Reaches tm (cfgL stA (op :: L_rest) (R ++ rep (S k) 1 []))
                 (cfgL stA L_rest ((op :: R) ++ rep k 1 [])) t.
  Proof.
    intros op L_rest R k Hop HL HR.
    destruct L_rest as [| a L']; [contradiction |].
    set (mark := if Nat.eqb op 2 then 0 else symB_mark).
    assert (H1 : Reaches tm (cfgL stA (op :: a :: L') (R ++ rep (S k) 1 []))
                            (mkCfgR (Some 5) (mark :: a :: L') (R ++ rep (S k) 1 [])) 1).
    { destruct Hop as [-> | [Ha ->]]; unfold mark.
      - apply reaches_one, step_mkCfgR_R_cons0, (hc_A2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
      - apply reaches_one, step_mkCfgR_R_cons0, (hc_A5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
    assert (H2 : Reaches tm (mkCfgR (Some 5) (mark :: a :: L') (R ++ rep (S k) 1 []))
                            (mkCfgR (Some 5) (rev R ++ mark :: a :: L') (rep (S k) 1 [])) (length R)).
    { apply walk_R. intros c Hc. apply F_skip_hydra.
      rewrite Forall_forall in HR. apply HR; exact Hc. }
    pose proof (walk_R_rep tm 5 (S k) 1 1 (rev R ++ mark :: a :: L') []
                  ltac:(lia) (hc_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H3.
    assert (H4 : Reaches tm (mkCfgR (Some 5) (rep (S k) 1 (rev R ++ mark :: a :: L')) [])
                            (cfgL 7 (rep k 1 (rev R ++ mark :: a :: L')) []) 2).
    { apply (steps_succ tm 1 _ (mkCfgR (Some 6) (rep k 1 (rev R ++ mark :: a :: L')) [1])).
      - unfold step, mkCfgR; simpl.
        rewrite (hc_F0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
      - apply reaches_one.
        destruct k as [| k']; simpl.
        + destruct (rev R) as [| r0 r_tl]; simpl;
          unfold step, mkCfgR; simpl;
          rewrite (hc_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
        + unfold step, mkCfgR; simpl.
          rewrite (hc_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity. }
    pose proof (walk_L_rep tm 7 k 1 (rev R ++ mark :: a :: L') []
                  ltac:(lia) (hc_H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H5.
    assert (H6 : Reaches tm (cfgL 7 (rev R ++ mark :: a :: L') (rep k 1 []))
                            (cfgL 7 (mark :: a :: L') (R ++ rep k 1 [])) (length R)).
    { apply walk_L_rev_cfgL. intros c Hc. apply H_skip_hydra.
      rewrite Forall_forall in HR. apply HR; exact Hc. }
    assert (H7 : Reaches tm (cfgL 7 (mark :: a :: L') (R ++ rep k 1 []))
                            (cfgL stA (a :: L') ((op :: R) ++ rep k 1 [])) 1).
    { destruct Hop as [-> | [Ha ->]]; unfold mark.
      - apply reaches_one, step_to_cfgL; [lia | exact (hc_H0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
      - apply reaches_one, step_to_cfgL; [lia | exact (hc_Hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
    eexists.
    eapply reaches_trans; [exact H1 |].
    eapply reaches_trans; [exact H2 |].
    eapply reaches_trans; [exact H3 |].
    eapply reaches_trans; [exact H4 |].
    eapply reaches_trans; [exact H5 |].
    eapply reaches_trans; [exact H6 | exact H7].
  Qed.

  Lemma A_skip_bal : forall B L_tail R k,
    Bal B ->
    L_tail <> [] ->
    Forall (IsHydraSym allow5) R ->
    exists t,
      Reaches tm (cfgL stA (rev B ++ L_tail) (R ++ rep k 1 []))
                 (cfgL stA L_tail ((B ++ R) ++ rep k 1 [])) t.
  Proof.
    intros B L_tail R k HB. revert L_tail R k.
    induction HB as [| B1 op B2 HB1 IHB1 Hop HB2 IHB2]; intros L_tail R k HL HR.
    - simpl. exists 0. apply reaches_zero.
    - assert (Hrev : rev (B1 ++ [op] ++ B2 ++ [3]) ++ L_tail =
                     3 :: rev B2 ++ op :: rev B1 ++ L_tail).
      { rewrite !rev_app_distr; simpl. rewrite <- !app_assoc; reflexivity. }
      rewrite Hrev.
      assert (HL2 : rev B2 ++ op :: rev B1 ++ L_tail <> [])
        by (apply non_nil_app; discriminate).
      destruct (A_push_3 (rev B2 ++ op :: rev B1 ++ L_tail) R k HL2 HR) as [t1 H1].
      assert (HL1 : op :: rev B1 ++ L_tail <> []) by discriminate.
      assert (HR3 : Forall (IsHydraSym allow5) (3 :: R))
        by (constructor; [right; reflexivity | exact HR]).
      destruct (IHB2 (op :: rev B1 ++ L_tail) (3 :: R) (S k) HL1 HR3) as [t2 H2].
      assert (HL0 : rev B1 ++ L_tail <> []) by (apply non_nil_app; exact HL).
      assert (HR2 : Forall (IsHydraSym allow5) (B2 ++ 3 :: R))
        by (apply Forall_app_iff; [apply Bal_HydraSym; exact HB2 | exact HR3]).
      destruct (A_pop_op op (rev B1 ++ L_tail) (B2 ++ 3 :: R) k Hop HL0 HR2) as [t3 H3].
      assert (HR1 : Forall (IsHydraSym allow5) (op :: B2 ++ 3 :: R))
        by (constructor; [left; exact Hop | exact HR2]).
      destruct (IHB1 L_tail (op :: B2 ++ 3 :: R) k HL HR1) as [t4 H4].
      replace ((B1 ++ op :: B2 ++ 3 :: R) ++ rep k 1 [])
        with (((B1 ++ [op] ++ B2 ++ [3]) ++ R) ++ rep k 1 []) in H4
        by (repeat (rewrite <- app_assoc; simpl); reflexivity).
      exists (t1 + t2 + t3 + t4).
      eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans;
        [exact H1 | exact H2] | exact H3] | exact H4].
  Qed.

  Lemma round_pop_top_paren : forall m' R_raw bal_pre k,
    Bal bal_pre ->
    ValidHydraTape allow5 symB_delim R_raw (bal_pre ++ [2] ++ rep k 3 []) ->
    exists t, S (S m') <= t /\
      Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                 (mkCfgR (Some 1) (rep (S (S m')) 1 []) bal_pre) t.
  Proof.
    intros m' R_raw bal_pre k Hbal Hvalid.
    destruct (round_to_I m' R_raw bal_pre 2 k Hvalid) as [t0 Ht0].
    assert (H1 : Reaches tm (mkCfgR (Some 8) (rev bal_pre ++ 4 :: rep m' 1 []) [2])
                            (cfgL stA (rev bal_pre ++ 4 :: rep m' 1 []) ([] ++ rep 0 1 [])) 1).
    { apply reaches_one.
      destruct (rev bal_pre) as [| a l']; simpl;
      unfold step, mkCfgR; simpl;
      rewrite (hc_I2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity. }
    assert (HL : 4 :: rep m' 1 [] <> []) by discriminate.
    destruct (A_skip_bal bal_pre (4 :: rep m' 1 []) [] 0 Hbal HL (Forall_nil _)) as [t2 H2].
    rewrite !app_nil_r in H2.
    assert (H3 : Reaches tm (cfgL stA (4 :: rep m' 1 []) bal_pre)
                            (cfgL 13 (rep m' 1 []) (1 :: bal_pre)) 1).
    { apply reaches_one, step_to_cfgL; [lia | exact (hc_A4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
    pose proof (walk_L_rep tm 13 m' 1 [] (1 :: bal_pre)
                  ltac:(lia) (hc_N1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H4.
    rewrite rep_snoc_one in H4.
    assert (H5 : Reaches tm (cfgL 13 [] (rep (S m') 1 bal_pre))
                            (mkCfgR (Some 1) [1] (rep (S m') 1 bal_pre)) 1).
    { apply reaches_one, step_mkCfgR_R, (hc_N0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
    pose proof (walk_R_rep tm 1 (S m') 1 1 [1] bal_pre
                  ltac:(lia) (hc_B1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H6.
    rewrite rep_snoc_one in H6.
    exists (t0 + 1 + t2 + 1 + m' + 1 + S m').
    split; [lia |].
    eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans; [eapply reaches_trans;
      [eapply reaches_trans; [eapply reaches_trans;
      [exact Ht0 | exact H1] | exact H2] | exact H3] | exact H4] | exact H5] | exact H6].
  Qed.

  (* ======================================================================= *)
  (* Completion 3: Parent Copy Round (J, stO, K/stU, M/L, Q/stR, N, V, P)    *)
  (* ======================================================================= *)

  Fixpoint rep_app (n : nat) (pat : list nat) : list nat :=
    match n with
    | 0 => []
    | S n' => pat ++ rep_app n' pat
    end.

  Lemma rep_app_snoc_r : forall n pat,
    rep_app n pat ++ pat = rep_app (S n) pat.
  Proof.
    induction n as [| n' IH]; intro pat; simpl.
    - symmetry; apply app_nil_r.
    - rewrite <- app_assoc, IH; reflexivity.
  Qed.

  Lemma Forall_rep_app : forall (P : nat -> Prop) n pat,
    Forall P pat -> Forall P (rep_app n pat).
  Proof.
    intros P n pat Hpat. induction n as [| n' IH]; simpl; [constructor | apply Forall_app_iff; assumption].
  Qed.

  Definition IsCopyMidSym (d_op c : nat) : Prop :=
    IsHydraSym allow5 c \/ c = d_op.

  Lemma d_op_valid : forall op,
    IsOp allow5 op ->
    (if Nat.eqb op 2 then 4 else symB_delim) = 4 \/
    (allow5 = true /\ (if Nat.eqb op 2 then 4 else symB_delim) = symB_delim).
  Proof.
    intros op [-> | [Ha ->]]; simpl; [left; reflexivity | right; split; [exact Ha | reflexivity]].
  Qed.

  Lemma K_skip_mid : forall op c,
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm 10 c = Some (mkAction c DR (Some 10)).
  Proof.
    intros op c Hop [[[-> | [Ha ->]] | ->] | ->].
    - split; [lia | exact (hc_K2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - split; [lia | exact (hc_K5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_K3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - destruct (d_op_valid op Hop) as [-> | [Ha ->]].
      + split; [lia | exact (hc_K4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Kd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma stU_skip_mid : forall op c,
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm stU c = Some (mkAction c DL (Some stU)).
  Proof.
    intros op c Hop [[[-> | [Ha ->]] | ->] | ->].
    - split; [lia | exact (hc_U2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - split; [lia | exact (hc_U5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_U3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - destruct (d_op_valid op Hop) as [-> | [Ha ->]].
      + split; [lia | exact (hc_U4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Ud _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma M_skip_mid : forall op c,
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm 12 c = Some (mkAction c DR (Some 12)).
  Proof.
    intros op c Hop [[[-> | [Ha ->]] | ->] | ->].
    - split; [lia | exact (hc_M2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - split; [lia | exact (hc_M5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_M3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - destruct (d_op_valid op Hop) as [-> | [Ha ->]].
      + split; [lia | exact (hc_M4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma L_skip_mid : forall op c,
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm 11 c = Some (mkAction c DL (Some 11)).
  Proof.
    intros op c Hop [[[-> | [Ha ->]] | ->] | ->].
    - split; [lia | exact (hc_L2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - split; [lia | exact (hc_L5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_L3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
    - destruct (d_op_valid op Hop) as [-> | [Ha ->]].
      + split; [lia | exact (hc_L4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Ld _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma Q_skip_mid : forall op c,
    allow5 = true ->
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm 16 c = Some (mkAction c DR (Some 16)).
  Proof.
    intros op c Ha Hop [[[-> | [_ ->]] | ->] | ->].
    - split; [lia | exact (hc_Q2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_Q5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_Q3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - destruct (d_op_valid op Hop) as [-> | [_ ->]].
      + split; [lia | exact (hc_Q4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Qd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma stR_skip_mid : forall op c,
    allow5 = true ->
    IsOp allow5 op ->
    IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim) c ->
    1 <= c /\ tm stR c = Some (mkAction c DL (Some stR)).
  Proof.
    intros op c Ha Hop [[[-> | [_ ->]] | ->] | ->].
    - split; [lia | exact (hc_R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_R5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - split; [lia | exact (hc_R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
    - destruct (d_op_valid op Hop) as [-> | [_ ->]].
      + split; [lia | exact (hc_R4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
      + split; [exact (proj1 (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha))
               | exact (hc_Rd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)].
  Qed.

  Lemma O_copy_one : forall op c L_left mid,
    IsOp allow5 op ->
    L_left <> [] ->
    IsHydraSym allow5 c ->
    Forall (IsCopyMidSym (if Nat.eqb op 2 then 4 else symB_delim)) mid ->
    exists t,
      Reaches tm (mkCfgR (Some stO) L_left (c :: mid))
                 (mkCfgR (Some stO) (c :: L_left) (mid ++ [c])) t.
  Proof.
    intros op c L_left mid Hop HL Hc Hmid.
    destruct L_left as [| a L']; [contradiction |].
    destruct Hc as [[-> | [Ha ->]] | ->].
    - (* c = 2 *)
      assert (H1 : Reaches tm (mkCfgR (Some stO) (a :: L') (2 :: mid))
                              (mkCfgR (Some 10) (sym2_mark :: a :: L') (mid ++ [])) 1).
      { rewrite app_nil_r. apply reaches_one, step_mkCfgR_R_cons0, (hc_O2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      assert (H2 : Reaches tm (mkCfgR (Some 10) (sym2_mark :: a :: L') (mid ++ []))
                              (mkCfgR (Some 10) (rev mid ++ sym2_mark :: a :: L') []) (length mid)).
      { apply walk_R. intros x Hx. apply (K_skip_mid op x Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H3 : Reaches tm (mkCfgR (Some 10) (rev mid ++ sym2_mark :: a :: L') [])
                              (cfgL stU (rev mid ++ sym2_mark :: a :: L') [2]) 1).
      { apply reaches_one.
        change (mkCfgR (Some 10) (rev mid ++ sym2_mark :: a :: L') [])
          with (mkCfgR (Some 10) (rev mid ++ sym2_mark :: a :: L') [0]).
        apply step_to_cfgL; [lia | exact (hc_K0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
      assert (H4 : Reaches tm (cfgL stU (rev mid ++ sym2_mark :: a :: L') [2])
                              (cfgL stU (sym2_mark :: a :: L') (mid ++ [2])) (length mid)).
      { apply walk_L_rev_cfgL. intros x Hx. apply (stU_skip_mid op x Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H5 : Reaches tm (cfgL stU (sym2_mark :: a :: L') (mid ++ [2]))
                              (mkCfgR (Some stO) (2 :: a :: L') (mid ++ [2])) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_Um _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      eexists.
      eapply reaches_trans; [exact H1 |].
      eapply reaches_trans; [exact H2 |].
      eapply reaches_trans; [exact H3 |].
      eapply reaches_trans; [exact H4 | exact H5].
    - (* c = 5 *)
      assert (H1 : Reaches tm (mkCfgR (Some stO) (a :: L') (5 :: mid))
                              (mkCfgR (Some 16) (sym5_mark :: a :: L') (mid ++ [])) 1).
      { rewrite app_nil_r. apply reaches_one, step_mkCfgR_R_cons0, (hc_O5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      assert (H2 : Reaches tm (mkCfgR (Some 16) (sym5_mark :: a :: L') (mid ++ []))
                              (mkCfgR (Some 16) (rev mid ++ sym5_mark :: a :: L') []) (length mid)).
      { apply walk_R. intros x Hx. apply (Q_skip_mid op x Ha Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H3 : Reaches tm (mkCfgR (Some 16) (rev mid ++ sym5_mark :: a :: L') [])
                              (cfgL stR (rev mid ++ sym5_mark :: a :: L') [5]) 1).
      { apply reaches_one.
        change (mkCfgR (Some 16) (rev mid ++ sym5_mark :: a :: L') [])
          with (mkCfgR (Some 16) (rev mid ++ sym5_mark :: a :: L') [0]).
        apply step_to_cfgL; [lia | exact (hc_Q0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      assert (H4 : Reaches tm (cfgL stR (rev mid ++ sym5_mark :: a :: L') [5])
                              (cfgL stR (sym5_mark :: a :: L') (mid ++ [5])) (length mid)).
      { apply walk_L_rev_cfgL. intros x Hx. apply (stR_skip_mid op x Ha Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H5 : Reaches tm (cfgL stR (sym5_mark :: a :: L') (mid ++ [5]))
                              (mkCfgR (Some stO) (5 :: a :: L') (mid ++ [5])) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_Rm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      eexists.
      eapply reaches_trans; [exact H1 |].
      eapply reaches_trans; [exact H2 |].
      eapply reaches_trans; [exact H3 |].
      eapply reaches_trans; [exact H4 | exact H5].
    - (* c = 3 *)
      assert (H1 : Reaches tm (mkCfgR (Some stO) (a :: L') (3 :: mid))
                              (mkCfgR (Some 12) (0 :: a :: L') (mid ++ [])) 1).
      { rewrite app_nil_r. apply reaches_one, step_mkCfgR_R_cons0, (hc_O3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      assert (H2 : Reaches tm (mkCfgR (Some 12) (0 :: a :: L') (mid ++ []))
                              (mkCfgR (Some 12) (rev mid ++ 0 :: a :: L') []) (length mid)).
      { apply walk_R. intros x Hx. apply (M_skip_mid op x Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H3 : Reaches tm (mkCfgR (Some 12) (rev mid ++ 0 :: a :: L') [])
                              (cfgL 11 (rev mid ++ 0 :: a :: L') [3]) 1).
      { apply reaches_one.
        change (mkCfgR (Some 12) (rev mid ++ 0 :: a :: L') [])
          with (mkCfgR (Some 12) (rev mid ++ 0 :: a :: L') [0]).
        apply step_to_cfgL; [lia | exact (hc_M0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
      assert (H4 : Reaches tm (cfgL 11 (rev mid ++ 0 :: a :: L') [3])
                              (cfgL 11 (0 :: a :: L') (mid ++ [3])) (length mid)).
      { apply walk_L_rev_cfgL. intros x Hx. apply (L_skip_mid op x Hop).
        rewrite Forall_forall in Hmid. apply Hmid; exact Hx. }
      assert (H5 : Reaches tm (cfgL 11 (0 :: a :: L') (mid ++ [3]))
                              (mkCfgR (Some stO) (3 :: a :: L') (mid ++ [3])) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_L0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      eexists.
      eapply reaches_trans; [exact H1 |].
      eapply reaches_trans; [exact H2 |].
      eapply reaches_trans; [exact H3 |].
      eapply reaches_trans; [exact H4 | exact H5].
  Qed.

  Lemma O_copy_pass : forall op rem L_left done_copy,
    IsOp allow5 op ->
    L_left <> [] ->
    Forall (IsHydraSym allow5) rem ->
    Forall (IsHydraSym allow5) done_copy ->
    let d_op := if Nat.eqb op 2 then 4 else symB_delim in
    exists t,
      Reaches tm (mkCfgR (Some stO) L_left (rem ++ d_op :: done_copy))
                 (mkCfgR (Some stO) (rev rem ++ L_left) (d_op :: done_copy ++ rem)) t.
  Proof.
    intros op rem. induction rem as [| c rem' IH]; intros L_left done_copy Hop HL Hrem Hdone d_op; simpl.
    - rewrite app_nil_r. exists 0. apply reaches_zero.
    - inversion Hrem as [| ? ? Hc Hrem']; subst.
      assert (Hmid : Forall (IsCopyMidSym d_op) (rem' ++ d_op :: done_copy)).
      { apply Forall_app_iff.
        - eapply Forall_impl; [| exact Hrem']. intros x Hx; left; exact Hx.
        - constructor; [right; reflexivity |].
          eapply Forall_impl; [| exact Hdone]. intros x Hx; left; exact Hx. }
      destruct (O_copy_one op c L_left (rem' ++ d_op :: done_copy) Hop HL Hc Hmid) as [t1 H1].
      replace ((rem' ++ d_op :: done_copy) ++ [c])
        with (rem' ++ d_op :: (done_copy ++ [c])) in H1
        by (rewrite <- !app_assoc; reflexivity).
      assert (HL' : c :: L_left <> []) by discriminate.
      assert (Hdone' : Forall (IsHydraSym allow5) (done_copy ++ [c]))
        by (apply Forall_app_iff; [exact Hdone | constructor; [exact Hc | constructor]]).
      destruct (IH (c :: L_left) (done_copy ++ [c]) Hop HL' Hrem' Hdone') as [t2 H2].
      replace (rev rem' ++ c :: L_left) with ((rev rem' ++ [c]) ++ L_left) in H2
        by (rewrite <- app_assoc; reflexivity).
      replace ((done_copy ++ [c]) ++ rem') with (done_copy ++ c :: rem') in H2
        by (rewrite <- app_assoc; reflexivity).
      exists (t1 + t2). eapply reaches_trans; eassumption.
  Qed.

  Lemma J_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 9 c = Some (mkAction c DL (Some 9)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_J2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_J5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_J3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma stJRet_skip_hydra : forall c,
    allow5 = true ->
    IsHydraSym allow5 c -> 1 <= c /\ tm stJRet c = Some (mkAction c DL (Some stJRet)).
  Proof.
    intros c Ha [[-> | [_ ->]] | ->]; split; try lia.
    - exact (hc_JR2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_JR5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_JR3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
  Qed.

  Lemma N_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 13 c = Some (mkAction c DL (Some 13)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_N2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_N5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_N3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma P_skip_hydra : forall c,
    IsHydraSym allow5 c -> 1 <= c /\ tm 15 c = Some (mkAction c DR (Some 15)).
  Proof.
    intros c [[-> | [Ha ->]] | ->]; split; try lia.
    - exact (hc_P2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (hc_P5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
    - exact (hc_P3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma J_setup_copy : forall op body mark_c L_pre,
    IsOp allow5 op ->
    Forall (IsHydraSym allow5) body ->
    L_pre <> [] ->
    ((op = 2 /\ mark_c = 0) \/
     (allow5 = true /\ op = 5 /\ (mark_c = symB_mark \/ mark_c = symB_delim))) ->
    let d_op := if Nat.eqb op 2 then 4 else symB_delim in
    exists t,
      Reaches tm (cfgL 9 (rev (body ++ [3]) ++ mark_c :: L_pre) [4])
                 (mkCfgR (Some stO) (op :: L_pre) ((body ++ [3]) ++ [d_op])) t.
  Proof.
    intros op body mark_c L_pre Hop Hbody HL Hmark d_op.
    destruct L_pre as [| a L']; [contradiction |].
    assert (Hb3 : Forall (IsHydraSym allow5) (body ++ [3]))
      by (apply Forall_app_iff; [exact Hbody | constructor; [right; reflexivity | constructor]]).
    assert (H1 : Reaches tm (cfgL 9 (rev (body ++ [3]) ++ mark_c :: a :: L') [4])
                            (cfgL 9 (mark_c :: a :: L') ((body ++ [3]) ++ [4]))
                            (length (body ++ [3]))).
    { apply walk_L_rev_cfgL. intros c Hc. apply J_skip_hydra.
      rewrite Forall_forall in Hb3. apply Hb3; exact Hc. }
    destruct Hmark as [[-> ->] | [Ha [-> Hm]]].
    - unfold d_op; simpl.
      assert (H2 : Reaches tm (cfgL 9 (0 :: a :: L') ((body ++ [3]) ++ [4]))
                              (mkCfgR (Some stO) (2 :: a :: L') ((body ++ [3]) ++ [4])) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_J0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      exists (length (body ++ [3]) + 1). eapply reaches_trans; eassumption.
    - unfold d_op; simpl.
      pose proof (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha) as [Hd _].
      assert (H2 : Reaches tm (cfgL 9 (mark_c :: a :: L') ((body ++ [3]) ++ [4]))
                              (mkCfgR (Some 5) (symB_temp :: a :: L') ((body ++ [3]) ++ [4])) 1).
      { destruct Hm as [-> | ->].
        - apply reaches_one, step_mkCfgR_R_cons0, (hc_Jm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
        - apply reaches_one, step_mkCfgR_R_cons0, (hc_Jd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      assert (H3 : Reaches tm (mkCfgR (Some 5) (symB_temp :: a :: L') ((body ++ [3]) ++ [4]))
                              (mkCfgR (Some 5) (rev (body ++ [3]) ++ symB_temp :: a :: L') [4])
                              (length (body ++ [3]))).
      { apply walk_R. intros c Hc. apply F_skip_hydra.
        rewrite Forall_forall in Hb3. apply Hb3; exact Hc. }
      assert (H4 : Reaches tm (mkCfgR (Some 5) (rev (body ++ [3]) ++ symB_temp :: a :: L') [4])
                              (cfgL stJRet (rev (body ++ [3]) ++ symB_temp :: a :: L') [symB_delim]) 1).
      { apply reaches_one, step_to_cfgL; [exact Hd | exact (hc_F4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      assert (H5 : Reaches tm (cfgL stJRet (rev (body ++ [3]) ++ symB_temp :: a :: L') [symB_delim])
                              (cfgL stJRet (symB_temp :: a :: L') ((body ++ [3]) ++ [symB_delim]))
                              (length (body ++ [3]))).
      { apply walk_L_rev_cfgL. intros c Hc. apply (stJRet_skip_hydra c Ha).
        rewrite Forall_forall in Hb3. apply Hb3; exact Hc. }
      assert (H6 : Reaches tm (cfgL stJRet (symB_temp :: a :: L') ((body ++ [3]) ++ [symB_delim]))
                              (mkCfgR (Some stO) (5 :: a :: L') ((body ++ [3]) ++ [symB_delim])) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_JRt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      eexists.
      eapply reaches_trans; [exact H1 |].
      eapply reaches_trans; [exact H2 |].
      eapply reaches_trans; [exact H3 |].
      eapply reaches_trans; [exact H4 |].
      eapply reaches_trans; [exact H5 | exact H6].
  Qed.

  Lemma copy_loop : forall op body j r done_hydra,
    IsOp allow5 op ->
    Forall (IsHydraSym allow5) body ->
    Forall (IsHydraSym allow5) done_hydra ->
    let d_op := if Nat.eqb op 2 then 4 else symB_delim in
    let pat := [op] ++ body ++ [3] in
    exists t, S (S (r + j)) <= t /\
      Reaches tm (mkCfgR (Some stO) (rev done_hydra ++ rep r 1 (4 :: rep j 1 [])) (d_op :: body ++ [3]))
                 (mkCfgR (Some 1) (rep (S (S (r + j))) 1 [])
                         (done_hydra ++ rep_app j pat ++ (d_op :: body ++ [3]))) t.
  Proof.
    intros op body j. induction j as [| j' IH]; intros r done_hydra Hop Hbody Hdone d_op pat.
    - rewrite Nat.add_0_r. simpl (rep_app 0 pat ++ _).
      assert (H1 : Reaches tm (mkCfgR (Some stO) (rev done_hydra ++ rep r 1 [4]) (d_op :: body ++ [3]))
                              (cfgL 13 (rev done_hydra ++ rep r 1 [4]) (d_op :: body ++ [3])) 1).
      { unfold d_op. destruct Hop as [-> | [Ha ->]]; simpl.
        - apply reaches_one, step_to_cfgL; [lia | exact (hc_O4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
        - pose proof (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha) as [Hd _].
          apply reaches_one, step_to_cfgL; [exact Hd | exact (hc_Od _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      assert (H2 : Reaches tm (cfgL 13 (rev done_hydra ++ rep r 1 [4]) (d_op :: body ++ [3]))
                              (cfgL 13 (rep r 1 [4]) (done_hydra ++ d_op :: body ++ [3]))
                              (length done_hydra)).
      { apply walk_L_rev_cfgL. intros c Hc. apply N_skip_hydra.
        rewrite Forall_forall in Hdone. apply Hdone; exact Hc. }
      pose proof (walk_L_rep tm 13 r 1 [4] (done_hydra ++ d_op :: body ++ [3])
                    ltac:(lia) (hc_N1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H3.
      assert (H4 : Reaches tm (cfgL 13 [4] (rep r 1 (done_hydra ++ d_op :: body ++ [3])))
                              (cfgL 14 [] (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3]))) 1).
      { apply reaches_one, step_to_cfgL; [lia | exact (hc_N4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
      assert (H5 : Reaches tm (cfgL 14 [] (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3])))
                              (mkCfgR (Some 1) [1] (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3]))) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_V0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      pose proof (walk_R_rep tm 1 (S r) 1 1 [1] (done_hydra ++ d_op :: body ++ [3])
                    ltac:(lia) (hc_B1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H6.
      rewrite rep_snoc_one in H6.
      eexists. split; [| eapply reaches_trans; [exact H1 |];
                         eapply reaches_trans; [exact H2 |];
                         eapply reaches_trans; [exact H3 |];
                         eapply reaches_trans; [exact H4 |];
                         eapply reaches_trans; [exact H5 | exact H6]].
      lia.
    - replace (r + S j') with (S r + j') by lia.
      assert (Hb3 : Forall (IsHydraSym allow5) (body ++ [3]))
        by (apply Forall_app_iff; [exact Hbody | constructor; [right; reflexivity | constructor]]).
      assert (Hpat : Forall (IsHydraSym allow5) pat)
        by (unfold pat; constructor; [left; exact Hop | exact Hb3]).
      assert (H1 : Reaches tm (mkCfgR (Some stO) (rev done_hydra ++ rep r 1 (4 :: 1 :: rep j' 1 [])) (d_op :: body ++ [3]))
                              (cfgL 13 (rev done_hydra ++ rep r 1 (4 :: 1 :: rep j' 1 [])) (d_op :: body ++ [3])) 1).
      { unfold d_op. destruct Hop as [-> | [Ha ->]]; simpl.
        - apply reaches_one, step_to_cfgL; [lia | exact (hc_O4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)].
        - pose proof (hc_delim_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha) as [Hd _].
          apply reaches_one, step_to_cfgL; [exact Hd | exact (hc_Od _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha)]. }
      assert (H2 : Reaches tm (cfgL 13 (rev done_hydra ++ rep r 1 (4 :: 1 :: rep j' 1 [])) (d_op :: body ++ [3]))
                              (cfgL 13 (rep r 1 (4 :: 1 :: rep j' 1 [])) (done_hydra ++ d_op :: body ++ [3]))
                              (length done_hydra)).
      { apply walk_L_rev_cfgL. intros c Hc. apply N_skip_hydra.
        rewrite Forall_forall in Hdone. apply Hdone; exact Hc. }
      pose proof (walk_L_rep tm 13 r 1 (4 :: 1 :: rep j' 1 []) (done_hydra ++ d_op :: body ++ [3])
                    ltac:(lia) (hc_N1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H3.
      assert (H4 : Reaches tm (cfgL 13 (4 :: 1 :: rep j' 1 []) (rep r 1 (done_hydra ++ d_op :: body ++ [3])))
                              (cfgL 14 (1 :: rep j' 1 []) (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3]))) 1).
      { apply reaches_one, step_to_cfgL; [lia | exact (hc_N4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
      assert (H5 : Reaches tm (cfgL 14 (1 :: rep j' 1 []) (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3])))
                              (mkCfgR (Some 15) (4 :: rep j' 1 []) (rep (S r) 1 (done_hydra ++ d_op :: body ++ [3]))) 1).
      { apply reaches_one, step_mkCfgR_R, (hc_V1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
      pose proof (walk_R_rep tm 15 (S r) 1 1 (4 :: rep j' 1 []) (done_hydra ++ d_op :: body ++ [3])
                    ltac:(lia) (hc_P1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H6.
      assert (H7 : Reaches tm (mkCfgR (Some 15) (rep (S r) 1 (4 :: rep j' 1 [])) (done_hydra ++ d_op :: body ++ [3]))
                              (mkCfgR (Some 15) (rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) (d_op :: body ++ [3]))
                              (length done_hydra)).
      { apply walk_R. intros c Hc. apply P_skip_hydra.
        rewrite Forall_forall in Hdone. apply Hdone; exact Hc. }
      set (mark_next := if Nat.eqb op 2 then 0 else symB_delim).
      assert (H8 : Reaches tm (mkCfgR (Some 15) (rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) (d_op :: body ++ [3]))
                              (mkCfgR (Some 15) (mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) ((body ++ [3]) ++ [])) 1).
      { rewrite app_nil_r.
        destruct (rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) as [| x0 xs0] eqn:Enon.
        - exfalso. eapply (non_nil_app (rev done_hydra) (rep (S r) 1 (4 :: rep j' 1 []))); [discriminate | exact Enon].
        - unfold d_op, mark_next. destruct Hop as [-> | [Ha ->]]; simpl.
          + apply reaches_one, step_mkCfgR_R_cons0, (hc_P4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
          + apply reaches_one, step_mkCfgR_R_cons0, (hc_Pd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
      assert (H9 : Reaches tm (mkCfgR (Some 15) (mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) ((body ++ [3]) ++ []))
                              (mkCfgR (Some 15) (rev (body ++ [3]) ++ mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) [])
                              (length (body ++ [3]))).
      { apply walk_R. intros c Hc. apply P_skip_hydra.
        rewrite Forall_forall in Hb3. apply Hb3; exact Hc. }
      assert (H10 : Reaches tm (mkCfgR (Some 15) (rev (body ++ [3]) ++ mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) [])
                               (cfgL 9 (rev (body ++ [3]) ++ mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) [4]) 1).
      { apply reaches_one.
        change (mkCfgR (Some 15) (rev (body ++ [3]) ++ mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) [])
          with (mkCfgR (Some 15) (rev (body ++ [3]) ++ mark_next :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) [0]).
        apply step_to_cfgL; [lia | exact (hc_P0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
      assert (HL_next : rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 []) <> [])
        by (apply non_nil_app; discriminate).
      assert (Hm_next : (op = 2 /\ mark_next = 0) \/
                        (allow5 = true /\ op = 5 /\ (mark_next = symB_mark \/ mark_next = symB_delim))).
      { unfold mark_next; destruct Hop as [-> | [Ha ->]]; simpl;
          [left; split; reflexivity | right; split; [exact Ha | split; [reflexivity | right; reflexivity]]]. }
      destruct (J_setup_copy op body mark_next (rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 []))
                  Hop Hbody HL_next Hm_next) as [t11 H11].
      assert (HL_O : op :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 []) <> []) by discriminate.
      destruct (O_copy_pass op (body ++ [3]) (op :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 [])) []
                  Hop HL_O Hb3 (Forall_nil _)) as [t12 H12].
      fold d_op in H11, H12.
      replace (rev (body ++ [3]) ++ op :: rev done_hydra ++ rep (S r) 1 (4 :: rep j' 1 []))
        with (rev (done_hydra ++ pat) ++ rep (S r) 1 (4 :: rep j' 1 [])) in H12
        by (unfold pat; rewrite !rev_app_distr; simpl; rewrite <- !app_assoc; reflexivity).
      assert (Hdone' : Forall (IsHydraSym allow5) (done_hydra ++ pat))
        by (apply Forall_app_iff; [exact Hdone | exact Hpat]).
      destruct (IH (S r) (done_hydra ++ pat) Hop Hbody Hdone') as [t13 [Ht13 H13]].
      fold d_op pat in H13.
      replace ((done_hydra ++ pat) ++ rep_app j' pat ++ d_op :: body ++ [3])
        with (done_hydra ++ (pat ++ rep_app j' pat) ++ d_op :: body ++ [3]) in H13
        by (rewrite <- !app_assoc; reflexivity).
      eexists. split; [| eapply reaches_trans; [exact H1 |];
                         eapply reaches_trans; [exact H2 |];
                         eapply reaches_trans; [exact H3 |];
                         eapply reaches_trans; [exact H4 |];
                         eapply reaches_trans; [exact H5 |];
                         eapply reaches_trans; [exact H6 |];
                         eapply reaches_trans; [exact H7 |];
                         eapply reaches_trans; [exact H8 |];
                         eapply reaches_trans; [exact H9 |];
                         eapply reaches_trans; [exact H10 |];
                         eapply reaches_trans; [exact H11 |];
                         eapply reaches_trans; [exact H12 | exact H13]].
      lia.
  Qed.

  Lemma Bal_last_3 : forall B,
    Bal B -> B = [] \/ exists B', rev B = 3 :: B'.
  Proof.
    intros B HB. destruct HB as [| B1 op B2 _ _ _].
    - left; reflexivity.
    - right. rewrite !rev_app_distr; simpl. eexists; reflexivity.
  Qed.

  Lemma round_copy_parent : forall m' R_raw pre op body k,
    Forall (IsHydraSym allow5) pre ->
    IsOp allow5 op ->
    Bal body ->
    ValidHydraTape allow5 symB_delim R_raw ((pre ++ [op] ++ body) ++ [2] ++ rep k 3 []) ->
    exists t R_raw', S (S m') <= t /\
      ValidHydraTape allow5 symB_delim R_raw' (pre ++ rep_app (S (S m')) ([op] ++ body ++ [3])) /\
      Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                 (mkCfgR (Some 1) (rep (S (S m')) 1 []) R_raw') t.
  Proof.
    intros m' R_raw pre op body k Hpre Hop Hbody Hvalid.
    assert (Hbody_sym : Forall (IsHydraSym allow5) body) by (apply Bal_HydraSym; exact Hbody).
    assert (Hb3 : Forall (IsHydraSym allow5) (body ++ [3]))
      by (apply Forall_app_iff; [exact Hbody_sym | constructor; [right; reflexivity | constructor]]).
    set (pat := [op] ++ body ++ [3]).
    assert (Hpat : Forall (IsHydraSym allow5) pat)
      by (unfold pat; constructor; [left; exact Hop | exact Hb3]).
    (* Extract that the first symbol of pre ++ pat is an opener from Hvalid *)
    assert (Hfirst_op : exists op0 tl0, pre ++ pat = op0 :: tl0 /\ IsOp allow5 op0).
    { destruct pre as [| p0 pre_tl]; simpl in *.
      - exists op, (body ++ [3]); split; [reflexivity | exact Hop].
      - destruct R_raw as [| r0 r_tl]; simpl in Hvalid; [contradiction |].
        destruct Hvalid as [-> [Hp0 _]].
        exists p0, (pre_tl ++ pat); split; [reflexivity | exact Hp0]. }
    destruct (round_to_I m' R_raw (pre ++ [op] ++ body) 2 k Hvalid) as [t0 Ht0].
    replace (rev (pre ++ [op] ++ body) ++ 4 :: rep m' 1 [])
      with (rev body ++ op :: rev pre ++ 4 :: rep m' 1 []) in Ht0
      by (rewrite !rev_app_distr; simpl; rewrite <- !app_assoc; reflexivity).
    assert (H1 : Reaches tm (mkCfgR (Some 8) (rev body ++ op :: rev pre ++ 4 :: rep m' 1 []) [2])
                            (cfgL stA (rev body ++ op :: rev pre ++ 4 :: rep m' 1 []) ([] ++ rep 0 1 [])) 1).
    { apply reaches_one.
      destruct (rev body) as [| b0 b_tl]; simpl;
      unfold step, mkCfgR; simpl;
      rewrite (hc_I2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity. }
    assert (HL_op : op :: rev pre ++ 4 :: rep m' 1 [] <> []) by discriminate.
    destruct (A_skip_bal body (op :: rev pre ++ 4 :: rep m' 1 []) [] 0 Hbody HL_op (Forall_nil _)) as [t2 H2].
    rewrite !app_nil_r in H2.
    set (mark0 := if Nat.eqb op 2 then 0 else symB_mark).
    assert (H3 : Reaches tm (cfgL stA (op :: rev pre ++ 4 :: rep m' 1 []) body)
                            (mkCfgR (Some 5) (mark0 :: rev pre ++ 4 :: rep m' 1 []) (body ++ [])) 1).
    { rewrite app_nil_r.
      destruct (rev pre ++ 4 :: rep m' 1 []) as [| x0 xs0] eqn:Enon.
      - exfalso. eapply (non_nil_app (rev pre) (4 :: rep m' 1 [])); [discriminate | exact Enon].
      - unfold mark0; destruct Hop as [-> | [Ha ->]].
        + apply reaches_one, step_mkCfgR_R_cons0, (hc_A2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
        + apply reaches_one, step_mkCfgR_R_cons0, (hc_A5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha). }
    assert (H4 : Reaches tm (mkCfgR (Some 5) (mark0 :: rev pre ++ 4 :: rep m' 1 []) (body ++ []))
                            (mkCfgR (Some 5) (rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [])
                            (length body)).
    { apply walk_R. intros c Hc. apply F_skip_hydra.
      rewrite Forall_forall in Hbody_sym. apply Hbody_sym; exact Hc. }
    assert (H5 : Reaches tm (mkCfgR (Some 5) (rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [])
                            (mkCfgR (Some 8) (rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) []) 2).
    { destruct (Bal_last_3 body Hbody) as [-> | [B' EB']].
      - apply (steps_succ tm 1 _ (mkCfgR (Some 6) (rev pre ++ 4 :: rep m' 1 []) [mark0])).
        + unfold step, mkCfgR; simpl.
          rewrite (hc_F0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
        + apply reaches_one.
          destruct (rev pre ++ 4 :: rep m' 1 []) as [| x0 xs0] eqn:Enon.
          * exfalso. eapply (non_nil_app (rev pre) (4 :: rep m' 1 [])); [discriminate | exact Enon].
          * unfold mark0; destruct Hop as [-> | [Ha ->]].
            -- apply step_mkCfgR_R_cons0, (hc_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
            -- apply step_mkCfgR_R_cons0, (hc_Gm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC Ha).
      - rewrite EB'.
        apply (steps_succ tm 1 _ (mkCfgR (Some 6) (B' ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [3])).
        + unfold step, mkCfgR; simpl.
          rewrite (hc_F0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC); reflexivity.
        + apply reaches_one, step_mkCfgR_R, (hc_G3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
    assert (H6 : Reaches tm (mkCfgR (Some 8) (rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [])
                            (cfgL 9 (rev (body ++ [3]) ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [4]) 2).
    { replace (rev (body ++ [3]) ++ mark0 :: rev pre ++ 4 :: rep m' 1 [])
        with (3 :: rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 [])
        by (rewrite rev_app_distr; reflexivity).
      apply (steps_succ tm 1 _ (mkCfgR (Some 15) (3 :: rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [])).
      - apply step_mkCfgR_R_nil, (hc_I0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC).
      - apply reaches_one.
        change (mkCfgR (Some 15) (3 :: rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [])
          with (mkCfgR (Some 15) (3 :: rev body ++ mark0 :: rev pre ++ 4 :: rep m' 1 []) [0]).
        apply step_to_cfgL; [lia | exact (hc_P0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)]. }
    assert (HL_pre : rev pre ++ 4 :: rep m' 1 [] <> [])
      by (apply non_nil_app; discriminate).
    assert (Hm0 : (op = 2 /\ mark0 = 0) \/
                  (allow5 = true /\ op = 5 /\ (mark0 = symB_mark \/ mark0 = symB_delim))).
    { unfold mark0; destruct Hop as [-> | [Ha ->]]; simpl;
        [left; split; reflexivity | right; split; [exact Ha | split; [reflexivity | left; reflexivity]]]. }
    set (d_op := if Nat.eqb op 2 then 4 else symB_delim).
    destruct (J_setup_copy op body mark0 (rev pre ++ 4 :: rep m' 1 []) Hop Hbody_sym HL_pre Hm0) as [t7 H7].
    fold d_op in H7.
    destruct (O_copy_pass op (body ++ [3]) (op :: rev pre ++ 4 :: rep m' 1 []) []
                Hop HL_op Hb3 (Forall_nil _)) as [t8 H8].
    fold d_op in H8.
    replace (rev (body ++ [3]) ++ op :: rev pre ++ 4 :: rep m' 1 [])
      with (rev (pre ++ pat) ++ rep 0 1 (4 :: rep m' 1 [])) in H8
      by (unfold pat; rewrite !rev_app_distr; simpl; rewrite <- !app_assoc; reflexivity).
    assert (Hdone0 : Forall (IsHydraSym allow5) (pre ++ pat))
      by (apply Forall_app_iff; [exact Hpre | exact Hpat]).
    destruct (copy_loop op body m' 0 (pre ++ pat) Hop Hbody_sym Hdone0) as [t9 [Ht9 H9]].
    fold d_op pat in H9. simpl (0 + m') in Ht9, H9.
    set (R_raw' := (pre ++ pat) ++ rep_app m' pat ++ d_op :: body ++ [3]).
    assert (Hvalid' : ValidHydraTape allow5 symB_delim R_raw' (pre ++ rep_app (S (S m')) pat)).
    { unfold R_raw'.
      replace (pre ++ rep_app (S (S m')) pat)
        with (((pre ++ pat) ++ rep_app m' pat) ++ pat)
        by (change (rep_app (S (S m')) pat) with (pat ++ rep_app (S m') pat);
            rewrite <- (rep_app_snoc_r m' pat), <- !app_assoc; reflexivity).
      replace ((pre ++ pat) ++ rep_app m' pat ++ d_op :: body ++ [3])
        with (((pre ++ pat) ++ rep_app m' pat) ++ (d_op :: body ++ [3]))
        by (rewrite <- !app_assoc; reflexivity).
      apply ValidHydraTape_app.
      - destruct Hfirst_op as [op0 [tl0 [E0 _]]]. rewrite E0; discriminate.
      - destruct Hfirst_op as [op0 [tl0 [E0 Hop0]]].
        assert (Hclean_l : Forall (IsHydraSym allow5) ((pre ++ pat) ++ rep_app m' pat))
          by (apply Forall_app_iff; [exact Hdone0 | apply Forall_rep_app; exact Hpat]).
        rewrite E0 in Hclean_l |- *; simpl in *.
        inversion Hclean_l; subst.
        apply ValidHydraTape_clean; assumption.
      - unfold pat; simpl. constructor.
        + unfold d_op; destruct Hop as [-> | [Ha ->]]; simpl; [apply rc_4 | apply rc_del; exact Ha].
        + apply RawCell_clean; exact Hb3. }
    eexists. exists R_raw'.
    split; [| split; [exact Hvalid' |]].
    2: { eapply reaches_trans; [exact Ht0 |].
         eapply reaches_trans; [exact H1 |].
         eapply reaches_trans; [exact H2 |].
         eapply reaches_trans; [exact H3 |].
         eapply reaches_trans; [exact H4 |].
         eapply reaches_trans; [exact H5 |].
         eapply reaches_trans; [exact H6 |].
         eapply reaches_trans; [exact H7 |].
         eapply reaches_trans; [exact H8 | exact H9]. }
    lia.
  Qed.

  (* ======================================================================= *)
  (* Part 4: Higher-Order Simulation (strip3_rev, TapSim, CSim, eval_succ)   *)
  (* ======================================================================= *)

  Fixpoint strip3_rev (l : list nat) : list nat :=
    match l with
    | 3 :: l' => strip3_rev l'
    | _ => l
    end.

  Lemma strip3_rev_3 : forall s,
    strip3_rev (rev (s ++ [3])) = strip3_rev (rev s).
  Proof.
    intro s. rewrite rev_app_distr; reflexivity.
  Qed.

  Lemma strip3_rev_rep3 : forall k s,
    strip3_rev (rev (s ++ rep k 3 [])) = strip3_rev (rev s).
  Proof.
    induction k as [| k' IH]; intro s.
    - rewrite app_nil_r; reflexivity.
    - replace (s ++ rep (S k') 3 []) with ((s ++ [3]) ++ rep k' 3 [])
        by (rewrite <- app_assoc; reflexivity).
      rewrite IH, strip3_rev_3; reflexivity.
  Qed.

  Lemma strip3_rev_spec : forall l,
    exists k, l = rep k 3 (strip3_rev l).
  Proof.
    induction l as [| x l' [k IH]]; simpl.
    - exists 0; reflexivity.
    - destruct x as [|[|[|[|x']]]]; try (exists 0; reflexivity).
      exists (S k); simpl; f_equal; exact IH.
  Qed.

  Lemma rev_rep3_cons : forall n a l,
    rev (rep n 3 (a :: l)) = rev l ++ [a] ++ rep n 3 [].
  Proof.
    induction n as [| n' IH]; intros a l; simpl.
    - reflexivity.
    - rewrite IH, <- !app_assoc; simpl.
      rewrite rep_app_snoc; reflexivity.
  Qed.

  Lemma strip3_rev_decompose : forall s last_op s_pre,
    strip3_rev (rev s) = last_op :: rev s_pre ->
    exists k, s = s_pre ++ [last_op] ++ rep k 3 [].
  Proof.
    intros s last_op s_pre H.
    destruct (strip3_rev_spec (rev s)) as [k Hk].
    rewrite H in Hk.
    exists k.
    rewrite <- (rev_involutive s), Hk, rev_rep3_cons, rev_involutive.
    reflexivity.
  Qed.

  Lemma strip3_rev_app : forall l1 l2,
    strip3_rev l1 <> [] ->
    strip3_rev (l1 ++ l2) = strip3_rev l1 ++ l2.
  Proof.
    induction l1 as [| x l1' IH]; intros l2 Hne; simpl in *.
    - contradiction.
    - destruct x as [|[|[|[|x']]]]; try reflexivity.
      apply IH; exact Hne.
  Qed.

  Lemma strip3_rev_app_rev : forall pre P1 P2,
    strip3_rev (rev P1) <> [] ->
    strip3_rev (rev P1) = strip3_rev (rev P2) ->
    strip3_rev (rev (pre ++ P1)) = strip3_rev (rev (pre ++ P2)).
  Proof.
    intros pre P1 P2 Hne Heq.
    rewrite !rev_app_distr.
    rewrite (strip3_rev_app (rev P1) (rev pre) Hne).
    assert (Hne2 : strip3_rev (rev P2) <> []) by congruence.
    rewrite (strip3_rev_app (rev P2) (rev pre) Hne2).
    rewrite Heq; reflexivity.
  Qed.

  Lemma strip3_rev_snoc_op : forall l op,
    IsOp allow5 op -> strip3_rev (l ++ [op]) <> [].
  Proof.
    induction l as [| x l' IH]; intros op Hop; simpl.
    - destruct Hop as [-> | [_ ->]]; simpl; discriminate.
    - destruct x as [|[|[|[|x']]]]; try discriminate.
      apply IH; exact Hop.
  Qed.

  Definition IsOpenParent (P : list nat) : Prop :=
    exists op body, P = [op] ++ body /\ IsOp allow5 op /\ Bal body.

  Lemma IsOpenParent_Bal3 : forall P,
    IsOpenParent P -> Bal (P ++ [3]).
  Proof.
    intros P [op [body [-> [Hop Hbody]]]].
    change (([op] ++ body) ++ [3]) with ([] ++ [op] ++ body ++ [3]).
    apply bal_node; [apply bal_nil | exact Hop | exact Hbody].
  Qed.

  Lemma Bal_app : forall B1 B2,
    Bal B1 -> Bal B2 -> Bal (B1 ++ B2).
  Proof.
    intros B1 B2 HB1 HB2. induction HB2 as [| C1 op C2 HC1 IHC1 Hop HC2 _].
    - rewrite app_nil_r; exact HB1.
    - replace (B1 ++ C1 ++ [op] ++ C2 ++ [3])
        with ((B1 ++ C1) ++ [op] ++ C2 ++ [3])
        by (rewrite <- !app_assoc; reflexivity).
      apply bal_node; assumption.
  Qed.

  Lemma Bal_rep_app : forall r P,
    IsOpenParent P -> Bal (rep_app r (P ++ [3])).
  Proof.
    induction r as [| r' IH]; intros P HP; simpl.
    - apply bal_nil.
    - apply Bal_app; [apply IsOpenParent_Bal3; exact HP | apply IH; exact HP].
  Qed.

  Lemma IsOpenParent_HydraSym : forall P,
    IsOpenParent P -> Forall (IsHydraSym allow5) P.
  Proof.
    intros P [op [body [-> [Hop Hbody]]]].
    constructor; [left; exact Hop | apply Bal_HydraSym; exact Hbody].
  Qed.

  Lemma IsOpenParent_strip3_nonempty : forall P,
    IsOpenParent P -> strip3_rev (rev P) <> [].
  Proof.
    intros P [op [body [-> [Hop _]]]].
    simpl. apply strip3_rev_snoc_op; exact Hop.
  Qed.

  Lemma IsOpenParent_snoc_child : forall Q P,
    IsOpenParent Q -> IsOpenParent P -> IsOpenParent (Q ++ P ++ [3]).
  Proof.
    intros Q P [opQ [bodyQ [-> [HopQ HbodyQ]]]] [opP [bodyP [-> [HopP HbodyP]]]].
    exists opQ, (bodyQ ++ [opP] ++ bodyP ++ [3]).
    split; [simpl; reflexivity |].
    split; [exact HopQ | apply bal_node; assumption].
  Qed.

  Lemma IsOpenParent_rep_app : forall r Q P,
    IsOpenParent Q -> IsOpenParent P ->
    IsOpenParent (Q ++ rep_app r (P ++ [3])).
  Proof.
    intros r Q P HQ HP. destruct HQ as [opQ [bodyQ [-> [HopQ HbodyQ]]]].
    exists opQ, (bodyQ ++ rep_app r (P ++ [3])).
    split; [simpl; reflexivity |].
    split; [exact HopQ | apply Bal_app; [exact HbodyQ | apply Bal_rep_app; exact HP]].
  Qed.

  Lemma iter_poly_snoc : forall {A : Type} (f : A -> A) n x,
    iter_poly f n (f x) = iter_poly f (S n) x.
  Proof.
    intros A f n. induction n as [| n' IH]; intro x; simpl.
    - reflexivity.
    - rewrite IH; reflexivity.
  Qed.

  Definition TapSim (f : nat -> nat) (s_target s_source : list nat) : Prop :=
    forall m' s_tape R_raw,
      strip3_rev (rev s_tape) = strip3_rev (rev s_source) ->
      ValidHydraTape allow5 symB_delim R_raw s_tape ->
      exists t R_raw',
        f (S m') <= t /\
        ValidHydraTape allow5 symB_delim R_raw' s_target /\
        Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                   (mkCfgR (Some 1) (rep (f (S m')) 1 []) R_raw') t.

  Fixpoint CSim (k : nat) : HType k -> list nat -> Prop :=
    match k with
    | 0 => fun (f : HType 0) (P : list nat) =>
        MonoH 0 f /\
        IsOpenParent P /\
        forall B_ext, Bal B_ext ->
          TapSim f B_ext (B_ext ++ P)
    | S k' => fun (F : HType k' -> HType k') (P : list nat) =>
        MonoH (S k') F /\
        IsOpenParent P /\
        forall (g : HType k') (Q : list nat),
          CSim k' g Q -> CSim k' (F g) (Q ++ P ++ [3])
    end.

  Lemma CSim_MonoH : forall k (x : HType k) P,
    CSim k x P -> MonoH k x.
  Proof.
    destruct k as [| k']; intros x P [Hm _]; exact Hm.
  Qed.

  Lemma CSim_OpenParent : forall k (x : HType k) P,
    CSim k x P -> IsOpenParent P.
  Proof.
    destruct k as [| k']; intros x P [_ [Hp _]]; exact Hp.
  Qed.

  Lemma CSim_LeH : forall k (x1 x2 : HType k) P,
    MonoH k x2 -> LeH k x1 x2 -> CSim k x2 P -> CSim k x1 P.
  Proof.
    induction k as [| k' IH]; intros x1 x2 P Hm2 Hle Hsim.
    (* Note: we actually need the direction LeH k x1 x2 -> CSim k x1 P -> ... wait:
       in TapSim, f (S m') is the EXACT counter value rep (f (S m')) 1 [],
       so CSim is for the exact function x! *)
  Abort.

  Definition OneRoundStep (P_source : list nat) (P_step : nat -> list nat) : Prop :=
    forall pre_outer m' s_tape R_raw,
      Forall (IsHydraSym allow5) pre_outer ->
      strip3_rev (rev s_tape) = strip3_rev (rev (pre_outer ++ P_source)) ->
      ValidHydraTape allow5 symB_delim R_raw s_tape ->
      exists t s_next R_raw',
        S (S m') <= t /\
        strip3_rev (rev s_next) = strip3_rev (rev (pre_outer ++ P_step (S m'))) /\
        ValidHydraTape allow5 symB_delim R_raw' s_next /\
        Reaches tm (mkCfgR (Some 1) (rep (S m') 1 []) R_raw)
                   (mkCfgR (Some 1) (rep (S (S m')) 1 []) R_raw') t.

  Lemma CSim_eval_succ : forall k (G : nat -> HType k) P_source (P_step : nat -> list nat),
    IsOpenParent P_source ->
    (forall m, CSim k (G m) (P_step m)) ->
    (forall m1 m2, m1 <= m2 -> LeH k (G m1) (G m2)) ->
    OneRoundStep P_source P_step ->
    CSim k (eval_succ k G) P_source.
  Proof.
    induction k as [| k' IH]; intros G P_source P_step HP Hsim Hmono Hstep.
    - split; [| split; [exact HP |]].
      + apply (proj1 (proj2 (eval_succ_MonoH_and_LeH 0 G G
                              (fun m => CSim_MonoH 0 (G m) (P_step m) (Hsim m))
                              (fun m => CSim_MonoH 0 (G m) (P_step m) (Hsim m))
                              Hmono) Hmono)).
      + intros B_ext HB m' s_tape R_raw Hstrip Hvalid.
        assert (HB_sym : Forall (IsHydraSym allow5) B_ext) by (apply Bal_HydraSym; exact HB).
        destruct (Hstep B_ext m' s_tape R_raw HB_sym Hstrip Hvalid)
          as [t1 [s_next [R_raw1 [Ht1 [Hstrip1 [Hvalid1 Hreach1]]]]]].
        destruct (Hsim (S m')) as [Hm_step [_ Htap_step]].
        destruct (Htap_step B_ext HB (S m') s_next R_raw1 Hstrip1 Hvalid1)
          as [t2 [R_raw2 [Ht2 [Hvalid2 Hreach2]]]].
        exists (t1 + t2), R_raw2.
        split; [simpl; lia | split; [exact Hvalid2 | eapply reaches_trans; eassumption]].
    - split; [| split; [exact HP |]].
      + apply (proj1 (proj2 (eval_succ_MonoH_and_LeH (S k') G G
                              (fun m => CSim_MonoH (S k') (G m) (P_step m) (Hsim m))
                              (fun m => CSim_MonoH (S k') (G m) (P_step m) (Hsim m))
                              Hmono) Hmono)).
      + intros g Q HQ.
        assert (Hg : MonoH k' g) by (apply (CSim_MonoH k' g Q HQ)).
        assert (HQ_op : IsOpenParent Q) by (apply (CSim_OpenParent k' g Q HQ)).
        change (eval_succ (S k') G g) with (eval_succ k' (fun m => G m g)).
        apply (IH (fun m => G m g) (Q ++ P_source ++ [3]) (fun m => Q ++ P_step m ++ [3])).
        * apply IsOpenParent_snoc_child; assumption.
        * intro m. destruct (Hsim m) as [_ [_ Happly]]. apply Happly; exact HQ.
        * intros m1 m2 Hm. apply (Hmono m1 m2 Hm g g Hg Hg (LeH_refl k' g Hg)).
        * intros pre_outer m' s_tape R_raw Hpre Hstrip Hvalid.
          assert (HpreQ : Forall (IsHydraSym allow5) (pre_outer ++ Q))
            by (apply Forall_app_iff; [exact Hpre | apply IsOpenParent_HydraSym; exact HQ_op]).
          assert (Hstrip' : strip3_rev (rev s_tape) = strip3_rev (rev ((pre_outer ++ Q) ++ P_source))).
          { rewrite Hstrip.
            replace (pre_outer ++ Q ++ P_source ++ [3])
              with (((pre_outer ++ Q) ++ P_source) ++ [3])
              by (rewrite <- !app_assoc; reflexivity).
            apply strip3_rev_3. }
          destruct (Hstep (pre_outer ++ Q) m' s_tape R_raw HpreQ Hstrip' Hvalid)
            as [t1 [s_next [R_raw1 [Ht1 [Hstrip1 [Hvalid1 Hreach1]]]]]].
          exists t1, s_next, R_raw1.
          split; [exact Ht1 | split; [| split; [exact Hvalid1 | exact Hreach1]]].
          rewrite Hstrip1.
          replace (pre_outer ++ Q ++ P_step (S m') ++ [3])
            with (((pre_outer ++ Q) ++ P_step (S m')) ++ [3])
            by (rewrite <- !app_assoc; reflexivity).
          symmetry; apply strip3_rev_3.
  Qed.

  Lemma CSim0_rep_app : forall f P r',
    CSim 0 f P ->
    forall B_ext, Bal B_ext ->
      TapSim (iter_poly f (S r')) B_ext (B_ext ++ rep_app (S r') (P ++ [3])).
  Proof.
    intros f P r' [Hmf [HP Htap]].
    induction r' as [| r'' IH]; intros B_ext HB m' s_tape R_raw Hstrip Hvalid.
    - simpl in *.
      assert (Hstrip' : strip3_rev (rev s_tape) = strip3_rev (rev (B_ext ++ P))).
      { rewrite Hstrip, app_nil_r.
        replace (B_ext ++ P ++ [3]) with ((B_ext ++ P) ++ [3])
          by (rewrite <- app_assoc; reflexivity).
        apply strip3_rev_3. }
      apply (Htap B_ext HB m' s_tape R_raw Hstrip' Hvalid).
    - assert (HB' : Bal (B_ext ++ rep_app (S r'') (P ++ [3]))).
      { apply Bal_app; [exact HB | apply Bal_rep_app; exact HP]. }
      assert (Hstrip1 : strip3_rev (rev s_tape) =
                        strip3_rev (rev ((B_ext ++ rep_app (S r'') (P ++ [3])) ++ P))).
      { rewrite Hstrip.
        replace (B_ext ++ rep_app (S (S r'')) (P ++ [3]))
          with (((B_ext ++ rep_app (S r'') (P ++ [3])) ++ P) ++ [3])
          by (rewrite <- (rep_app_snoc_r (S r'') (P ++ [3])), <- !app_assoc; reflexivity).
        apply strip3_rev_3. }
      destruct (Htap (B_ext ++ rep_app (S r'') (P ++ [3])) HB' m' s_tape R_raw Hstrip1 Hvalid)
        as [t1 [R_raw1 [Ht1 [Hvalid1 Hreach1]]]].
      pose proof (proj1 Hmf (S m')) as Hpos1.
      destruct (f (S m')) as [| m1] eqn:Em1; [lia |].
      destruct (IH B_ext HB m1 (B_ext ++ rep_app (S r'') (P ++ [3])) R_raw1 eq_refl Hvalid1)
        as [t2 [R_raw2 [Ht2 [Hvalid2 Hreach2]]]].
      rewrite <- Em1 in Hreach1, Ht2, Hreach2.
      rewrite (iter_poly_snoc f (S r'') (S m')) in Ht2, Hreach2.
      exists (t1 + t2), R_raw2.
      split; [lia | split; [exact Hvalid2 | eapply reaches_trans; eassumption]].
  Qed.

  Lemma CSim_rep_app : forall k' (F : HType (S k')) P (g : HType k') Q r',
    CSim (S k') F P ->
    CSim k' g Q ->
    CSim k' (iter_poly F (S r') g) (Q ++ rep_app (S r') (P ++ [3])).
  Proof.
    intros k' F P g Q r' [HmF [HP Happly]] HQ.
    revert g Q HQ.
    induction r' as [| r'' IH]; intros g Q HQ.
    - simpl. rewrite app_nil_r. apply Happly; exact HQ.
    - replace (Q ++ rep_app (S (S r'')) (P ++ [3]))
        with ((Q ++ rep_app (S r'') (P ++ [3])) ++ P ++ [3])
        by (rewrite <- (rep_app_snoc_r (S r'') (P ++ [3])), <- !app_assoc; reflexivity).
      change (iter_poly F (S (S r'')) g) with (F (iter_poly F (S r'') g)).
      apply Happly, IH; exact HQ.
  Qed.

  Lemma IsOpenParent_2 : IsOpenParent [2].
  Proof.
    exists 2, []; split; [reflexivity | split; [left; reflexivity | apply bal_nil]].
  Qed.

  Lemma IsOpenParent_5 : allow5 = true -> IsOpenParent [5].
  Proof.
    intro Ha. exists 5, []; split; [reflexivity | split; [right; split; [exact Ha | reflexivity] | apply bal_nil]].
  Qed.

  Lemma OneRoundStep_copy_parent : forall P,
    IsOpenParent P ->
    OneRoundStep (P ++ [2] ++ [3]) (fun m => rep_app (S m) (P ++ [3])).
  Proof.
    intros P [op [body [-> [Hop Hbody]]]] pre_outer m' s_tape R_raw Hpre Hstrip Hvalid.
    assert (Hrev : strip3_rev (rev s_tape) = 2 :: rev (pre_outer ++ [op] ++ body)).
    { rewrite Hstrip.
      replace (pre_outer ++ ([op] ++ body) ++ [2] ++ [3])
        with (((pre_outer ++ [op] ++ body) ++ [2]) ++ [3])
        by (rewrite <- !app_assoc; reflexivity).
      rewrite strip3_rev_3, rev_app_distr; reflexivity. }
    destruct (strip3_rev_decompose s_tape 2 (pre_outer ++ [op] ++ body) Hrev) as [k Es].
    subst s_tape.
    destruct (round_copy_parent m' R_raw pre_outer op body k Hpre Hop Hbody Hvalid)
      as [t [R_raw' [Ht [Hvalid' Hreach']]]].
    exists t, (pre_outer ++ rep_app (S (S m')) ([op] ++ body ++ [3])), R_raw'.
    split; [exact Ht | split; [reflexivity | split; [exact Hvalid' | exact Hreach']]].
  Qed.

  Lemma CSim_baseP : forall k, CSim k (baseP k) [2].
  Proof.
    destruct k as [| [| k']].
    - (* k = 0 *)
      split; [apply (baseP_MonoH 0) | split; [apply IsOpenParent_2 |]].
      intros B_ext HB m' s_tape R_raw Hstrip Hvalid.
      rewrite rev_app_distr in Hstrip; simpl in Hstrip.
      destruct (strip3_rev_decompose s_tape 2 B_ext Hstrip) as [k Es].
      subst s_tape.
      destruct (round_pop_top_paren m' R_raw B_ext k HB Hvalid) as [t [Ht Hreach]].
      exists t, B_ext.
      split; [exact Ht | split; [| exact Hreach]].
      assert (Hall : Forall (IsHydraSym allow5) B_ext) by (apply Bal_HydraSym; exact HB).
      destruct B_ext as [| b0 b_tl]; [exact I |].
      destruct R_raw as [| r0 r_tl]; simpl in Hvalid; [contradiction |].
      destruct Hvalid as [-> [Hop_b0 _]].
      inversion Hall; subst.
      apply ValidHydraTape_clean; assumption.
    - (* k = 1: stepH 0 *)
      split; [apply (stepH_MonoH 0) | split; [apply IsOpenParent_2 |]].
      intros g Q HQ.
      assert (Hg : MonoH 0 g) by (apply (CSim_MonoH 0 g Q HQ)).
      assert (HQ_op : IsOpenParent Q) by (apply (CSim_OpenParent 0 g Q HQ)).
      split; [apply (proj1 (stepH_MonoH 0) g Hg) | split; [apply IsOpenParent_snoc_child; [exact HQ_op | apply IsOpenParent_2] |]].
      intros B_ext HB m' s_tape R_raw Hstrip Hvalid.
      assert (HB_sym : Forall (IsHydraSym allow5) B_ext) by (apply Bal_HydraSym; exact HB).
      destruct (OneRoundStep_copy_parent Q HQ_op B_ext m' s_tape R_raw HB_sym Hstrip Hvalid)
        as [t1 [s_next [R_raw1 [Ht1 [Hstrip1 [Hvalid1 Hreach1]]]]]].
      destruct (CSim0_rep_app g Q (S m') HQ B_ext HB (S m') s_next R_raw1 Hstrip1 Hvalid1)
        as [t2 [R_raw2 [Ht2 [Hvalid2 Hreach2]]]].
      exists (t1 + t2), R_raw2.
      split; [eapply Nat.le_trans; [exact Ht2 | lia]
             | split; [exact Hvalid2 | eapply reaches_trans; eassumption]].
    - (* k = S (S k'): stepH (S k') *)
      split; [apply (stepH_MonoH (S k')) | split; [apply IsOpenParent_2 |]].
      intros F P HP.
      assert (HF : MonoH (S k') F) by (apply (CSim_MonoH (S k') F P HP)).
      assert (HP_op : IsOpenParent P) by (apply (CSim_OpenParent (S k') F P HP)).
      split; [apply (proj1 (stepH_MonoH (S k')) F HF) | split; [apply IsOpenParent_snoc_child; [exact HP_op | apply IsOpenParent_2] |]].
      intros g Q HQ.
      assert (Hg : MonoH k' g) by (apply (CSim_MonoH k' g Q HQ)).
      assert (HQ_op : IsOpenParent Q) by (apply (CSim_OpenParent k' g Q HQ)).
      change (stepH (S k') F g) with (eval_succ k' (fun m => iter_poly F (S m) g)).
      apply (CSim_eval_succ k' (fun m => iter_poly F (S m) g)
               (Q ++ (P ++ [2] ++ [3]) ++ [3])
               (fun m => Q ++ rep_app (S m) (P ++ [3]))).
      + apply IsOpenParent_snoc_child; [exact HQ_op | apply IsOpenParent_snoc_child; [exact HP_op | apply IsOpenParent_2]].
      + intro m. apply CSim_rep_app; assumption.
      + intros m1 m2 Hm.
        apply (iter_poly_LeH (S k') (S m1) (S m2) F F ltac:(lia) ltac:(lia) HF HF (LeH_refl (S k') F HF)
                 g g Hg Hg (LeH_refl k' g Hg)).
      + intros pre_outer m' s_tape R_raw Hpre Hstrip Hvalid.
        assert (HpreQ : Forall (IsHydraSym allow5) (pre_outer ++ Q))
          by (apply Forall_app_iff; [exact Hpre | apply IsOpenParent_HydraSym; exact HQ_op]).
        assert (Hstrip' : strip3_rev (rev s_tape) =
                          strip3_rev (rev ((pre_outer ++ Q) ++ (P ++ [2] ++ [3])))).
        { rewrite Hstrip.
          replace (pre_outer ++ Q ++ (P ++ [2] ++ [3]) ++ [3])
            with (((pre_outer ++ Q) ++ (P ++ [2] ++ [3])) ++ [3])
            by (rewrite <- !app_assoc; reflexivity).
          apply strip3_rev_3. }
        destruct (OneRoundStep_copy_parent P HP_op (pre_outer ++ Q) m' s_tape R_raw HpreQ Hstrip' Hvalid)
          as [t1 [s_next [R_raw1 [Ht1 [Hstrip1 [Hvalid1 Hreach1]]]]]].
        exists t1, s_next, R_raw1.
        split; [exact Ht1 | split; [| split; [exact Hvalid1 | exact Hreach1]]].
        rewrite Hstrip1, <- !app_assoc; reflexivity.
  Qed.

  Fixpoint chainP_str (d : nat) : list nat :=
    match d with
    | 0 => [2]
    | S d' => [2] ++ chainP_str d' ++ [3]
    end.

  Lemma chainP_str_eq : forall d,
    chainP_str d = rep (S d) 2 [] ++ rep d 3 [].
  Proof.
    induction d as [| d' IH]; simpl.
    - reflexivity.
    - rewrite IH, <- !app_assoc; simpl.
      f_equal; f_equal. rewrite rep_app_snoc; reflexivity.
  Qed.

  Lemma CSim_chainH : forall d k,
    CSim k (chainH d k) (chainP_str d).
  Proof.
    induction d as [| d' IH]; intro k.
    - apply CSim_baseP.
    - exact (proj2 (proj2 (IH (S k))) (baseP k) [2] (CSim_baseP k)).
  Qed.

  Lemma CSim_bracketH : forall k,
    allow5 = true -> CSim k (bracketH k) [5].
  Proof.
    intros k Ha. unfold bracketH.
    apply (CSim_eval_succ k (fun m => chainH (m - 1) k) [5] (fun m => chainP_str (m - 1))).
    - apply IsOpenParent_5; exact Ha.
    - intro m. apply CSim_chainH.
    - intros m1 m2 Hm. apply chainH_LeH_mono; lia.
    - intros pre_outer m' s_tape R_raw Hpre Hstrip Hvalid.
      rewrite rev_app_distr in Hstrip; simpl in Hstrip.
      destruct (strip3_rev_decompose s_tape 5 pre_outer Hstrip) as [k3 Es].
      subst s_tape.
      assert (Hpre_true : Forall (IsHydraSym true) pre_outer) by (rewrite <- Ha; exact Hpre).
      assert (Hvalid_true : ValidHydraTape true symB_delim R_raw (pre_outer ++ [5] ++ rep k3 3 []))
        by (rewrite <- Ha; exact Hvalid).
      destruct (round_expand_bracket m' R_raw pre_outer k3 Ha Hpre_true Hvalid_true)
        as [t [Ht Hreach]].
      replace (S m' - 1) with m' by lia.
      exists t, (pre_outer ++ rep (S m') 2 []), (pre_outer ++ rep (S m') 2 []).
      split; [exact Ht | split; [| split; [| exact Hreach]]].
      + rewrite chainP_str_eq.
        replace (pre_outer ++ rep (S m') 2 [] ++ rep m' 3 [])
          with ((pre_outer ++ rep (S m') 2 []) ++ rep m' 3 [])
          by (rewrite <- app_assoc; reflexivity).
        symmetry; apply strip3_rev_rep3.
      + assert (Hall : Forall (IsHydraSym allow5) (pre_outer ++ rep (S m') 2 [])).
        { apply Forall_app_iff; [exact Hpre |].
          apply Forall_rep; [left; left; reflexivity | constructor]. }
        destruct pre_outer as [| p0 pre_tl].
        * simpl in Hall. inversion Hall; subst. apply ValidHydraTape_clean; [left; reflexivity | assumption].
        * destruct R_raw as [| r0 r_tl]; simpl in Hvalid; [contradiction |].
          destruct Hvalid as [-> [Hp0 _]].
          simpl in Hall. inversion Hall; subst. apply ValidHydraTape_clean; assumption.
  Qed.

  Fixpoint chainB_str (d : nat) : list nat :=
    match d with
    | 0 => [5]
    | S d' => [5] ++ chainB_str d' ++ [3]
    end.

  Lemma chainB_str_eq : forall d,
    chainB_str d = rep (S d) 5 [] ++ rep d 3 [].
  Proof.
    induction d as [| d' IH]; simpl.
    - reflexivity.
    - rewrite IH, <- !app_assoc; simpl.
      f_equal; f_equal. rewrite rep_app_snoc; reflexivity.
  Qed.

  Lemma CSim_chainB_H : forall d k,
    allow5 = true -> CSim k (chainB_H d k) (chainB_str d).
  Proof.
    induction d as [| d' IH]; intros k Ha.
    - apply CSim_bracketH; exact Ha.
    - exact (proj2 (proj2 (IH (S k) Ha)) (bracketH k) [5] (CSim_bracketH k Ha)).
  Qed.

  Theorem Hydra_chainP_halts : forall m d,
    1 <= m ->
    exists t,
      HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep (S d) 2 [])) t /\
      chainH d 0 m < t.
  Proof.
    intros [| m'] d Hm; [lia |].
    destruct (CSim_chainH d 0) as [Hmono [_ Htap]].
    assert (Hstrip : strip3_rev (rev (rep (S d) 2 [])) = strip3_rev (rev ([] ++ chainP_str d))).
    { simpl. rewrite chainP_str_eq, strip3_rev_rep3; reflexivity. }
    assert (Hvalid : ValidHydraTape allow5 symB_delim (rep (S d) 2 []) (rep (S d) 2 [])).
    { simpl. apply ValidHydraTape_clean; [left; reflexivity |].
      apply Forall_rep; [left; left; reflexivity | constructor]. }
    destruct (Htap [] bal_nil m' (rep (S d) 2 []) (rep (S d) 2 []) Hstrip Hvalid)
      as [t1 [R_raw' [Ht1 [Hvalid' Hreach1]]]].
    destruct R_raw' as [| r0 r_tl]; [| simpl in Hvalid'; contradiction].
    assert (Hhalt : Reaches tm (mkCfgR (Some 1) (rep (chainH d 0 (S m')) 1 []) [])
                               (mkCfgR None (1 :: rep (chainH d 0 (S m')) 1 []) []) 1).
    { apply reaches_one, step_mkCfgR_R_nil, (hc_B0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
    exists (t1 + 1). split.
    - unfold HaltsIn. exists (mkCfgR None (1 :: rep (chainH d 0 (S m')) 1 []) []).
      split; [eapply reaches_trans; [exact Hreach1 | exact Hhalt] | reflexivity].
    - lia.
  Qed.

  Theorem Hydra_chainB_halts : forall m d,
    allow5 = true ->
    1 <= m ->
    exists t,
      HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep (S d) 5 [])) t /\
      chainB_H d 0 m < t.
  Proof.
    intros [| m'] d Ha Hm; [lia |].
    destruct (CSim_chainB_H d 0 Ha) as [Hmono [_ Htap]].
    assert (Hstrip : strip3_rev (rev (rep (S d) 5 [])) = strip3_rev (rev ([] ++ chainB_str d))).
    { simpl. rewrite chainB_str_eq, strip3_rev_rep3; reflexivity. }
    assert (Hvalid : ValidHydraTape allow5 symB_delim (rep (S d) 5 []) (rep (S d) 5 [])).
    { simpl. apply ValidHydraTape_clean; [right; split; [exact Ha | reflexivity] |].
      apply Forall_rep; [left; right; split; [exact Ha | reflexivity] | constructor]. }
    destruct (Htap [] bal_nil m' (rep (S d) 5 []) (rep (S d) 5 []) Hstrip Hvalid)
      as [t1 [R_raw' [Ht1 [Hvalid' Hreach1]]]].
    destruct R_raw' as [| r0 r_tl]; [| simpl in Hvalid'; contradiction].
    assert (Hhalt : Reaches tm (mkCfgR (Some 1) (rep (chainB_H d 0 (S m')) 1 []) [])
                               (mkCfgR None (1 :: rep (chainB_H d 0 (S m')) 1 []) []) 1).
    { apply reaches_one, step_mkCfgR_R_nil, (hc_B0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC). }
    exists (t1 + 1). split.
    - unfold HaltsIn. exists (mkCfgR None (1 :: rep (chainB_H d 0 (S m')) 1 []) []).
      split; [eapply reaches_trans; [exact Hreach1 | exact Hhalt] | reflexivity].
    - lia.
  Qed.
End HydraRound.

(* ========================================================================= *)
(* Part 5: Master Core Halting Theorems for fe0_5_16, fe1_6, fe1_7, fe1_8    *)
(* ========================================================================= *)

Theorem Fe0_5_16_halts : forall tm m n,
  Fe0_5_16Core tm ->
  1 <= m -> 3 <= n ->
  exists t,
    HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep n 2 [])) t /\
    f_epsilon0 (n - 3) < t.
Proof.
  intros tm m n HC Hm Hn.
  replace (rep n 2 []) with (rep (S ((n - 3) + 2)) 2 []) by (f_equal; lia).
  destruct (Hydra_chainP_halts tm false 0 2 14 11 13 15 11 9 4 4 0 1 0 HC m ((n - 3) + 2) Hm)
    as [t [Hhalt Ht]].
  exists t; split; [exact Hhalt |].
  unfold f_epsilon0.
  eapply Nat.le_lt_trans; [exact (proj2 (chainH_MonoH ((n - 3) + 2) 0) 1 m Hm) | exact Ht].
Qed.

Theorem Fe1_6_halts : forall tm m n,
  Fe1_6Core tm ->
  1 <= m -> 3 <= n ->
  exists t,
    HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep n 5 [])) t /\
    f_epsilon1 (n - 3) < t.
Proof.
  intros tm m n HC Hm Hn.
  replace (rep n 5 []) with (rep (S ((n - 3) + 2)) 5 []) by (f_equal; lia).
  destruct (Hydra_chainB_halts tm true 14 8 0 17 18 19 20 17 4 1 0 0 0 HC m ((n - 3) + 2) eq_refl Hm)
    as [t [Hhalt Ht]].
  exists t; split; [exact Hhalt |].
  unfold f_epsilon1.
  eapply Nat.le_lt_trans; [exact (proj2 (chainB_H_MonoH ((n - 3) + 2) 0) 1 m Hm) | exact Ht].
Qed.

Theorem Fe1_7_halts : forall tm m n,
  Fe1_7Core tm ->
  1 <= m -> 3 <= n ->
  exists t,
    HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep n 5 [])) t /\
    f_epsilon1 (n - 3) < t.
Proof.
  intros tm m n HC Hm Hn.
  replace (rep n 5 []) with (rep (S ((n - 3) + 2)) 5 []) by (f_equal; lia).
  destruct (Hydra_chainB_halts tm true 0 2 14 17 18 19 11 9 6 6 1 1 0 HC m ((n - 3) + 2) eq_refl Hm)
    as [t [Hhalt Ht]].
  exists t; split; [exact Hhalt |].
  unfold f_epsilon1.
  eapply Nat.le_lt_trans; [exact (proj2 (chainB_H_MonoH ((n - 3) + 2) 0) 1 m Hm) | exact Ht].
Qed.

Theorem Fe1_8_halts : forall tm m n,
  Fe1_8Core tm ->
  1 <= m -> 3 <= n ->
  exists t,
    HaltsIn tm (mkCfgR (Some 1) (rep m 1 []) (rep n 5 [])) t /\
    f_epsilon1 (n - 3) < t.
Proof.
  intros tm m n HC Hm Hn.
  replace (rep n 5 []) with (rep (S ((n - 3) + 2)) 5 []) by (f_equal; lia).
  destruct (Hydra_chainB_halts tm true 0 2 14 11 17 18 11 9 6 6 1 1 7 HC m ((n - 3) + 2) eq_refl Hm)
    as [t [Hhalt Ht]].
  exists t; split; [exact Hhalt |].
  unfold f_epsilon1.
  eapply Nat.le_lt_trans; [exact (proj2 (chainB_H_MonoH ((n - 3) + 2) 0) 1 m Hm) | exact Ht].
Qed.

Print Assumptions Fe0_5_16_halts.
Print Assumptions Fe1_6_halts.
Print Assumptions Fe1_7_halts.
Print Assumptions Fe1_8_halts.










