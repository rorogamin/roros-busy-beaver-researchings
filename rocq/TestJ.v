From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Definition P (n:nat) : Z := Z.of_nat (3^n).
Lemma P0 : P 0 = 1.
Proof. unfold P. reflexivity. Qed.
Lemma P_succ (n:nat) : P (S n) = 3 * P n.
Proof. unfold P. rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul. ring. Qed.
Definition jI (p:Z*Z) : Z*Z := (3*fst p+2, snd p-fst p+1).
Fixpoint jIterI (n:nat) (p:Z*Z) : Z*Z :=
 match n with 0%nat => p | S n' => jI (jIterI n' p) end.
Lemma j_formula (n:nat) (c:Z) :
 jIterI n (1,c) = (2*P n-1, c-P n+1+2*Z.of_nat n).
Proof.
 induction n as [|n ih].
 - unfold jIterI. unfold P. simpl. assert (h : c - 1 + 1 + 0 = c) by ring. rewrite h. reflexivity.
 - cbn [jIterI]. rewrite ih. unfold jI. cbn [fst snd]. rewrite P_succ. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by (rewrite Nat2Z.inj_succ; reflexivity). apply pair_equal_spec; split; ring.
Qed.
