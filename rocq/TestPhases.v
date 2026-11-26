From Stdlib Require Import Arith Lia PeanoNat.
Import Nat.

Definition Lstep (d:nat) : nat := (9*d+20)/4.
Lemma Lstep_ge_two (d:nat) : 2*d <= Lstep d.
Proof. unfold Lstep. apply Nat.div_le_lower_bound; [discriminate|lia]. Qed.

Fixpoint LIter (n:nat) (d:nat) : nat :=
 match n with 0%nat => d | S n' => Lstep (LIter n' d) end.

Lemma LIter_ge (n d:nat) : 2^n * d <= LIter n d.
Proof.
 induction n as [|n ih]; cbn [LIter].
 - rewrite Nat.pow_0_r; lia.
 - rewrite Nat.pow_succ_r'. pose proof (Lstep_ge_two (LIter n d)) as hL. nia.
Qed.

Definition Jstep (e:nat) : nat := 3*e.
Fixpoint JIter (n:nat) (e:nat) : nat :=
 match n with 0%nat => e | S n' => Jstep (JIter n' e) end.
Lemma JIter_ge (n e:nat) : 3^n * e <= JIter n e.
Proof.
 induction n as [|n ih]; cbn [JIter].
 - rewrite Nat.pow_0_r; lia.
 - rewrite Nat.pow_succ_r'. unfold Jstep. nia.
Qed.

Lemma pow2_gt : 2^465 < 2^466. Proof. vm_compute; reflexivity. Qed.
Lemma pow3_gt : 2^465 < 3^294. Proof. vm_compute; reflexivity. Qed.

Lemma L_phase_length_le_465 (n d:nat) (hd:1<=d)
  (hU: LIter n d <= 2^465) : n <= 465.
Proof.
 assert (H: ~ 465 < n).
 { intro hlt. have hn:466<=n by lia.
   have hp:2^466 <= 2^n := Nat.pow_le_mono_r 2 (by discriminate) hn.
   have h1:2^n <= 2^n*d by nia.
   have h2:2^n <= LIter n d := le_trans h1 (LIter_ge n d).
   lia. }
 lia.
Qed.

Lemma J_phase_length_le_293 (n e:nat) (he:1<=e)
  (hU: JIter n e <= 2^465) : n <= 293.
Proof.
 assert (H: ~ 293 < n).
 { intro hlt. have hn:294<=n by lia.
   have hp:3^294 <= 3^n := Nat.pow_le_mono_r 3 (by discriminate) hn.
   have h1:3^n <= 3^n*e by nia.
   have h2:3^n <= JIter n e := le_trans h1 (JIter_ge n e).
   lia. }
 lia.
Qed.

Print Assumptions L_phase_length_le_465.
Print Assumptions J_phase_length_le_293.
