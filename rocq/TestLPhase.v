From Stdlib Require Import Arith Lia.
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
Lemma pow2_gt : 2^465 < 2^466.
Proof. apply Nat.pow_lt_mono_r; lia. Qed.
Lemma L_phase_length_le_465 (n d:nat) (hd:1<=d)
  (hU: LIter n d <= 2^465) : n <= 465.
Proof.
 assert (H: ~ 465 < n).
 { intro hlt. assert (hn:466<=n) by lia.
   assert (h2nz:2<>0) by discriminate.
   pose proof (@Nat.pow_le_mono_r 2 466 n h2nz hn) as hp.
   assert (h1:2^n <= 2^n*d) by nia.
   assert (h2:2^n <= LIter n d). { apply Nat.le_trans with (2^n*d); [exact h1|apply LIter_ge]. }
   pose proof pow2_gt as hgt. lia. }
 lia.
Qed.
Print Assumptions L_phase_length_le_465.
