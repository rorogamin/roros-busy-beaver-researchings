From Stdlib Require Import Arith Lia PeanoNat.
Lemma t (d:nat) : 2*d <= (9*d+20)/4.
Proof.
  apply Nat.div_le_lower_bound; [discriminate|].
  lia.
Qed.
