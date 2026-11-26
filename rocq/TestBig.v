From Stdlib Require Import Arith Lia.
Lemma a : 2^465 < 2^466.
Proof.
  rewrite Nat.pow_succ_r'.
  assert (h : 0 < 2^465). { apply Nat.lt_0_neq. apply Nat.pow_nonzero. lia. }
  nia.
Qed.
