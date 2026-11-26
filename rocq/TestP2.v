From Stdlib Require Import Arith Lia.
Lemma pow2_pos n : 0 < 2^n.
Proof. induction n; simpl; [lia|nia]. Qed.
Lemma doubleL n : 2*n = n+n. Proof. nia. Qed.
Lemma pow2_gt : 2^465 < 2^466.
Proof.
 rewrite Nat.pow_succ_r'.
 rewrite doubleL.
 apply Nat.lt_add_pos_r.
 apply pow2_pos.
Qed.
