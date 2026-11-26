From Stdlib Require Import Arith Lia.
Lemma pow2_pos n : 0 < 2^n.
Proof. induction n; simpl; [lia|nia]. Qed.
