From Stdlib Require Import Arith Lia.
Lemma pow2_gt : 2^465 < 2^466.
Proof. apply Nat.pow_lt_mono_r; lia. Qed.
