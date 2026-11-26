From Stdlib Require Import Arith Lia.
Lemma t (a b:nat) (h:a<=b) : 2*a<=2*b.
Proof. nlinarith. Qed.
