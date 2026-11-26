From Stdlib Require Import Arith Lia.
From Top Require Import BB33_758_LPhase.

(** Holdout #758: cumulative L-step budget, stated for the actual
    iteration [LIter] of the L-step map. *)

Lemma total_L_budget_iter (n d:nat) (hd:1<=d)
  (hU: LIter n d <= 2^465) : n<=465.
Proof.
  exact (L_phase_length_le_465 n d hd hU).
Qed.

Print Assumptions total_L_budget_iter.
