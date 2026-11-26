From Stdlib Require Import Arith Lia ZArith.

(** Holdout #758: constant increment defect implies the wall.

    [D c] is the endpoint increment [F c - c] of the chain from [A(1,c)].
    If [|D (2*c+r) - D c| <= K] for [r=0,1], then [D c <= D 1 + K*t]
    for every [c < 2^t].  At [t=463] and [K=80000], this is
    [D c <= D 1 + 37040000], inside the 38.6M wall window.

    This file proves only the arithmetic reduction, not the defect bound. *)

Theorem increment_bound (D : nat -> nat) (K : nat)
    (hstep : forall c, 1 <= c ->
      D (2 * c) <= D c + K /\ D (2 * c + 1) <= D c + K) :
    forall t c, 1 <= c -> c < 2 ^ t -> D c <= D 1 + K * t.
Proof.
  induction t as [| t ih]; intros c h1 hc.
  - simpl in hc. lia.
  - simpl in hc.
    destruct (Nat.eq_dec c 1) as [hc1 | hc1].
    + subst c. simpl. lia.
    + assert (hc2 : 2 <= c) by lia.
      assert (hm : c / 2 < 2 ^ t).
      { apply Nat.Div0.div_lt_upper_bound. lia. }
      assert (h1m : 1 <= c / 2).
      { destruct (Nat.eq_dec (c / 2) 0) as [h0 | h0]; [| lia].
        exfalso.
        pose proof (Nat.div_mod_eq c 2) as Hdec.
        assert (h2 : 2 <> 0) by lia.
        pose proof (Nat.mod_upper_bound c 2 h2) as Hmod.
        rewrite h0 in Hdec. lia. }
      assert (hdecomp : c = 2 * (c / 2) + c mod 2).
      { apply Nat.div_mod_eq. }
      assert (hmod : c mod 2 = 0 \/ c mod 2 = 1).
      { assert (h2 : 2 <> 0) by lia.
        pose proof (Nat.mod_upper_bound c 2 h2). lia. }
      destruct hmod as [h0 | h1'].
      * assert (hc_eq : c = 2 * (c / 2)) by lia.
        rewrite hc_eq.
        specialize (hstep (c / 2) h1m). destruct hstep as [hs _].
        specialize (ih (c / 2) h1m hm).
        lia.
      * assert (hc_eq : c = 2 * (c / 2) + 1) by lia.
        rewrite hc_eq.
        specialize (hstep (c / 2) h1m). destruct hstep as [_ hs].
        specialize (ih (c / 2) h1m hm).
        lia.
Qed.

Theorem at_463 (D : nat -> nat)
    (hstep : forall c, 1 <= c ->
      D (2 * c) <= D c + 80000 /\ D (2 * c + 1) <= D c + 80000)
    (c : nat) (h1 : 1 <= c) (hc : c < 2 ^ 463) :
    D c <= D 1 + 80000 * 463.
Proof.
  exact (increment_bound D 80000 hstep 463 c h1 hc).
Qed.

(** Numeric wall check at the integer level, avoiding large unary nat
    literals.  [7 + 800*463 = 370407 < 38600000]. *)
Theorem delta_wall_z (Dc : Z) (h : (Dc <= 7 + 80000 * 463)%Z) :
    (Dc < 38600000)%Z.
Proof.
  lia.
Qed.

Print Assumptions increment_bound.
Print Assumptions at_463.
Print Assumptions delta_wall_z.
