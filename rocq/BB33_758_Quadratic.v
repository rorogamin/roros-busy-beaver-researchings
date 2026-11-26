From Stdlib Require Import Arith Lia ZArith.

(** Holdout #758: conditional quadratic chain-length bound.

    Assume the 3-adic renormalization defect is at most [C*(t+1)] at
    ternary depth [t]:
      [L (3*m+r) <= L m + C*(t+1)] whenever [m < 3^t] and [r < 3].
    Then for every [c < 3^t],
      [2*L c <= 2*L 1 + C*t*(t+1)].

    This file proves only the arithmetic consequence, not the defect
    bound. *)

Fixpoint pow3 (t : nat) : nat :=
  match t with
  | 0 => 1
  | S k => 3 * pow3 k
  end.

Theorem quadratic_chain_bound (L : nat -> nat) (hL0 : L 0 = 0) (C : nat)
    (hscale : forall t m r, m < pow3 t -> r < 3 ->
      L (3 * m + r) <= L m + C * (t + 1)) :
    forall t c, 1 <= c -> c < pow3 t ->
      2 * L c <= 2 * L 1 + C * t * (t + 1).
Proof.
  induction t as [| t ih]; intros c hc1 hc.
  - simpl in hc. lia.
  - simpl in hc.
    assert (hm : c / 3 < pow3 t).
    { apply Nat.Div0.div_lt_upper_bound. lia. }
    assert (hcdecomp : c = 3 * (c / 3) + c mod 3).
    { apply Nat.div_mod_eq. }
    rewrite hcdecomp.
    specialize (hscale t (c / 3) (c mod 3) hm (Nat.mod_upper_bound c 3 (ltac:(lia)))).
    destruct (Nat.eq_dec (c / 3) 0) as [h0 | h0].
    + rewrite h0 in hscale.
      rewrite hL0 in hscale.
      change (L (c mod 3) <= C * (t + 1)) in hscale.
      rewrite h0.
      change (2 * L (c mod 3) <=
              L 1 + (L 1 + 0) + C * S t * S (t + 1)).
      assert (HL : 2 * L (c mod 3) <= C * (t + 1) * 2) by lia.
      assert (H2 : C * (t + 1) * 2 <= C * (t + 1) * (t + 1 + 1)).
      { apply Nat.mul_le_mono_l. lia. }
      lia.
    + assert (h1m : 1 <= c / 3) by lia.
      specialize (ih (c / 3) h1m hm).
      assert (H2 : C * t * (t + 1) + 2 * (C * (t + 1)) =
                  C * (t + 1) * (t + 1 + 1)) by ring.
      lia.
Qed.

Theorem at_292 (L : nat -> nat) (hL0 : L 0 = 0)
    (hscale : forall t m r, m < pow3 t -> r < 3 ->
      L (3 * m + r) <= L m + 100 * (t + 1))
    (c : nat) (hc1 : 1 <= c) (hc : c < pow3 292) :
    2 * L c <= 2 * L 1 + 100 * 292 * 293.
Proof.
  apply quadratic_chain_bound with (C := 100); auto.
Qed.

Theorem delta_window_z (Lc L1 : Z)
    (h : (2 * Lc <= 2 * L1 + 8555600)%Z) :
    (9 * Lc < 38600000 + 9 * L1)%Z.
Proof.
  lia.
Qed.

Print Assumptions quadratic_chain_bound.
Print Assumptions at_292.
Print Assumptions delta_window_z.
