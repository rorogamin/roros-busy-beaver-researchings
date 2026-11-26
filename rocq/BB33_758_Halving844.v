From Stdlib Require Import NArith Lia.

Open Scope N_scope.

(** Holdout #758: the exact 844-step extremal halving trace.

    The state [(2*3^289 - 1, 2047)] has halving time exactly 844, ending in
    rule [h] (a return to [A(1,·)]).  Binary [N] arithmetic is used so that
    [vm_compute] can evaluate the 139-digit state.

    This is a machine-checked lower-bound certificate for the reachable
    maximum.  It does not by itself prove that no other reachable state has a
    larger halving time. *)

Inductive Out :=
  | halt
  | next (a c : N).

Definition step (a c : N) : Out :=
  if N.leb a c then
    if N.eqb (N.modulo a 2) 0 then
      if N.eqb (N.modulo c 2) 0 then halt
      else next 1 (N.div a 2 + c + 2)
    else if N.eqb (N.modulo c 2) 0 then
      next (3 * a) (c - a + 4)
    else
      next (3 * a + 2) (c - a + 1)
  else if orb (N.eqb (N.modulo c 4) 0) (N.eqb (N.modulo c 4) 2) then
    next (a - c - 1) (3 * (N.div c 2) + 2)
  else if N.eqb (N.modulo c 4) 1 then
    if N.eqb a (c + 1) then halt
    else next (a - c - 2) (3 * (N.div (c - 1) 2) + 5)
  else
    if N.eqb a (c + 1) then halt
    else if N.eqb a (c + 2) then next (3 * c + 8) 1
    else if N.eqb a (c + 3) then halt
    else next (a - c - 4) (3 * (N.div (c - 1) 2) + 8).

Fixpoint run (n : nat) (p : N * N) : option (N * N) :=
  match n with
  | 0%nat => Some p
  | S n' =>
      match step (fst p) (snd p) with
      | halt => None
      | next a' c' => run n' (a', c')
      end
  end.

Fixpoint ht (c0 : N) (n : nat) (a c : N) : N :=
  match n with
  | 0%nat => 0
  | S n' =>
      match step a c with
      | halt => 1
      | next a' c' =>
          if orb (N.eqb a' 1) (N.leb (2 * c') c0) then 1
          else 1 + ht c0 n' a' c'
      end
  end.

Definition aStar : N :=
  1545512812055393272156186978973263063630360047026903492257618701737754488390986882010987554468198065880319558791263685445573594052009864965.

Lemma prefix_reaches :
  run 289 (1, 3 ^ 289 + 1468) = Some (aStar, 2047).
Proof. vm_compute. reflexivity. Qed.

Lemma halving_time_844 :
  ht 2047 2000 aStar 2047 = 844%N.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions prefix_reaches.
Print Assumptions halving_time_844.
