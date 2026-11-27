(** * Holdout #758: Kernel-checked halting certificate for [A(1, H)] and [A(1, H - 2)]

    Uses binary [N] arithmetic so that the full 307-rule accelerated evaluation
    from the 463-bit halting value [H = (3^307 - 8282708212) / 13959275] (and its
    twin [H - 2]) is verified directly by [vm_compute] with zero axioms. *)

From Stdlib Require Import BinNat.
Open Scope N_scope.

Inductive OutN : Type :=
| HaltN
| NextN (a c : N).

(** Exact 10-rule accelerated step over binary [N]. *)
Definition stepN (a c : N) : OutN :=
  if N.leb a c then
    if N.eqb (a mod 2) 0 then
      if N.eqb (c mod 2) 0 then HaltN else NextN 1 (a / 2 + c + 2)
    else if N.eqb (c mod 2) 0 then
      NextN (3 * a) (c - a + 4)
    else
      NextN (3 * a + 2) (c - a + 1)
  else if orb (N.eqb (c mod 4) 0) (N.eqb (c mod 4) 2) then
    NextN (a - c - 1) (3 * (c / 2) + 2)
  else if N.eqb (c mod 4) 1 then
    if N.eqb a (c + 1) then HaltN
    else NextN (a - c - 2) (3 * ((c - 1) / 2) + 5)
  else
    if N.eqb a (c + 1) then HaltN
    else if N.eqb a (c + 2) then NextN (3 * c + 8) 1
    else if N.eqb a (c + 3) then HaltN
    else NextN (a - c - 4) (3 * ((c - 1) / 2) + 8).

Fixpoint runN (n : nat) (a c : N) : option (N * N) :=
  match n with
  | O => Some (a, c)
  | S k =>
      match stepN a c with
      | HaltN => None
      | NextN a' c' => runN k a' c'
      end
  end.

Definition isSomeN {A : Type} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

(** The 463-bit halting value [H = (3^307 - 8282708212) / 13959275]. *)
Definition H_val : N := (3 ^ 307 - 8282708212) / 13959275.

Lemma H_exact_div : (3 ^ 307 - 8282708212) mod 13959275 = 0.
Proof. vm_compute. reflexivity. Qed.

(** [A(1, H)] halts in exactly 307 accelerated rules ([j^292 bcbbccbbjbcbbcd]). *)
Lemma H_halts_307 : runN 307 1 H_val = None.
Proof. vm_compute. reflexivity. Qed.

(** [A(1, H)] is still alive after 306 accelerated rules (sharpness). *)
Lemma H_alive_306 : isSomeN (runN 306 1 H_val) = true.
Proof. vm_compute. reflexivity. Qed.

(** Twin halting value [A(1, H - 2)] also halts in exactly 307 rules ([j^292 ccbbccbbjbcbbcd]). *)
Lemma H_minus_2_halts_307 : runN 307 1 (H_val - 2) = None.
Proof. vm_compute. reflexivity. Qed.

(** [A(1, H - 2)] is still alive after 306 rules (sharpness). *)
Lemma H_minus_2_alive_306 : isSomeN (runN 306 1 (H_val - 2)) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions H_exact_div.
Print Assumptions H_halts_307.
Print Assumptions H_alive_306.
Print Assumptions H_minus_2_halts_307.
Print Assumptions H_minus_2_alive_306.
