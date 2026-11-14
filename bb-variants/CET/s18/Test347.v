From Stdlib Require Import ZArith NArith Bool.
Require Import CET3_Cert CET3_SepCert.
Open Scope Z_scope.

Definition ag1_347 (s : State) (b : bool) : option Transition :=
  match s, b with
  | StA, false => Some {| write_sym := false; move_dir := MoveL; next_state := StB |}
  | StA, true  => Some {| write_sym := false; move_dir := MoveL; next_state := StA |}
  | StB, false => Some {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StB, true  => Some {| write_sym := true;  move_dir := MoveL; next_state := StB |}
  | StC, false => Some {| write_sym := false; move_dir := MoveR; next_state := StC |}
  | StC, true  => Some {| write_sym := true;  move_dir := MoveR; next_state := StA |}
  end.

Definition ag2_347 (s : State) (b : bool) : option Transition :=
  match s, b with
  | StA, false => Some {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StA, true  => Some {| write_sym := true;  move_dir := MoveR; next_state := StB |}
  | StB, false => Some {| write_sym := false; move_dir := MoveL; next_state := StC |}
  | StB, true  => Some {| write_sym := false; move_dir := MoveR; next_state := StA |}
  | StC, false => Some {| write_sym := true;  move_dir := MoveL; next_state := StC |}
  | StC, true  => Some {| write_sym := false; move_dir := MoveR; next_state := StB |}
  end.

Lemma cert_347_ok :
  check_separated_cert ag1_347 ag2_347 10011%N 11%N (-3) (-2733) (-2728) 6144%N 0 (-18) 5 = true.
Proof. vm_compute. reflexivity. Qed.
