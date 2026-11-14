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


Eval vm_compute in match run_N_fast ag1_347 ag2_347 10011%N fc0 with None => (0,0,0,0) | Some fc => (fp1 fc, fp2 fc, fmin_w fc, fmax_w fc) end.
