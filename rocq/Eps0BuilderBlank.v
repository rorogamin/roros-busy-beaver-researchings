(** * Eps0BuilderBlank.v -- a blank-tape run through the stage builder

    This is the concrete end-to-end composition of the 10-state builder with
    the 33-state drive.  A 22-state prologue writes the builder's source
    frame on an all-blank tape:

        1^2(source) 0 0 1(seed) 0 1(wall) 0 1^2(value) 0 1(seed)

    It leaves the head on the blank immediately right of the source, so the
    builder starts in [A].  The builder consumes the two source marks, writes
    the two-mark stage block, and hands over to [F0].  The drive then runs its
    two stages and halts.

    The prologue is deliberately fixed at source length two: this theorem is
    a concrete integration test for the parametric builder, not a symbolic
    proof of every blank-tape stage count.  The exact halt is a 68,311-step
    run (68,312 configurations including the start), with the wall, 255 value
    marks and the trailing seed:

        [0^6] 1(wall) 0^268 1^255 0 1(seed)

    The left context has six blanks because the builder leaves four trailing
    blanks and the prologue supplies two head cells. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM Eps0Drive Eps0Builder.

Open Scope nat_scope.

(** ** The shifted builder/drive table *)

Definition SHIFT2 : nat := 22.

(** States 0..11 write the source frame left-to-right.  States 12..20 return
    left over it without changing it; state 21 steps left into the builder's
    starting blank.  From state 22 on, this is [etbl] with every state shifted
    by [SHIFT2]. *)

Definition ibtbl : table := fun s b =>
  if s <? SHIFT2 then
    match s with
    | 0  => Some (on, true, 1)
    | 1  => Some (on, true, 2)
    | 2  => Some (bl, true, 3)
    | 3  => Some (bl, true, 4)
    | 4  => Some (on, true, 5)
    | 5  => Some (bl, true, 6)
    | 6  => Some (on, true, 7)
    | 7  => Some (bl, true, 8)
    | 8  => Some (on, true, 9)
    | 9  => Some (on, true, 10)
    | 10 => Some (bl, true, 11)
    | 11 => Some (on, true, 12)
    | 12 => Some (b, false, 13)
    | 13 => Some (b, false, 14)
    | 14 => Some (b, false, 15)
    | 15 => Some (b, false, 16)
    | 16 => Some (b, false, 17)
    | 17 => Some (b, false, 18)
    | 18 => Some (b, false, 19)
    | 19 => Some (b, false, 20)
    | 20 => Some (b, false, 21)
    | 21 => Some (b, false, 22)
    | _  => None
    end
  else
    match etbl (s - SHIFT2) b with
    | None => None
    | Some (w, d, t) => Some (w, d, t + SHIFT2)
    end.

Definition c0 : conf := mkConf 0 [] bl [].

Definition cf : conf :=
  mkConf 55 [bl; bl; bl; bl; bl; bl] bl
    (on :: zeros 268 ++ ones 255 ++ bl :: on :: []).

(** ** The exact builder handoff and drive suffix *)

(** The state after 47 steps: the prologue's 22-cell write/return followed by
    the builder's 25-step [builder_run] segment.  The state is [SHIFT2 + 22],
    the shifted [F0], and the stage block is exactly [1^2]. *)

Definition stage_up : conf :=
  mkConf 44 (on :: bl :: ones 2 ++ zeros 4) bl
    (ones 2 ++ bl :: on :: bl :: []).

Lemma prologue_builder_run :
  run ibtbl 47 c0 = Some stage_up.
Proof. vm_compute. reflexivity. Qed.

Lemma drive_suffix :
  run ibtbl 68264 stage_up = Some cf.
Proof. vm_compute. reflexivity. Qed.

Lemma builder_blank_run :
  run ibtbl 68311 c0 = Some cf.
Proof.
  change (run ibtbl (47 + 68264) c0 = Some cf).
  rewrite run_add, prologue_builder_run.
  exact drive_suffix.
Qed.

Lemma builder_blank_halted :
  halted ibtbl cf.
Proof. vm_compute. reflexivity. Qed.

Lemma builder_blank_halts :
  exists c', run ibtbl 68311 c0 = Some c' /\ halted ibtbl c'.
Proof.
  exists cf. split; [apply builder_blank_run | apply builder_blank_halted].
Qed.

Print Assumptions builder_blank_halts.
