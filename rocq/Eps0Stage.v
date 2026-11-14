(* The eps_0 drive's stage: [c] consecutive parametric rounds.

   [Eps0Round.round_v] proves one round for a value of arbitrary length.
   This file iterates it over [c] counter marks.  The tape shape is the same
   at every entry:

       R1 (ones c ++ L) on (on :: zeros m ++ ones (S v) ++ bl :: on :: [])

   After [c] rounds the counter marks are gone, the value is
   [S (stage_w c v)] marks, and the gap is [stage_gap c m v].  The step count
   is the sum of the per-round costs, [stage_cost].

   This is the whole interior of the drive's loop.  It is not a blank-tape
   machine and it makes no FGH-level claim: [c] is still supplied by the
   caller. *)

From Stdlib Require Import List Arith Lia.
From Top Require Import TM ModuleK Eps0Drive Eps0Round.
Import ListNotations.
Open Scope nat_scope.

Fixpoint stage_gap (c m v : nat) : nat :=
  match c with
  | 0 => m
  | S c' => stage_gap c' (m + S v + 2) (2 * S v)
  end.

Fixpoint stage_w (c v : nat) : nat :=
  match c with
  | 0 => v
  | S c' => stage_w c' (2 * S v)
  end.

Fixpoint stage_cost (c m v : nat) : nat :=
  match c with
  | 0 => 0
  | S c' => round_sum m v + stage_cost c' (m + S v + 2) (2 * S v)
  end.

Lemma stage_run : forall c m v L,
  run dtbl (stage_cost c m v)
    (mkConf R1 (ones c ++ L) on
            (on :: zeros m ++ ones (S v) ++ bl :: on :: [])) =
  Some (mkConf R1 L on
          (on :: zeros (stage_gap c m v) ++
           ones (S (stage_w c v)) ++ bl :: on :: [])).
Proof.
  induction c as [|c IH]; intros m v L.
  - cbn. reflexivity.
  - cbn [stage_cost stage_gap stage_w].
    change (run dtbl (round_sum m v +
                      stage_cost c (m + S v + 2) (2 * S v))
      (mkConf R1 (on :: ones c ++ L) on
              (on :: zeros m ++ ones (S v) ++ bl :: on :: [])) =
      Some (mkConf R1 L on
              (on :: zeros (stage_gap c (m + S v + 2) (2 * S v)) ++
               ones (S (stage_w c (2 * S v))) ++ bl :: on :: []))).
    rewrite run_add, (round_v m v (ones c ++ L)).
    cbn [run].
    replace (2 * S v + 1) with (S (2 * S v)) by lia.
    apply IH.
Qed.

Print Assumptions stage_run.
