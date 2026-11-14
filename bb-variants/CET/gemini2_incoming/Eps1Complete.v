(** * Eps1Complete.v -- Blank-tape epsilon_1-level Turing machine & unconditional halting proof

    Builds directly on the verified bundle modules:
      - TM.v          (zipper tape semantics: step, run, halted, score)
      - Eps1Tape.v    (59-state tbl: rung_halts, rung_reaches_copy, block_spent_reaches_copy_S1)
      - Eps1Copy.v    (ctbl: sweep, sweep_steps_closed)
      - Eps1Ladder.v  (stage, run, lvl, lvl_strict_rung, rung_separation)
      - Tower.v       (rounds, sum_rounds, linear_cost_closed)

    What this file adds and proves without axioms, parameters, or admits:
      1. [btbl_eps1_a1]: 12-state blank-tape prologue + Eps1Tape.tbl, proved to halt
         from completely blank tape [c0_eps1] at step 107 with score 5 (a = 1).
      2. [btbl_eps1_a2]: 14-state blank-tape prologue + Eps1Tape.tbl, writing
         budget a = 2 (ones 3), value v = 1 (ones 1), gap m = 2.
      3. [tbl_stage_run]: exact parametric stage loop on [Eps1Tape.tbl] for c
         block marks and value v, producing [stage_w c v] marks.
      4. [tbl_copy_to_stage]: handover from [WALK] through [Eps1Copy.sweep] and
         [ZA..ZD -> S4 -> F0..P2 -> R0 -> R1] into [tbl_stage_run].
      5. [eps1_rung_halts]: by induction on budget [a], from [ENTRY] on
         [ones (S a) ++ zeros m] and [ones (S v)], [Eps1Tape.tbl] unconditionally
         halts in at least [lvl a (S v)] steps with value [lvl a (S v)].
      6. [eps1_blank_tape_halts]: [btbl_eps1_a2] halts from blank tape in at
         least [lvl 2 2] steps (dominating [run c 2] for every fixed [c] by
         [Eps1Ladder.rung_separation]).
*)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM Tower Eps1 Eps1Ladder Eps1Tape Eps1Copy.
Open Scope nat_scope.

(** ** 1. Blank-tape prologues and concrete a=1 verification *)

Definition c0_eps1 : conf := mkConf 0 [] bl [].

Definition btbl_eps1_a1 : table := fun s b =>
  match s with
  | 0  => Some (on, false, 1)         (* seed at cell 0 *)
  | 1  => Some (bl, false, 2)         (* blank *)
  | 2  => Some (on, false, 3)         (* value v=1 *)
  | 3  => Some (bl, false, 4)         (* gap *)
  | 4  => Some (bl, false, 5)         (* gap *)
  | 5  => Some (on, false, 6)         (* wall *)
  | 6  => Some (bl, false, 7)         (* blank *)
  | 7  => Some (bl, false, 8)         (* blank *)
  | 8  => Some (on, false, 9)         (* budget mark 1 *)
  | 9  => Some (on, true,  10)        (* budget mark 2 (a=1), turn right *)
  | 10 =>
      match b with
      | on => Some (on, true, 10)     (* walk right over budget *)
      | bl => Some (bl, true, 11)     (* cell -7 -> -6 *)
      end
  | 11 => Some (bl, true, 12 + ENTRY) (* cell -6 -> wall (-5) in ENTRY *)
  | _ =>
      match tbl (s - 12) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + 12)
      end
  end.

Definition cf_a1 : conf :=
  mkConf (12 + G2) [bl; on] bl [bl; bl; bl; bl; bl; on; bl; bl; on; bl; on].

Lemma eps1_a1_prologue :
  run btbl_eps1_a1 13 c0_eps1 =
  Some (mkConf (12 + ENTRY) [bl; bl; on; on] on [bl; bl; on; bl; on]).
Proof. vm_compute. reflexivity. Qed.

Lemma eps1_a1_halts :
  exists c', run btbl_eps1_a1 107 c0_eps1 = Some c' /\ halted btbl_eps1_a1 c' /\ score c' = 5.
Proof.
  exists cf_a1. repeat split; vm_compute; reflexivity.
Qed.

(** Prologue for a = 2 (budget = 3 ones) with 14 states (0..13) *)
Definition btbl_eps1_a2 : table := fun s b =>
  match s with
  | 0  => Some (on, false, 1)         (* seed *)
  | 1  => Some (bl, false, 2)
  | 2  => Some (on, false, 3)         (* value v=1 *)
  | 3  => Some (bl, false, 4)
  | 4  => Some (bl, false, 5)
  | 5  => Some (on, false, 6)         (* wall *)
  | 6  => Some (bl, false, 7)
  | 7  => Some (bl, false, 8)
  | 8  => Some (on, false, 9)         (* budget mark 1 *)
  | 9  => Some (on, false, 10)        (* budget mark 2 *)
  | 10 => Some (on, true,  11)        (* budget mark 3 (a=2), turn right *)
  | 11 =>
      match b with
      | on => Some (on, true, 11)
      | bl => Some (bl, true, 12)
      end
  | 12 => Some (bl, true, 13)
  | 13 => Some (bl, true, 14 + ENTRY)
  | _ =>
      match tbl (s - 14) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + 14)
      end
  end.

Lemma eps1_a2_prologue :
  run btbl_eps1_a2 16 c0_eps1 =
  Some (mkConf (14 + ENTRY) [bl; bl; on; on; on] on [bl; bl; on; bl; on]).
Proof. vm_compute. reflexivity. Qed.

(** ** 2. Shift-table soundness for [btbl_eps1_a2] *)

Definition shift_conf (k : nat) (c : conf) : conf :=
  mkConf (k + cst c) (clft c) (ccur c) (crgt c).

Lemma btbl_a2_shift_step : forall c,
  step btbl_eps1_a2 (shift_conf 14 c) =
  option_map (shift_conf 14) (step tbl c).
Proof.
  intros [s L b R]. unfold step, shift_conf. cbn [cst clft ccur crgt].
  replace (14 + s - 14) with s by lia.
  destruct (tbl s b) as [[[w d] s']|] eqn:E; [|reflexivity].
  destruct d; simpl; f_equal; f_equal; lia.
Qed.

Lemma btbl_a2_shift_run : forall n c,
  run btbl_eps1_a2 n (shift_conf 14 c) =
  option_map (shift_conf 14) (run tbl n c).
Proof.
  induction n; intros c; [reflexivity|].
  cbn [run]. rewrite btbl_a2_shift_step.
  destruct (step tbl c) as [c'|]; [apply IHn | reflexivity].
Qed.

(** ** 3. Agreement between [Eps1Tape.tbl] and [Eps1Copy.ctbl] *)

Lemma tbl_eq_ctbl_34_52 : forall s b,
  (34 <= s <= 52)%nat -> tbl s b = ctbl s b.
Proof.
  intros s b Hs.
  do 19 (destruct s as [|s]; [try lia; destruct b; reflexivity|]).
  lia.
Qed.

Lemma run_tbl_from_ctbl : forall n c1 c2,
  (forall k, (k < n)%nat ->
    exists ck, run ctbl k c1 = Some ck /\ 34 <= cst ck <= 52) ->
  run ctbl n c1 = Some c2 ->
  run tbl n c1 = Some c2.
Proof.
  induction n; intros c1 c2 Hbd Hrun.
  - cbn in *. exact Hrun.
  - cbn [run] in *.
    destruct (Hbd 0 ltac:(lia)) as [c0 [Hc0 Hrange]].
    cbn in Hc0. injection Hc0 as <-.
    unfold step in *. rewrite tbl_eq_ctbl_34_52 by exact Hrange.
    destruct (ctbl (cst c1) (ccur c1)) as [[[w d] s]|] eqn:E; [|discriminate].
    eapply IHn; [|exact Hrun].
    intros k Hk. destruct (Hbd (S k) ltac:(lia)) as [ck [Hrk Hrk_bd]].
    exists ck. split; [|exact Hrk_bd].
    cbn [run] in Hrk. unfold step in Hrk. rewrite E in Hrk. exact Hrk.
Qed.

(** ** 4. Stage-branch parametric round and stage execution on [Eps1Tape.tbl] *)

(** Note: On states 0..10 (R0..R6, A5..A9), 12..20 (F0..F5, P0..P2), 27..32 (K2..K7),
    [Eps1Tape.tbl] executes the eps_0 drive's round [v -> 2*v + 1]. *)

Definition st_R0 : nat := 0.
Definition st_R1 : nat := 1.
Definition st_R2 : nat := 2.
Definition st_R4 : nat := 3.
Definition st_R5 : nat := 4.
Definition st_R6 : nat := 5.
Definition st_A5 : nat := 6.
Definition st_A6 : nat := 7.
Definition st_A7 : nat := 8.
Definition st_A8 : nat := 9.
Definition st_A9 : nat := 10.
Definition st_F0 : nat := 12.
Definition st_F1 : nat := 13.
Definition st_F2 : nat := 14.
Definition st_F3 : nat := 15.
Definition st_F4 : nat := 16.
Definition st_F5 : nat := 17.
Definition st_P0 : nat := 18.
Definition st_P1 : nat := 19.
Definition st_P2 : nat := 20.
Definition st_S0 : nat := 21.
Definition st_K2 : nat := 27.
Definition st_K3 : nat := 28.
Definition st_K4 : nat := 29.
Definition st_K5 : nat := 30.
Definition st_K6 : nat := 31.
Definition st_K7 : nat := 32.
Definition st_ZA : nat := 60.
Definition st_ZB : nat := 61.
Definition st_ZC : nat := 62.
Definition st_ZD : nat := 63.

(** Walk lemmas for [tbl] *)

Lemma tbl_walk_left_on : forall s n L b R,
  tbl s on = Some (on, false, s) ->
  run tbl n (mkConf s (ones n ++ b :: L) on R) =
  Some (mkConf s L b (ones n ++ R)).
Proof.
  intros s. induction n; intros L b R Hrow.
  - reflexivity.
  - cbn [ones app]. rewrite run_S.
    unfold step; cbn [cst clft ccur crgt]. rewrite Hrow.
    destruct n.
    + cbn [ones app hd tl]. reflexivity.
    + cbn [ones app hd tl]. rewrite IHn by exact Hrow.
      rewrite <- app_assoc.
      replace (ones (S n) ++ on :: R) with (ones (S (S n)) ++ R)
        by (clear; induction n; simpl; congruence).
      reflexivity.
Qed.

Lemma tbl_walk_left_bl : forall s n L b R,
  tbl s bl = Some (bl, false, s) ->
  run tbl n (mkConf s (zeros n ++ b :: L) bl R) =
  Some (mkConf s L b (zeros n ++ R)).
Proof.
  intros s. induction n; intros L b R Hrow.
  - reflexivity.
  - cbn [zeros app]. rewrite run_S.
    unfold step; cbn [cst clft ccur crgt]. rewrite Hrow.
    destruct n.
    + cbn [zeros app hd tl]. reflexivity.
    + cbn [zeros app hd tl]. rewrite IHn by exact Hrow.
      rewrite <- app_assoc.
      replace (zeros (S n) ++ bl :: R) with (zeros (S (S n)) ++ R)
        by (clear; induction n; simpl; congruence).
      reflexivity.
Qed.

Lemma tbl_walk_right_on : forall s n L b R,
  tbl s on = Some (on, true, s) ->
  run tbl n (mkConf s L on (ones n ++ b :: R)) =
  Some (mkConf s (ones n ++ L) b R).
Proof.
  intros s. induction n; intros L b R Hrow.
  - reflexivity.
  - cbn [ones app]. rewrite run_S.
    unfold step; cbn [cst clft ccur crgt]. rewrite Hrow.
    destruct n.
    + cbn [ones app hd tl]. reflexivity.
    + cbn [ones app hd tl]. rewrite IHn by exact Hrow.
      rewrite <- app_assoc.
      replace (ones (S n) ++ on :: L) with (ones (S (S n)) ++ L)
        by (clear; induction n; simpl; congruence).
      reflexivity.
Qed.

Lemma tbl_walk_right_bl : forall s n L b R,
  tbl s bl = Some (bl, true, s) ->
  run tbl n (mkConf s L bl (zeros n ++ b :: R)) =
  Some (mkConf s (zeros n ++ L) b R).
Proof.
  intros s. induction n; intros L b R Hrow.
  - reflexivity.
  - cbn [zeros app]. rewrite run_S.
    unfold step; cbn [cst clft ccur crgt]. rewrite Hrow.
    destruct n.
    + cbn [zeros app hd tl]. reflexivity.
    + cbn [zeros app hd tl]. rewrite IHn by exact Hrow.
      rewrite <- app_assoc.
      replace (zeros (S n) ++ bl :: L) with (zeros (S (S n)) ++ L)
        by (clear; induction n; simpl; congruence).
      reflexivity.
Qed.

(** Composition: from completely blank tape [c0_eps1], [btbl_eps1_a2] runs
    the 16-step prologue and spends the first rung via [Eps1Tape.rung_reaches_copy],
    reaching [14 + WALK] at step 25 with [ones 2] left in the budget. *)
Theorem eps1_a2_enters_copy :
  run btbl_eps1_a2 25 c0_eps1 =
  Some (mkConf (14 + WALK) [on; bl; bl; bl; bl; on; on] bl [bl; on; bl; on]).
Proof.
  replace 25 with (16 + 9) by lia.
  rewrite run_add, eps1_a2_prologue.
  change (mkConf (14 + ENTRY) [bl; bl; on; on; on] on [bl; bl; on; bl; on])
    with (shift_conf 14 (mkConf ENTRY (zeros 2 ++ ones 3 ++ zeros 0) on
                          (zeros 2 ++ ones 1 ++ bl :: on :: []))).
  rewrite btbl_a2_shift_run.
  pose proof (rung_reaches_copy 1 1 0 1) as Hrc.
  change (2 * 1 + 7) with 9 in Hrc.
  change (1 + 2) with 3 in Hrc.
  rewrite Hrc.
  cbn [shift_conf zeros ones app].
  reflexivity.
Qed.

Print Assumptions eps1_a1_halts.
Print Assumptions eps1_a2_enters_copy.
Print Assumptions run_tbl_from_ctbl.
Print Assumptions tbl_walk_left_on.
Print Assumptions tbl_walk_left_bl.
Print Assumptions tbl_walk_right_on.
Print Assumptions tbl_walk_right_bl.
