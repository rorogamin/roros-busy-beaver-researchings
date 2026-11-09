(** * StackPass: the engine of Machine 5 as a symbolic doubling pass

    Machine5.v certifies one concrete run by evaluation.  This file opens the
    symbolic argument that every pass of the engine doubles the counter, for a
    counter of any length.

    Geometry of one pass (measured, see the traces in the README section on
    machine 5).  Entry: the head is on the counter's leftmost mark, state
    [ENTRY].  Then

      ENTRY  walks right over the counter to the first blank,
      E0     erases the counter's rightmost mark and steps left,
      E1     walks left over the rest of the source to the two separator cells,
      E2/E3  cross them and append one mark to the left end of the destination,
      E4/E6  walk back right to the erased cursor and restore it,
      E7     erases the next source mark and steps left, or finishes.

    So each iteration moves one cell from the source to the destination, and
    [c] iterations turn `1^c` into `1^(2c+2)` (`2c` copied, two from filling
    the separators), which for [r] rounds gives `3*2^(r+1) - 2`.

    This file proves the entry sweep, the twenty one-step lemmas, the four walk
    lemmas and the copy-loop round itself ([round], with [pass_loop] for [c]
    rounds and [pass_run] joining it to the entry sweep).  The [E7] exit and the
    [D0] sweep that rewrite the layout for the next pass are not modelled
    here; the [E9] block sweep and the [D0] hand-over are ([walk_E9],
    [exit_sweep]).  Nothing in this file is assumed: every lemma is about the
    literal table [tbl] of Machine5.v, and `tools/round_check.py` checks the
    round statements numerically against the same table. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Machine5.
Import ListNotations.

(** ** State names *)

Definition ENTRY : nat := 200.
Definition E0 : nat := 201.
Definition E1 : nat := 202.
Definition E2 : nat := 203.
Definition E3 : nat := 204.
Definition E4 : nat := 205.
Definition E5 : nat := 206.
Definition E6 : nat := 207.
Definition E7 : nat := 208.
Definition E8 : nat := 209.
Definition E9 : nat := 210.
Definition E10 : nat := 211.
Definition D0 : nat := 220.
Definition D1 : nat := 221.

(** ** Block arithmetic *)

Lemma ones_succ : forall n L, ones n ++ on :: L = ones (S n) ++ L.
Proof.
  intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - change (on :: (ones n ++ on :: L) = on :: (ones (S n) ++ L)).
    rewrite IH. reflexivity.
Qed.

Lemma hd_ones : forall n R, hd bl (ones (S n) ++ R) = on.
Proof.
  intros. change (hd bl (on :: (ones n ++ R)) = on). reflexivity.
Qed.

Lemma tl_ones : forall n R, tl (ones (S n) ++ R) = ones n ++ R.
Proof.
  intros. change (tl (on :: (ones n ++ R)) = ones n ++ R). reflexivity.
Qed.

(** ** One-step lemmas, straight from the literal table *)

Lemma st_ENTRY_on : forall L R,
  step tbl (mkConf ENTRY L on R) =
  Some (mkConf ENTRY (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_ENTRY_bl : forall L R,
  step tbl (mkConf ENTRY L bl R) =
  Some (mkConf E0 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E0_on : forall L R,
  step tbl (mkConf E0 L on R) =
  Some (mkConf E1 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E1_on : forall L R,
  step tbl (mkConf E1 L on R) =
  Some (mkConf E1 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E1_bl : forall L R,
  step tbl (mkConf E1 L bl R) =
  Some (mkConf E2 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E2_bl : forall L R,
  step tbl (mkConf E2 L bl R) =
  Some (mkConf E3 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E3_on : forall L R,
  step tbl (mkConf E3 L on R) =
  Some (mkConf E3 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E3_bl : forall L R,
  step tbl (mkConf E3 L bl R) =
  Some (mkConf E4 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E4_on : forall L R,
  step tbl (mkConf E4 L on R) =
  Some (mkConf E4 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E4_bl : forall L R,
  step tbl (mkConf E4 L bl R) =
  Some (mkConf E5 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E5_bl : forall L R,
  step tbl (mkConf E5 L bl R) =
  Some (mkConf E6 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E6_on : forall L R,
  step tbl (mkConf E6 L on R) =
  Some (mkConf E6 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E6_bl : forall L R,
  step tbl (mkConf E6 L bl R) =
  Some (mkConf E7 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E7_on : forall L R,
  step tbl (mkConf E7 L on R) =
  Some (mkConf E1 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E7_bl : forall L R,
  step tbl (mkConf E7 L bl R) =
  Some (mkConf E8 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E8_bl : forall L R,
  step tbl (mkConf E8 L bl R) =
  Some (mkConf E9 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_E9_on : forall L R,
  step tbl (mkConf E9 L on R) =
  Some (mkConf E9 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E9_bl : forall L R,
  step tbl (mkConf E9 L bl R) =
  Some (mkConf E10 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_E10_bl : forall L R,
  step tbl (mkConf E10 L bl R) =
  Some (mkConf D0 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_D0_on : forall L R,
  step tbl (mkConf D0 L on R) =
  Some (mkConf D1 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

(** ** The entry sweep

    The head starts on the counter's leftmost mark with [n] marks to its right.
    [ENTRY] walks right over all of them and stops on the gap's first blank,
    after [S n] steps; then [E0] erases the last mark and steps left. *)

Lemma walk_ENTRY : forall n L R,
  run tbl (S n) (mkConf ENTRY L on (ones n ++ bl :: R)) =
  Some (mkConf ENTRY (ones (S n) ++ L) bl R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_ENTRY_on.
    rewrite hd_ones, tl_ones.
    rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

(** From the entry configuration to the first loop head: two marks are consumed
    by the entry sweep and [E0], so the loop starts on the counter's [n+1]-th
    mark with [n] marks still to its left. *)

Lemma pass_start : forall n L R,
  run tbl (S (S n) + 2) (mkConf ENTRY L on (ones (S n) ++ bl :: R)) =
  Some (mkConf E1 (ones n ++ L) on (bl :: bl :: R)).
Proof.
  intros n L R.
  rewrite run_add with (a := S (S n)) (b := 2).
  rewrite walk_ENTRY.
  cbn [hd tl].
  rewrite run_S, st_ENTRY_bl.
  rewrite tl_ones, hd_ones.
  rewrite run_S, st_E0_on.
  rewrite tl_ones, hd_ones.
  reflexivity.
Qed.

(** ** The copy loop

    [loop_inv s d L R] is the configuration at the top of one iteration: the
    head is on the rightmost remaining source mark, [s] further source marks
    are to its left, then the two separator cells, then the [d] marks built by
    the previous iterations, then the untouched context [L].  To the right of
    the head are the erased cursor cell, the marks already finalised, and the
    gap followed by the stack [R].

    Each iteration takes one mark from the source to the destination.  With [s]
    and [d] the source and destination counts at the START of the round, one
    round costs exactly `2s + 2d + 9` steps and carries

      loop_inv s d (bl :: L) R   -->   loop_inv (s-1) (d+1) L (on :: R).

    Three things move, and an earlier version of this comment missed two of them:
    the source loses a mark, the destination gains one, the left context loses
    its leading blank (the destination grows leftwards into it) and the right
    tail gains one mark (the erase shifts the source one cell right).  The old
    text claimed `2s + 2d + 7` with [L] and [R] fixed.

    The [s = 0] case is not a round at all: the source is exhausted, so the
    erase step lands on a blank and [E7] exits to [E8] instead of returning to
    [E1].  The pass therefore ends with [s = 0], not by counting rounds.

    PROVED below.  [round] is the round statement, assembled from three lemmas:
    [round_zero] (empty destination), [round_pos] (non-empty destination) and
    [round_back] (the return path), each chained with [run_cat].  [pass_loop]
    iterates the round -- the per-round cost `2 s + 2 d + 9` stays constant
    because the two counts sum to `c + s + d` -- and [pass_run] joins it to the
    entry sweep.  `tools/round_check.py` is the independent numerical check of
    the same statements against the literal table, and it also confirms the [E7]
    exit that the loop does not model. *)


(** ** Rotating a mark across a block *)

Lemma on_rotate : forall n x, ones n ++ on :: x = on :: (ones n ++ x).
Proof.
  intros n. induction n as [|n IH]; intros x.
  - reflexivity.
  - change (on :: (ones n ++ on :: x) = on :: (on :: (ones n ++ x))).
    rewrite IH. reflexivity.
Qed.

Lemma hd_ones_cons : forall n x, hd bl (ones n ++ on :: x) = on.
Proof. intros. rewrite on_rotate. reflexivity. Qed.

Lemma tl_ones_cons : forall n x, tl (ones n ++ on :: x) = ones n ++ x.
Proof. intros. rewrite on_rotate. reflexivity. Qed.

(** ** Walking over a block of marks

    [walk_E1] crosses [n] source marks leftwards and stops on the leftmost of
    them; [walk_E3] does the same over the destination.  [walk_E4] and
    [walk_E6] go rightwards and stop on the blank that ends the block. *)

Lemma walk_E1 : forall n L X,
  run tbl n (mkConf E1 (ones n ++ bl :: L) on X) =
  Some (mkConf E1 (bl :: L) on (ones n ++ X)).
Proof.
  intros n. induction n as [|n IH]; intros L X.
  - reflexivity.
  - rewrite run_S, st_E1_on.
    rewrite tl_ones, hd_ones.
    rewrite IH. rewrite on_rotate. reflexivity.
Qed.

Lemma walk_E3 : forall n L X,
  run tbl n (mkConf E3 (ones n ++ bl :: L) on X) =
  Some (mkConf E3 (bl :: L) on (ones n ++ X)).
Proof.
  intros n. induction n as [|n IH]; intros L X.
  - reflexivity.
  - rewrite run_S, st_E3_on.
    rewrite tl_ones, hd_ones.
    rewrite IH. rewrite on_rotate. reflexivity.
Qed.

Lemma walk_E4 : forall n L X,
  run tbl (S n) (mkConf E4 L on (ones n ++ bl :: X)) =
  Some (mkConf E4 (ones (S n) ++ L) bl X).
Proof.
  intros n. induction n as [|n IH]; intros L X.
  - reflexivity.
  - rewrite run_S, st_E4_on.
    rewrite tl_ones, hd_ones.
    rewrite IH.
    rewrite on_rotate. reflexivity.
Qed.

Lemma walk_E6 : forall n L X,
  run tbl (S n) (mkConf E6 L on (ones n ++ bl :: X)) =
  Some (mkConf E6 (ones (S n) ++ L) bl X).
Proof.
  intros n. induction n as [|n IH]; intros L X.
  - reflexivity.
  - rewrite run_S, st_E6_on.
    rewrite tl_ones, hd_ones.
    rewrite IH.
    rewrite on_rotate. reflexivity.
Qed.

Definition loop_inv (s d : nat) (L R : list sym) : conf :=
  mkConf E1 (ones s ++ zeros 2 ++ ones d ++ L) on (bl :: R).

(** ** The round lemma, machine-checked

    [round] is the statement checked numerically by tools/round_check.py: one
    round costs `2 s + 2 d + 9` steps (with [s], [d] the counts at the start) and
    carries `loop_inv s d (bl :: L) R` to `loop_inv (s-1) (d+1) L (on :: R)`.
    The [s = 0] case is the [E7] exit, not a round, so [round] needs no
    hypothesis: it is legal even for the last source mark. *)

Lemma run_cat : forall (k1 k2 : nat) (c1 c2 c3 : conf),
  run tbl k1 c1 = Some c2 ->
  run tbl k2 c2 = Some c3 ->
  run tbl (k1 + k2) c1 = Some c3.
Proof.
  intros k1 k2 c1 c2 c3 H1 H2.
  rewrite run_add, H1. cbn. exact H2.
Qed.

(** Back half of a round: the [E6] walk over the source, its write into the
    cursor and the [E7] erase, i.e. `S s + 2` steps for [S s] source marks.
    The two fixed steps after the walk are computed by [cbn]. *)

Lemma round_back : forall a c L R,
  run tbl (S (S a) + 2)
    (mkConf E6 (zeros 2 ++ ones (S c) ++ L) on (ones (S a) ++ bl :: R)) =
  Some (loop_inv a (S c) L (on :: R)).
Proof.
  intros a c L R.
  apply run_cat with (k1 := S (S a)) (k2 := 2)
    (c2 := mkConf E6 (ones (S (S a)) ++ zeros 2 ++ ones (S c) ++ L) bl R).
  - rewrite (walk_E6 (S a) (zeros 2 ++ ones (S c) ++ L) R). reflexivity.
  - cbn. unfold loop_inv. reflexivity.
Qed.

(** Front half with an empty destination: source walk, the two separator
    crossings and the two blank returns, i.e. [s + 6] steps. *)

Lemma round_zero : forall a L R,
  run tbl (S a + 6) (loop_inv (S a) 0 (bl :: L) R) =
  Some (mkConf E6 (zeros 2 ++ on :: L) on (ones (S a) ++ bl :: R)).
Proof.
  intros a L R.
  change (run tbl (S a + 6)
            (mkConf E1 (ones (S a) ++ bl :: bl :: bl :: L) on (bl :: R)) =
          Some (mkConf E6 (zeros 2 ++ on :: L) on (ones (S a) ++ bl :: R))).
  apply run_cat with (k1 := S a) (k2 := 6)
    (c2 := mkConf E1 (bl :: bl :: bl :: L) on (ones (S a) ++ bl :: R)).
  - rewrite (walk_E1 (S a) (bl :: bl :: L) (bl :: R)). reflexivity.
  - cbn. reflexivity.
Qed.

(** Front half with a non-empty destination: same walk, then the [E3] sweep
    over the [d] destination marks, its write, the [E4] walk back and the two
    blank steps of [E5]. *)

Lemma round_pos : forall a d L R,
  run tbl (S a + (3 + (d + (2 + (S d + 2))))) (loop_inv (S a) (S d) (bl :: L) R) =
  Some (mkConf E6 (zeros 2 ++ ones (S (S d)) ++ L) on (ones (S a) ++ bl :: R)).
Proof.
  intros a d L R.
  change (run tbl (S a + (3 + (d + (2 + (S d + 2)))))
            (mkConf E1 (ones (S a) ++ bl :: bl :: ones (S d) ++ bl :: L) on (bl :: R)) =
          Some (mkConf E6 (zeros 2 ++ ones (S (S d)) ++ L) on (ones (S a) ++ bl :: R))).
  apply run_cat with (k1 := S a) (k2 := (3 + (d + (2 + (S d + 2)))))
    (c2 := mkConf E1 (bl :: bl :: ones (S d) ++ bl :: L) on (ones (S a) ++ bl :: R)).
  - rewrite (walk_E1 (S a) (bl :: ones (S d) ++ bl :: L) (bl :: R)). reflexivity.
  - apply run_cat with (k1 := 3) (k2 := (d + (2 + (S d + 2))))
      (c2 := mkConf E3 (ones d ++ bl :: L) on (bl :: bl :: on :: ones (S a) ++ bl :: R)).
    + cbn. reflexivity.
    + apply run_cat with (k1 := d) (k2 := (2 + (S d + 2)))
        (c2 := mkConf E3 (bl :: L) on (ones d ++ bl :: bl :: on :: ones (S a) ++ bl :: R)).
      * rewrite (walk_E3 d L (bl :: bl :: on :: ones (S a) ++ bl :: R)). reflexivity.
      * apply run_cat with (k1 := 2) (k2 := (S d + 2))
          (c2 := mkConf E4 (on :: L) on (ones d ++ bl :: bl :: on :: ones (S a) ++ bl :: R)).
        { cbn. reflexivity. }
        apply run_cat with (k1 := S d) (k2 := 2)
          (c2 := mkConf E4 (ones (S d) ++ on :: L) bl (bl :: on :: ones (S a) ++ bl :: R)).
        { rewrite (walk_E4 d (on :: L) (bl :: on :: ones (S a) ++ bl :: R)). reflexivity. }
        cbn. rewrite ones_succ. reflexivity.
Qed.

(** One round of the copy loop. *)

Lemma round : forall a c L R,
  run tbl (2 * S a + 2 * c + 9) (loop_inv (S a) c (bl :: L) R) =
  Some (loop_inv a (S c) L (on :: R)).
Proof.
  intros a [|d] L R.
  - replace (2 * S a + 2 * 0 + 9) with (S a + 6 + (S (S a) + 2)) by lia.
    apply run_cat with (k1 := S a + 6) (k2 := S (S a) + 2)
      (c2 := mkConf E6 (zeros 2 ++ on :: L) on (ones (S a) ++ bl :: R)).
    + exact (round_zero a L R).
    + exact (round_back a 0 L R).
  - replace (2 * S a + 2 * S d + 9)
      with (S a + (3 + (d + (2 + (S d + 2)))) + (S (S a) + 2)) by lia.
    apply run_cat with (k1 := S a + (3 + (d + (2 + (S d + 2))))) (k2 := S (S a) + 2)
      (c2 := mkConf E6 (zeros 2 ++ ones (S (S d)) ++ L) on (ones (S a) ++ bl :: R)).
    + exact (round_pos a d L R).
    + exact (round_back a (S d) L R).
Qed.

(** Entry sweep into the invariant: the two separator blanks must already be
    in place, which is what the previous pass leaves behind. *)

Lemma pass_start_inv : forall n L R,
  run tbl (S (S n) + 2) (mkConf ENTRY (zeros 2 ++ L) on (ones (S n) ++ bl :: R)) =
  Some (loop_inv (n + 0) 0 L (bl :: R)).
Proof.
  intros n L R. unfold loop_inv. replace (n + 0) with n by lia. apply pass_start.
Qed.

(** [c] rounds of the loop: the per-round cost `2 s + 2 d + 9` is constant
    because the source and destination counts always sum to `c + s + d`, so the
    total is `c * (2 (c + s + d) + 9)` -- `c * (2c + 9)` for the pass itself. *)

Lemma pass_loop : forall c s d L R,
  run tbl (c * (2 * (c + s + d) + 9))
    (loop_inv (c + s) d (zeros c ++ L) R) =
  Some (loop_inv s (c + d) L (ones c ++ R)).
Proof.
  induction c as [|c IH]; intros s d L R.
  - cbn. reflexivity.
  - replace (S c * (2 * (S c + s + d) + 9))
      with (2 * S (c + s) + 2 * d + 9 + c * (2 * (c + s + S d) + 9)) by lia.
    apply run_cat with (k1 := 2 * S (c + s) + 2 * d + 9)
                      (k2 := c * (2 * (c + s + S d) + 9))
      (c2 := loop_inv (c + s) (S d) (zeros c ++ L) (on :: R)).
    + exact (round (c + s) d (zeros c ++ L) R).
    + replace (S c + d) with (c + S d) by lia.
      rewrite <- ones_succ.
      exact (IH s (S d) L (on :: R)).
Qed.

(** The pass's loop phase: from the entry sweep's invariant to an exhausted
    source, still inside the loop states.  The [E7] exit, the [E9] sweep and the
    hand-over to [D0]/[D1] that rewrite the layout for the next pass are not
    covered here. *)

Lemma pass_run : forall c L R,
  run tbl (S (S c) + 2 + c * (2 * (c + 0 + 0) + 9))
    (mkConf ENTRY (zeros 2 ++ zeros c ++ L) on (ones (S c) ++ bl :: R)) =
  Some (loop_inv 0 (c + 0) L (ones c ++ bl :: R)).
Proof.
  intros c L R.
  apply run_cat with (k1 := S (S c) + 2) (k2 := c * (2 * (c + 0 + 0) + 9))
    (c2 := loop_inv (c + 0) 0 (zeros c ++ L) (bl :: R)).
  - exact (pass_start_inv c (zeros c ++ L) R).
  - exact (pass_loop c 0 0 L (bl :: R)).
Qed.

(** The deterministic front of a carry step: with the source exhausted the head
    sits on a blank with [m+1] settled marks to its left and a blank beyond them.
    [E1] and [E2] cross the two blanks, the [E3] walk runs out the mark block, the
    write puts a fresh mark at its left end, and the [E4] walk comes back over the
    block -- `2 m + 5` steps, leaving [E4] on the blank with the block one mark
    longer and the two crossed cells pushed onto the right.  This composes: it is
    the body of an exit carry step, before the [E7] test that decides whether the
    block is finished (exit) or still needs a carry. *)

Lemma carry_front : forall m Z0 R,
  run tbl (2 + m + 2 + S m)
    (mkConf E1 (bl :: ones (S m) ++ bl :: Z0) bl R) =
  Some (mkConf E4 (ones (S m) ++ on :: Z0) bl (bl :: R)).
Proof.
  intros m Z0 R.
  replace (2 + m + 2 + S m) with (1 + (1 + (m + (1 + (1 + S m))))) by lia.
  apply run_cat with (k1 := 1) (k2 := 1 + (m + (1 + (1 + S m))))
    (c2 := mkConf E2 (ones (S m) ++ bl :: Z0) bl (bl :: R)).
  - cbn. reflexivity.
  - apply run_cat with (k1 := 1) (k2 := m + (1 + (1 + S m)))
      (c2 := mkConf E3 (ones m ++ bl :: Z0) on (bl :: bl :: R)).
    + cbn. reflexivity.
    + apply run_cat with (k1 := m) (k2 := 1 + (1 + S m))
        (c2 := mkConf E3 (bl :: Z0) on (ones m ++ bl :: bl :: R)).
      * exact (walk_E3 m Z0 (bl :: bl :: R)).
      * apply run_cat with (k1 := 1) (k2 := 1 + S m)
          (c2 := mkConf E3 Z0 bl (ones (S m) ++ bl :: bl :: R)).
        { cbn. reflexivity. }
        apply run_cat with (k1 := 1) (k2 := S m)
          (c2 := mkConf E4 (on :: Z0) on (ones m ++ bl :: bl :: R)).
        { cbn. reflexivity. }
        exact (walk_E4 m (on :: Z0) (bl :: R)).
Qed.

(** The exit path in one piece: from the exhausted-source loop head, the carry
    front grows the block, the two blank steps and the [E7]/[E8] writes hand over,
    and [E9] starts its sweep with the block one mark longer and the two erased
    cells plus their blank in front -- `2 m + 10` steps.
    Composing with [exit_sweep] takes this all the way to [D0], so the whole exit
    is machine-checked except the [E7] re-entry branch and [D0]'s blank crossing. *)

Lemma carry_exit : forall m Z0 R1,
  run tbl (2 + m + 2 + S m + 5)
    (mkConf E1 (bl :: ones (S m) ++ bl :: Z0) bl (bl :: bl :: R1)) =
  Some (mkConf E9 (ones m ++ on :: Z0) on (on :: on :: on :: bl :: R1)).
Proof.
  intros m Z0 R1.
  replace (2 + m + 2 + S m + 5) with ((2 + m + 2 + S m) + 5) by lia.
  apply run_cat with (k1 := 2 + m + 2 + S m) (k2 := 5)
    (c2 := mkConf E4 (ones (S m) ++ on :: Z0) bl (bl :: bl :: bl :: R1)).
  - exact (carry_front m Z0 (bl :: bl :: R1)).
  - cbn. reflexivity.
Qed.

(** [E9] sweeps the marks the last round finalised: it crosses [n] of them and
    stops on the blank that ends the block, exactly like [walk_E6] on the other
    side of the loop. *)

Lemma walk_E9 : forall n L R,
  run tbl (S n) (mkConf E9 L on (ones n ++ bl :: R)) =
  Some (mkConf E9 (ones (S n) ++ L) bl R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_E9_on.
    rewrite hd_ones, tl_ones.
    rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

(** The hand-over to the stack engine: after the sweep, [E9] erases nothing and
    steps onto the gap, [E10] follows, and [D0] takes over.  This is the one part
    of the exit that is a straight sequence rather than a layout-driven loop. *)

Lemma exit_sweep : forall n L R,
  run tbl (S n + 2) (mkConf E9 L on (ones n ++ bl :: bl :: R)) =
  Some (mkConf D0 (bl :: bl :: ones (S n) ++ L) (hd bl R) (tl R)).
Proof.
  intros n L R.
  apply run_cat with (k1 := S n) (k2 := 2)
    (c2 := mkConf E9 (ones (S n) ++ L) bl (bl :: R)).
  - exact (walk_E9 n L (bl :: R)).
  - cbn. reflexivity.
Qed.

(** The pass's exit, start to finish: from the loop head with an exhausted
    source, one carry step (which grows the block by a mark) and the [E9] sweep
    hand the tape to [D0] in `2 m + 16` steps.  This is the first theorem in this
    file that spans the whole second half of a pass; it composes the carry body
    ([carry_front]), the [E7]/[E8] writes ([carry_exit]) and the sweep plus the
    [D0] landing ([exit_sweep]).  It is not yet a *pass* lemma: the counter's
    doubling still needs the [E7] re-entry branch, where the block is not
    finished and the carry repeats. *)

Lemma exit_run : forall m Z0 R,
  run tbl (2 + m + 2 + S m + 5 + 6)
    (mkConf E1 (bl :: ones (S m) ++ bl :: Z0) bl (bl :: bl :: bl :: R)) =
  Some (mkConf D0 (bl :: bl :: ones 4 ++ ones m ++ on :: Z0) (hd bl R) (tl R)).
Proof.
  intros m Z0 R.
  replace (2 + m + 2 + S m + 5 + 6) with ((2 + m + 2 + S m + 5) + 6) by lia.
  apply run_cat with (k1 := 2 + m + 2 + S m + 5) (k2 := 6)
    (c2 := mkConf E9 (ones m ++ on :: Z0) on (on :: on :: on :: bl :: bl :: R)).
  - exact (carry_exit m Z0 (bl :: R)).
  - exact (exit_sweep 3 (ones m ++ on :: Z0) R).
Qed.

(** ** The exit phase: what is proved, and what stops it closing

    After the last round the source is empty, so [E7] sits on a blank and leaves
    the loop: [E7] --(on, left)--> [E8] --(on, left)--> [E9], which sweeps RIGHT
    over the settled marks, stops on a blank, and goes [E9] --> [E10] --> [D0].
    The sweep and the hand-over are proved above, for any number of marks and any
    context: [walk_E9] crosses the block, [exit_sweep] lands on [D0] with the two
    erased cells pushed back onto the left context.  Two facts stop the rest of
    the rest of the exit being another closed invariant: [carry_front] proves the
    body of one carry step (the two erasures, the block walk, the fresh mark and
    the return walk), so only the [E7] re-entry test is left unmodelled.  What
    remains is:

      [D0] is `220 bl -> bl,R,220`, i.e. it crosses blank cells to the right and
      stops only when it meets the next field of the stack.  On blank tape it
      runs right forever -- checked, not guessed, by tools/round_check.py, which
      also shows that a gap of [g] blanks followed by a stack stops it after [g]
      steps.

      The [E9] sweep length is a function of the whole layout (the destination,
      the left context and the settled marks), not of the source count alone.

      Nor is the approach to [E9] a straight sweep.  With a blank left context
      the exit from [loop_inv 0 d] costs `4 d + 26` steps (measured for `d <= 4`
      and asserted in tools/round_check.py), because [E2]/[E3]/[E4] first run a
      carry loop that lengthens the left mark run, [E5]..[E8] test it, and only
      the [E8]-on-blank case gets out to [E9].  That loop, like [D0]'s blank
      crossing, is driven by the layout rather than by the source count.

    So the second half of a pass -- the hand-over that rebuilds the layout for
    the next pass, and with it the `c -> 2c+2` doubling -- needs the stack's
    field structure in the invariant.  That is the next piece of work; this file
    deliberately stops at the loop, where the invariant closes. *)

Print Assumptions walk_E9.
Print Assumptions exit_sweep.
Print Assumptions carry_front.
Print Assumptions carry_exit.
Print Assumptions exit_run.
