(** * Eps0Builder.v -- a tape-driven stage-count builder for the eps0 drive

    The 33-state drive reads its stage count from a written block [1^k].  This
    file adds a 10-state builder that produces that block from a unary source
    already on the tape:

        source 1^k  [blank]  1(seed destination)  0  1(wall) 0 1^v 0 1(seed)

    One source mark is moved per trip.  The destination grows leftwards from
    its seed, while the source shrinks from its right end, so the two stay
    separated by one blank.  A temporary destination seed makes the right end
    fixed; the cleanup erases one mark from the left end, leaving exactly [1^k]
    flush against the wall.  The builder then hands over to [F0] in the drive's
    gap.

    The same table handles every source length [k].  The theorem [builder_run]
    is parametric in [k] and [v] and gives the exact count [10*k+5].

    This file proves the frame handoff.  It does not prove that the 33-state
    drive halts for every stage count; that is a separate obligation.  The
    concrete k=2 composition is proved in [Eps0BuilderBlank.v]. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM Eps0Drive.

Open Scope nat_scope.

(** ** States and table *)

Definition A  : nat := 0.   (* blank right of the source: start/continue *)
Definition A1 : nat := 1.   (* the source's rightmost mark *)
Definition B  : nat := 2.   (* cross the blanks to the destination *)
Definition C  : nat := 3.   (* step back onto the append cell *)
Definition D  : nat := 4.   (* return over the first blank *)
Definition D1 : nat := 5.   (* return over the second blank *)
Definition D2 : nat := 6.   (* the next source mark, or the cleanup entry *)
Definition G  : nat := 7.   (* cleanup: walk to the destination's left end *)
Definition H  : nat := 8.   (* erase that end, then walk to the wall *)
Definition I  : nat := 9.   (* cross the wall into the drive's gap *)

Definition SHIFT : nat := 10.

Definition BUF (v : nat) : list sym :=
  bl :: on :: bl :: ones v ++ bl :: on :: [].

Definition etbl : table := fun s b =>
  match s with
  | 0 =>
      match b with
      | bl => Some (bl, false, A1)
      | on => Some (on, false, A1)
      end
  | 1 =>
      match b with
      | bl => Some (bl, true, G)
      | on => Some (bl, true, B)
      end
  | 2 =>
      match b with
      | bl => Some (bl, true, B)
      | on => Some (on, false, C)
      end
  | 3 =>
      match b with
      | bl => Some (on, false, D)
      | on => Some (on, false, D)
      end
  | 4 =>
      match b with
      | bl => Some (bl, false, D1)
      | on => Some (bl, false, D1)
      end
  | 5 =>
      match b with
      | bl => Some (bl, false, D2)
      | on => Some (bl, false, D2)
      end
  | 6 =>
      match b with
      | bl => Some (bl, true, G)
      | on => Some (on, true, A)
      end
  | 7 =>
      match b with
      | bl => Some (bl, true, G)
      | on => Some (bl, true, H)
      end
  | 8 =>
      match b with
      | bl => Some (bl, true, I)
      | on => Some (on, true, H)
      end
  | 9 =>
      match b with
      | bl => Some (bl, true, SHIFT + F0)
      | on => Some (on, true, SHIFT + F0)
      end
  | _ =>
      match dtbl (s - SHIFT) b with
      | None => None
      | Some (w, d, t) => Some (w, d, t + SHIFT)
      end
  end.

(** ** Frames *)

(** The head is on the blank immediately right of the source.  The source is
    [ones s] to its left; one blank, then the destination [ones (S d)], then
    the wall/value/seed tail. *)
Definition src_frame (s d v : nat) : conf :=
  mkConf A (ones s) bl (bl :: ones (S d) ++ BUF v).

(** The handoff frame.  The final left context is not semantically important
    to [F0]; keeping it as [L] lets the cleanup proof stay parametric. *)
Definition stage_frame_ctx (d v : nat) (L : list sym) : conf :=
  mkConf (SHIFT + F0) (on :: bl :: ones d ++ L) bl
    (ones v ++ bl :: on :: []).

(** ** The destination's right-end seed is permanent during the trip *)

Lemma ones_cons : forall n L, ones n ++ on :: L = on :: (ones n ++ L).
Proof.
  induction n as [|n IH]; intros L.
  - reflexivity.
  - change (on :: ones n ++ on :: L = on :: (on :: ones n ++ L)).
    rewrite IH. reflexivity.
Qed.

(** ** One trip with at least two source marks: 9 steps *)

Lemma cycle_many : forall s d v,
  run etbl 9 (src_frame (S (S s)) d v) =
  Some (src_frame (S s) (S d) v).
Proof.
  intros s d v.
  reflexivity.
Qed.

(** ** One source mark left: 9 steps to the cleanup entry *)

Lemma cycle_one : forall d v,
  run etbl 9 (src_frame 1 d v) =
  Some (mkConf G [bl] bl
          (bl :: ones (S (S d)) ++ BUF v)).
Proof.
  intros d v.
  reflexivity.
Qed.

(** ** Cleanup: erase the destination's leftmost mark and cross the wall

    The head starts on a blank with [ones (S (S d))] at the first mark.  Two
    blank steps reach the destination, one erases its left end, and the
    remaining [S d] marks are walked by [H], which then crosses the wall. *)

Lemma stage_frame_ctx_succ : forall k v L,
  stage_frame_ctx (S k) v (on :: L) =
  stage_frame_ctx (S (S k)) v L.
Proof.
  intros. unfold stage_frame_ctx.
  change (mkConf (SHIFT + F0)
            (on :: bl :: (ones (S k) ++ on :: L)) bl
            (ones v ++ bl :: on :: []) =
          mkConf (SHIFT + F0)
            (on :: bl :: (on :: (ones (S k) ++ L))) bl
            (ones v ++ bl :: on :: [])).
  rewrite ones_cons. reflexivity.
Qed.

Lemma walk_H_step : forall k v L,
  step etbl (mkConf H L on (ones (S k) ++ BUF v)) =
  Some (mkConf H (on :: L) on (ones k ++ BUF v)).
Proof.
  intros. cbn [step etbl]. reflexivity.
Qed.

Lemma walk_H : forall k v L,
  run etbl (k + 3)
    (mkConf H L on (ones k ++ BUF v)) =
  Some (stage_frame_ctx (S k) v L).
Proof.
  induction k as [|k IH]; intros v L.
  - cbn. reflexivity.
  - replace (S k + 3) with (S (k + 3)) by lia.
    rewrite run_S, walk_H_step.
    rewrite IH.
    apply f_equal.
    apply stage_frame_ctx_succ.
Qed.

Lemma cleanup : forall d v L,
  run etbl (S (S d) + 4)
    (mkConf G L bl (bl :: ones (S (S d)) ++ BUF v)) =
  Some (stage_frame_ctx (S d) v (bl :: bl :: bl :: L)).
Proof.
  intros d v L.
  set (D := S (S d)).
  set (C0 := mkConf G L bl (bl :: ones D ++ BUF v)).
  set (C1 := mkConf G (bl :: L) bl (ones D ++ BUF v)).
  set (C2 := mkConf G (bl :: bl :: L) on (ones (S d) ++ BUF v)).
  set (C3 := mkConf H (bl :: bl :: bl :: L) on (ones d ++ BUF v)).
  set (T := stage_frame_ctx (S d) v (bl :: bl :: bl :: L)).
  assert (H1 : run etbl 1 C0 = Some C1).
  { subst C0 C1 D. cbn. reflexivity. }
  assert (H2 : run etbl 1 C1 = Some C2).
  { subst C1 C2 D. cbn. reflexivity. }
  assert (H3 : run etbl 1 C2 = Some C3).
  { subst C2 C3 D. cbn. reflexivity. }
  assert (H4 : run etbl (d + 3) C3 = Some T).
  { subst C3 T. apply walk_H. }
  assert (H12 : run etbl 2 C0 = Some C2).
  { change (run etbl (1 + 1) C0 = Some C2).
    rewrite (run_add etbl 1 1 C0), H1. cbn [run]. reflexivity. }
  assert (H123 : run etbl 3 C0 = Some C3).
  { change (run etbl (2 + 1) C0 = Some C3).
    rewrite (run_add etbl 2 1 C0), H12. cbn [run]. reflexivity. }
  subst D.
  replace (S (S d) + 4) with (3 + (d + 3)) by lia.
  change (run etbl (3 + (d + 3)) C0 = Some T).
  rewrite (run_add etbl 3 (d + 3) C0), H123. cbn [run].
  rewrite H4. reflexivity.
Qed.

(** ** The induction over the source length

    [builder_from s d] treats [s >= 1] source marks and a destination that
    starts with [S d] marks.  It ends with [s + d] stage marks and exactly four
    trailing blanks at the far left of the handoff frame. *)

Lemma builder_from : forall s d v,
  1 <= s ->
  run etbl (10 * s + d + 5) (src_frame s d v) =
  Some (stage_frame_ctx (s + d) v (zeros 4)).
Proof.
  induction s as [|s IH]; intros d v Hs.
  - lia.
  - destruct s as [|s'].
    + (* s = 1: one trip, then cleanup *)
      replace (10 * 1 + d + 5) with (9 + (S (S d) + 4)) by lia.
      rewrite run_add, cycle_one.
      cbn [run].
      change (run etbl (S (S d) + 4)
                (mkConf G [bl] bl
                        (bl :: ones (S (S d)) ++ BUF v)) =
              Some (stage_frame_ctx (S d) v (zeros 4))).
      rewrite cleanup.
      cbn [zeros]. reflexivity.
    + (* s = S (S s'): one many-source trip, then the induction hypothesis *)
      pose proof (IH (S d) v ltac:(lia)) as Hrun.
      replace (10 * S (S s') + d + 5)
        with (9 + (10 * S s' + S d + 5)) by lia.
      rewrite run_add, (cycle_many s' d v).
      replace (S (S s') + d) with (S s' + S d) by lia.
      exact Hrun.
Qed.

(** ** The final handoff theorem *)

Theorem builder_run : forall k v,
  1 <= k ->
  run etbl (10 * k + 5) (src_frame k 0 v) =
  Some (stage_frame_ctx k v (zeros 4)).
Proof.
  intros k v Hk.
  pose proof (builder_from k 0 v Hk) as Hrun.
  replace (10 * k + 0 + 5) with (10 * k + 5) in Hrun by lia.
  replace (k + 0) with k in Hrun by lia.
  exact Hrun.
Qed.

Print Assumptions cycle_many.
Print Assumptions cycle_one.
Print Assumptions walk_H.
Print Assumptions cleanup.
Print Assumptions builder_from.
Print Assumptions builder_run.
