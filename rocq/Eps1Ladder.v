(* The ladder the eps_1 machine descends, fixed as a rule about values.

   Tower.v proves one stage worth of the eps_0 engine: a block of v marks goes
   to (v + 1) * 2 ^ c - 1 in c rounds.  Eps1.v takes the round count from the
   value itself (nest v = rounds v v) and proves that no fixed stage count
   catches that diagonal.

   What neither file fixes is the *shape of the level*, which is what the eps_1
   table has to be built against.  Two things about it are worth stating
   precisely, because both are easy to get wrong.

   First, one stage of the eps_0 engine, counting from an empty block with the
   count taken from the value, is

       stage v = 2 ^ (S v) - 1 = rounds (S v) 0

   which is what the frame check in tools/eps1_machine.py observes: stages 1, 1
   twice, 2, 2 twice give 3, 7, 15, 255, 7.  n stages are [run n].

   Second, the level is NOT obtained by nesting [stage] or [nest].  Nesting a
   stage function k times is still one exponentiation of height k: that is the
   eps_0 rung wearing a different hat, and calling it eps_1 is exactly the
   mistake this file exists to prevent.  The level comes from where the *count*
   is read:

       lvl 0 v     = v                       (the engine is not running)
       lvl (S k) v = run (lvl k v) v         (the count is the previous
                                              level's own output)

   so each rung hands the next rung its stage count, and nothing is guessed.
   The descent is on k -- one rung spent per outer turn -- which is why the outer
   loop terminates by induction on k, and why the eps_1 machine needs a
   *preserving* copy of the value: to run [run (lvl k v) v] the table has to read
   a number off the tape and keep the value that produced it.

   What is proved below, for every parameter and not by sampling:

     * [stage] is the proven round rule at the count the value gives, it is
       monotone and strictly increasing, and it never lowers a value;
     * [run] is additive in its stage count, monotone in both arguments, and
       never lowers a value;
     * [lvl] never lowers a value, is monotone in the value, and strictly
       grows from one rung to the next at the previous rung's own output
       ([lvl_strict_rung]);
     * and the rung separation, which is the content of the whole construction:
       for every fixed number of eps_0 stages c, and every rung k and value v,
       [run c v] is at most [lvl (S k) (v + c)].  A fixed number of stages
       therefore never reaches the next rung -- the same statement Eps1.v proves
       for the diagonal one rung down.

   What is NOT here, and must not be read into it: a tape, a table, a step
   count, or any claim about f_eps_1.  This is the value-level specification the
   table has to meet, in the same spirit as Eps1.v; the tape-level proof -- that
   the copy preserves the frame, which is the part that is actually hard -- is
   not in this file.  See EPS1_35_STATES.md. *)

From Stdlib Require Import Arith Lia.
From Top Require Import Tower Eps1.

Open Scope nat_scope.

(** ** One stage of the eps_0 engine *)

Definition stage (v : nat) : nat := 2 ^ (S v) - 1.

(** The count in a stage is the value's, and the block starts from one seed:
    this is [rounds] at count [S v] and value 0. *)

Lemma stage_is_rounds : forall v, stage v = rounds (S v) 0.
Proof.
  intros v. unfold stage.
  assert (H := rounds_closed (S v) 0).
  rewrite Nat.add_0_l in H. rewrite Nat.mul_1_l in H.
  lia.
Qed.

Lemma pow2_ge_succ : forall v, v + 1 <= 2 ^ (S v).
Proof.
  induction v as [| v IH].
  - simpl. lia.
  - rewrite pow2_succ. lia.
Qed.

Lemma pow2_ge_succ2 : forall v, v + 2 <= 2 ^ (S v).
Proof.
  induction v as [| v IH].
  - simpl. lia.
  - assert (H2 : 2 ^ (S (S v)) = 2 * 2 ^ (S v)) by reflexivity.
    lia.
Qed.

Lemma pow2_pos : forall v, 0 < 2 ^ v.
Proof.
  induction v as [| v IH]; simpl; lia.
Qed.

Lemma stage_gt : forall v, 1 <= v -> v < stage v.
Proof.
  intros v H. unfold stage.
  assert (H2 : v + 2 <= 2 ^ (S v)) by apply pow2_ge_succ2.
  lia.
Qed.

Lemma stage_ge : forall v, v <= stage v.
Proof.
  intros v. unfold stage.
  assert (H := pow2_ge_succ v). lia.
Qed.

Lemma stage_mono : forall v v', v <= v' -> stage v <= stage v'.
Proof.
  intros v v' H. rewrite stage_is_rounds. rewrite stage_is_rounds.
  apply (rounds_mono_c (S v) (S v') 0). lia.
Qed.

Lemma stage_strict : forall v, stage v < stage (S v).
Proof.
  intros v. unfold stage.
  assert (Hpos : 0 < 2 ^ v) by apply pow2_pos.
  assert (H1 : 2 ^ (S v) = 2 * 2 ^ v) by apply pow2_succ.
  assert (H2 : 2 ^ (S (S v)) = 2 * 2 ^ (S v)) by apply pow2_succ.
  lia.
Qed.

(** ** n stages *)

Fixpoint run (n v : nat) : nat :=
  match n with
  | 0 => v
  | S n' => run n' (stage v)
  end.

Lemma run_ge : forall n v, v <= run n v.
Proof.
  induction n as [| n IH]; intros v.
  - simpl. lia.
  - simpl. apply Nat.le_trans with (stage v).
    + apply stage_ge.
    + apply IH.
Qed.

Lemma run_mono_v : forall n v v', v <= v' -> run n v <= run n v'.
Proof.
  induction n as [| n IH]; intros v v' H.
  - simpl. exact H.
  - simpl. apply IH. apply stage_mono. exact H.
Qed.

(** The stage count can always be raised: one more stage only adds value. *)

Lemma run_le_succ : forall n v, run n v <= run (S n) v.
Proof.
  intros n v. simpl. apply run_mono_v. apply stage_ge.
Qed.

Lemma run_mono_n : forall n n' v, n <= n' -> run n v <= run n' v.
Proof.
  intros n n' v H. induction H as [| n' H IH].
  - lia.
  - apply Nat.le_trans with (run n' v).
    + exact IH.
    + apply run_le_succ.
Qed.

(** Running the stages in sequence is the same as one longer run: this is what
    makes "the count the previous rung produced" well defined. *)

Lemma run_succ_alt : forall n v, run (S n) v = stage (run n v).
Proof.
  induction n as [| n IH]; intros v.
  - simpl. reflexivity.
  - change (run (S n) (stage v) = stage (run (S n) v)).
    rewrite (IH (stage v)). reflexivity.
Qed.

Lemma run_compose : forall m n v, run m (run n v) = run (m + n) v.
Proof.
  induction m as [| m IH]; intros n v.
  - simpl. reflexivity.
  - change (run m (stage (run n v)) = run (m + n) (stage v)).
    rewrite <- run_succ_alt.
    change (run m (run (S n) v) = run (S (m + n)) v).
    replace (S (m + n)) with (m + S n) by lia.
    exact (IH (S n) v).
Qed.

(** ** The rungs *)

Fixpoint lvl (k v : nat) : nat :=
  match k with
  | 0 => v
  | S k' => run (lvl k' v) v
  end.

Lemma lvl_ge : forall k v, v <= lvl k v.
Proof.
  induction k as [| k IH]; intros v.
  - simpl. lia.
  - simpl. apply run_ge.
Qed.

Lemma lvl_mono_v : forall k v v', v <= v' -> lvl k v <= lvl k v'.
Proof.
  induction k as [| k IH]; intros v v' H.
  - simpl. exact H.
  - simpl. apply Nat.le_trans with (run (lvl k v') v).
    + apply (run_mono_n (lvl k v) (lvl k v') v). apply IH. exact H.
    + apply (run_mono_v (lvl k v') v v'). exact H.
Qed.

(** One rung up, at the previous rung's own output, is strictly above it.  This
    is the step the outer loop takes: it spends one rung and hands over the
    number it produced. *)

Lemma lvl_strict_rung : forall k v, 1 <= v -> lvl k v < lvl (S k) (lvl k v).
Proof.
  intros k v Hv.
  set (w := lvl k v).
  assert (Hw : 1 <= w).
  { unfold w. apply Nat.le_trans with v. exact Hv. apply lvl_ge. }
  assert (Hn : 1 <= lvl k w).
  { apply Nat.le_trans with w. exact Hw. apply lvl_ge. }
  change (w < run (lvl k w) w).
  apply Nat.le_trans with (run 1 w).
  - change (w < stage w). apply stage_gt. exact Hw.
  - apply (run_mono_n 1 (lvl k w) w). exact Hn.
Qed.

(** ** Rungs are separated *)

(** A fixed number of eps_0 stages never reaches the next rung: whatever c is
    handed in, the rung above is at least [run c] at an argument a little above
    v.  No fixed stage count can be a machine at the next level, which is the
    same gap Eps1.v proves one rung down. *)

Theorem lvl_beats_fixed : forall c k v, run c v <= lvl (S k) (v + c).
Proof.
  intros c k v.
  change (run c v <= run (lvl k (v + c)) (v + c)).
  apply Nat.le_trans with (run c (v + c)).
  - apply (run_mono_v c v (v + c)). lia.
  - apply (run_mono_n c (lvl k (v + c)) (v + c)).
    apply Nat.le_trans with (v + c). lia. apply lvl_ge.
Qed.

(** The machine's own frame check, stated at the value level: the numbers that
    tools/eps1_machine.py measures at the copy entry are [run] of the seed. *)

Theorem frame_stage_1 : run 1 1 = 3.
Proof. reflexivity. Qed.

Theorem frame_stage_2 : run 2 1 = 15.
Proof. reflexivity. Qed.

Theorem frame_stage_2_of_2 : run 2 2 = 255.
Proof. reflexivity. Qed.

Print Assumptions stage_is_rounds.
Print Assumptions pow2_ge_succ.
Print Assumptions pow2_ge_succ2.
Print Assumptions pow2_pos.
Print Assumptions stage_gt.
Print Assumptions stage_ge.
Print Assumptions stage_mono.
Print Assumptions stage_strict.
Print Assumptions run_ge.
Print Assumptions run_mono_v.
Print Assumptions run_mono_n.
Print Assumptions run_succ_alt.
Print Assumptions run_compose.
Print Assumptions lvl_ge.
Print Assumptions lvl_mono_v.
Print Assumptions lvl_strict_rung.
Print Assumptions lvl_beats_fixed.
