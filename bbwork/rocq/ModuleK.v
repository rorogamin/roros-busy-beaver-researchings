(** * ModuleK: the append engine of our eps-machine

    `tools/eps_machine.py` checks the seven-state module K on the concrete
    inputs x = 1..6 by simulation:

      1^x 0 1   (head on the source's last mark, state K1)
      -->       0^x 0 1^(2x+1)   (source consumed, destination grows by two
                                 per source mark)

    This file proves the walks the round is built from, for every length:
    crossing the gap, running the destination to its right end and appending,
    walking back over the destination, and walking back over the gap to erase
    a source mark.  Each statement is about the literal table [ktbl].

    What is proved here, as runs and not as steps: one mark's cycle of module
    K, [ki (S (S s)) G d --> ki (S s) (S G) (d + 2)] at the exact cost
    [2*G + 2*d + 9] (measured from the composed phases; the [2*g + 2*d + 7]
    that tools/kcheck.py reports is the same number in that file's indices,
    where the source is [s] marks and the destination [d] rather than [S s] and
    [S d]), the iteration of that cycle over
    a whole source block at [cycles_cost], and the halt that ends the block.
    What is NOT here: the drive's own loop around module K, and any step count
    for the eps_0 rung.  Nothing is assumed: the file contains no unfinished
    goal and no axiom.

    Two ordering facts the Python module paid for: the destination must be
    seeded, or "skip the blanks to the destination" has no stopping point;
    and a round must append before it erases, or the last source mark is
    destroyed uncopied and every answer comes out 2x-1. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM.
Import ListNotations.

(** ** States *)

Definition K1 : nat := 0.
Definition K2 : nat := 1.
Definition K3 : nat := 2.
Definition K4 : nat := 3.
Definition K5 : nat := 4.
Definition K6 : nat := 5.
Definition K7 : nat := 6.

(** ** The literal table, transcribed from tools/eps_machine.py *)

Definition ktbl : table := fun s b =>
  match s, b with
  | 0, on => Some (on, true, 1)
  | 1, bl => Some (bl, true, 1)
  | 1, on => Some (on, true, 2)
  | 2, bl => Some (on, true, 3)
  | 2, on => Some (on, true, 2)
  | 3, bl => Some (on, false, 4)
  | 4, bl => Some (bl, false, 5)
  | 4, on => Some (on, false, 4)
  | 5, bl => Some (bl, false, 5)
  | 5, on => Some (bl, false, 6)
  | 6, on => Some (on, true, 1)
  | _, _ => None
  end.

(** ** Block arithmetic *)

Lemma ones_succ : forall n L, ones n ++ on :: L = ones (S n) ++ L.
Proof.
  intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - change (on :: (ones n ++ on :: L) = on :: (ones (S n) ++ L)).
    rewrite IH. reflexivity.
Qed.

Lemma zeros_succ : forall n L, zeros n ++ bl :: L = zeros (S n) ++ L.
Proof.
  intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - change (bl :: (zeros n ++ bl :: L) = bl :: (zeros (S n) ++ L)).
    rewrite IH. reflexivity.
Qed.

Lemma hd_ones : forall n R, hd bl (ones (S n) ++ R) = on.
Proof. intros. change (hd bl (on :: (ones n ++ R)) = on). reflexivity. Qed.

Lemma tl_ones : forall n R, tl (ones (S n) ++ R) = ones n ++ R.
Proof. intros. change (tl (on :: (ones n ++ R)) = ones n ++ R). reflexivity. Qed.

Lemma hd_ones_nil : forall n, hd bl (ones (S n)) = on.
Proof. reflexivity. Qed.

Lemma tl_ones_nil : forall n, tl (ones (S n)) = ones n.
Proof. reflexivity. Qed.

Lemma hd_zeros : forall n R, hd bl (zeros (S n) ++ R) = bl.
Proof. intros. change (hd bl (bl :: (zeros n ++ R)) = bl). reflexivity. Qed.

Lemma tl_zeros : forall n R, tl (zeros (S n) ++ R) = zeros n ++ R.
Proof. intros. change (tl (bl :: (zeros n ++ R)) = zeros n ++ R). reflexivity. Qed.

(** ** One-step lemmas, straight from the table *)

Lemma st_K1_on : forall L R,
  step ktbl (mkConf K1 L on R) =
  Some (mkConf K2 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_K2_bl : forall L R,
  step ktbl (mkConf K2 L bl R) =
  Some (mkConf K2 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_K2_on : forall L R,
  step ktbl (mkConf K2 L on R) =
  Some (mkConf K3 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_K3_on : forall L R,
  step ktbl (mkConf K3 L on R) =
  Some (mkConf K3 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_K3_bl : forall L R,
  step ktbl (mkConf K3 L bl R) =
  Some (mkConf K4 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_K4_bl : forall L R,
  step ktbl (mkConf K4 L bl R) =
  Some (mkConf K5 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_K5_on : forall L R,
  step ktbl (mkConf K5 L on R) =
  Some (mkConf K5 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_K5_bl : forall L R,
  step ktbl (mkConf K5 L bl R) =
  Some (mkConf K6 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_K6_bl : forall L R,
  step ktbl (mkConf K6 L bl R) =
  Some (mkConf K6 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_K6_on : forall L R,
  step ktbl (mkConf K6 L on R) =
  Some (mkConf K7 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_K7_on : forall L R,
  step ktbl (mkConf K7 L on R) =
  Some (mkConf K2 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

(** [run_cat]: two runs concatenate. *)

Lemma run_cat : forall (k1 k2 : nat) (c1 c2 c3 : conf),
  run ktbl k1 c1 = Some c2 ->
  run ktbl k2 c2 = Some c3 ->
  run ktbl (k1 + k2) c1 = Some c3.
Proof.
  intros k1 k2 c1 c2 c3 H1 H2.
  rewrite run_add, H1. cbn. exact H2.
Qed.

(** ** Walk lemmas *)

(** Crossing the gap: [g] blanks, then the destination's first mark. *)

Lemma walk_gap : forall g L d,
  run ktbl (S g) (mkConf K2 L bl (zeros g ++ ones (S d))) =
  Some (mkConf K2 (zeros (S g) ++ L) on (ones d)).
Proof.
  induction g as [|g IH]; intros L d.
  - reflexivity.
  - change (run ktbl (S (S g))
            (mkConf K2 L bl (zeros (S g) ++ ones (S d))) =
          Some (mkConf K2 (zeros (S (S g)) ++ L) on (ones d))).
    rewrite run_S, st_K2_bl.
    rewrite tl_zeros, hd_zeros.
    rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.

(** The K3 sweep: [d] marks to the right of the head, then the blank beyond
    them.  Every step is K3's, so the state does not change. *)

Lemma walk_k3_on : forall d L,
  run ktbl (S d) (mkConf K3 L on (ones d)) =
  Some (mkConf K3 (ones (S d) ++ L) bl []).
Proof.
  induction d as [|d IH]; intros L.
  - reflexivity.
  - change (run ktbl (S (S d)) (mkConf K3 L on (ones (S d))) =
            Some (mkConf K3 (ones (S (S d)) ++ L) bl [])).
    rewrite run_S, st_K3_on.
    rewrite hd_ones_nil, tl_ones_nil.
    rewrite IH. rewrite ones_succ. reflexivity.
Qed.

(** The destination sweep, proved below.  From K3 with the head on a mark and
    [d] further marks to its right, the sweep rebuilds the block -- the head's
    own mark is written by the first step -- and appends one more, stopping in
    K4.  Cost [d + 2] steps, and the block grows by [d + 2] marks: one step and
    one mark per cell crossed, plus the appended mark.  This is the append
    phase of the round; `tools/kcheck.py`s `rounds` test exercises the same
    walk, and the count here matches its cost. *)

(** Back over the destination: [n] marks, stopping on the blank with the marks
    pushed to the right. *)

Lemma walk_k5 : forall n L X,
  run ktbl (S n) (mkConf K5 (ones n ++ bl :: L) on X) =
  Some (mkConf K5 L bl (ones (S n) ++ X)).
Proof.
  induction n as [|n IH]; intros L X.
  - reflexivity.
  - change (run ktbl (S (S n)) (mkConf K5 (ones (S n) ++ bl :: L) on X) =
            Some (mkConf K5 L bl (ones (S (S n)) ++ X))).
    rewrite run_S, st_K5_on.
    rewrite hd_ones, tl_ones.
    rewrite IH. rewrite ones_succ. reflexivity.
Qed.

(** ** The gap-and-erase walk, with its cost *)

(** Walking left over [g] gap blanks costs [g] steps; the head ends on the
    last blank of the gap with the blanks pushed onto the right list. *)

Lemma walk_k6_zeros : forall g L R,
  run ktbl g (mkConf K6 (zeros g ++ L) bl R) =
  Some (mkConf K6 L bl (zeros g ++ R)).
Proof.
  induction g as [|g IH]; intros L R.
  - reflexivity.
  - change (run ktbl (S g) (mkConf K6 (zeros (S g) ++ L) bl R) =
            Some (mkConf K6 L bl (zeros (S g) ++ R))).
    rewrite run_S, st_K6_bl.
    rewrite hd_zeros, tl_zeros.
    rewrite IH.
    rewrite <- zeros_succ.
    reflexivity.
Qed.

(** Crossing the gap and erasing the source's last mark costs [g + 2] steps:
    one per gap blank, one to step onto the source's last mark, one to erase
    it.  The result is K7 on the cell left of the erased mark -- another
    source mark, or a blank, which is exactly the halt test. *)

Lemma walk_k6_erase : forall g s R,
  run ktbl (g + 2) (mkConf K6 (zeros g ++ ones (S s)) bl R) =
  Some (mkConf K7 (tl (ones s)) (hd bl (ones s))
                  (bl :: bl :: zeros g ++ R)).
Proof.
  induction g as [|g IH]; intros s R.
  - reflexivity.
  - change (run ktbl (S (g + 2)) (mkConf K6 (zeros (S g) ++ ones (S s)) bl R) =
            Some (mkConf K7 (tl (ones s)) (hd bl (ones s))
                            (bl :: bl :: zeros (S g) ++ R))).
    rewrite run_S, st_K6_bl.
    rewrite hd_zeros, tl_zeros.
    rewrite IH.
    rewrite <- zeros_succ.
    reflexivity.
Qed.



Print Assumptions walk_k6_zeros.
Print Assumptions walk_k6_erase.

(** ** The destination sweep, with its cost *)

Lemma sweep_append : forall d L,
  run ktbl (d + 2) (mkConf K3 L on (ones d)) =
  Some (mkConf K4 (ones (d + 2) ++ L) bl []).
Proof.
  induction d as [|d IH]; intros L.
  - reflexivity.
  - change (run ktbl (S (d + 2)) (mkConf K3 L on (ones (S d))) =
            Some (mkConf K4 (ones (S (d + 2)) ++ L) bl [])).
    rewrite run_S, st_K3_on.
    rewrite hd_ones_nil, tl_ones_nil.
    rewrite IH.
    rewrite ones_succ.
    reflexivity.
Qed.

Print Assumptions sweep_append.

(** ** Composed phases *)

(** The append phase as one run: K2's step onto the destination's first mark,
    then the sweep.  Cost [d + 2] for every [d], the [d = 0] case being the
    head on the only destination mark with the single append step left. *)

Lemma append_phase : forall d L,
  run ktbl (d + 2) (mkConf K2 L on (ones d)) =
  Some (mkConf K4 (ones (d + 2) ++ L) bl []).
Proof.
  induction d as [|d IH]; intros L.
  - reflexivity.
  - change (run ktbl (S (d + 2)) (mkConf K2 L on (ones (S d))) =
            Some (mkConf K4 (ones (S d + 2) ++ L) bl [])).
    rewrite run_S, st_K2_on.
    rewrite hd_ones_nil, tl_ones_nil.
    rewrite sweep_append.
    rewrite ones_succ.
    reflexivity.
Qed.

(** The turn: K4's second append step, then the walk back over the rebuilt
    block, leaving K5 on the blank to its left.  Cost [n + 2]. *)

Lemma turn_phase : forall n L X,
  run ktbl (S (S n)) (mkConf K4 (ones (S n) ++ bl :: L) bl X) =
  Some (mkConf K5 L bl (ones (S n) ++ on :: X)).
Proof.
  intros n L X.
  rewrite run_S, st_K4_bl.
  rewrite hd_ones, tl_ones.
  rewrite walk_k5.
  reflexivity.
Qed.

Print Assumptions append_phase.
Print Assumptions turn_phase.

(** ** One mark's cycle of module K *)

(** A one-step run, so that single steps splice with the walk lemmas through
    [run_cat]. *)

Lemma run_1 : forall c c', step ktbl c = Some c' -> run ktbl 1 c = Some c'.
Proof. intros c c' H. cbn. rewrite H. reflexivity. Qed.

(** The gap-and-erase walk with a left context, in the arity the cycle needs:
    the head is on a blank with [g] blanks beyond it and then at least two
    marks of the source.  The source need not be the whole left list, which is
    what the assembly below requires.  Cost [g + 2]. *)

Lemma walk_k6_erase_ctx : forall g s L R,
  run ktbl (g + 2) (mkConf K6 (zeros g ++ ones (S (S s)) ++ L) bl R) =
  Some (mkConf K7 (ones s ++ L) on (bl :: bl :: zeros g ++ R)).
Proof.
  induction g as [|g IH]; intros s L R.
  - reflexivity.
  - change (run ktbl (S (g + 2))
              (mkConf K6 (zeros (S g) ++ ones (S (S s)) ++ L) bl R) =
            Some (mkConf K7 (ones s ++ L) on
                            (bl :: bl :: zeros (S g) ++ R))).
    rewrite run_S, st_K6_bl.
    rewrite hd_zeros, tl_zeros.
    rewrite IH.
    rewrite <- zeros_succ.
    reflexivity.
Qed.

(** ** The two composed phases *)

(** Walking the gap and taking the append as one run.  Cost [S G + (d + 2)]. *)

Lemma phase_A : forall G d L,
  run ktbl (S G + (d + 2)) (mkConf K2 L bl (zeros G ++ ones (S d))) =
  Some (mkConf K4 (ones (S (d + 1)) ++ zeros (S G) ++ L) bl []).
Proof.
  intros G d L.
  replace (S (d + 1)) with (d + 2) by nia.
  eapply run_cat.
  - apply walk_gap.
  - apply append_phase.
Qed.

(** Plus the turn back over the rebuilt destination: one run, cost
    [(S G + (d + 2)) + S (S (d + 1))], ending in K5 on the blank that
    separates the destination from the gap. *)

Lemma phase_AB : forall G d L,
  run ktbl ((S G + (d + 2)) + S (S (d + 1)))
    (mkConf K2 L bl (zeros G ++ ones (S d))) =
  Some (mkConf K5 (zeros G ++ L) bl (ones (S (d + 1)) ++ on :: [])).
Proof.
  intros G d L.
  eapply run_cat.
  - apply phase_A.
  - apply turn_phase.
Qed.

(** ** The cycle *)

(** Crossing a nonempty gap: [S G] blanks from the head, then the destination.
    The tape in front of the head is rebuilt with [G] blanks instead of [S G]
    -- the erased source mark showing up as blank tape. *)

Lemma cycle_pos_raw : forall s G d L,
  run ktbl (((S (S G) + (d + 2)) + S (S (d + 1))) + (1 + ((G + 2) + 1)))
    (mkConf K2 (ones (S (S s)) ++ L) bl (zeros (S G) ++ ones (S d))) =
  Some (mkConf K2 (ones (S s) ++ L) bl
                  (bl :: zeros G ++ bl :: ones (S (d + 1)) ++ on :: [])).
Proof.
  intros s G d L.
  eapply run_cat.
  - apply phase_AB.
  - eapply run_cat.
    + eapply run_1. apply st_K5_bl.
    + eapply run_cat.
      * apply walk_k6_erase_ctx.
      * eapply run_1. apply st_K7_on.
Qed.

(** The [G = 0] case: the head's blank is the only gap, so the turn lands it on
    the source's last mark and the erase is a single step. *)

Lemma cycle_zero_raw : forall s d L,
  run ktbl (((S 0 + (d + 2)) + S (S (d + 1))) + (1 + (1 + 1)))
    (mkConf K2 (ones (S (S s)) ++ L) bl (ones (S d))) =
  Some (mkConf K2 (ones (S s) ++ L) bl
                  (bl :: ones (S (d + 1)) ++ on :: [])).
Proof.
  intros s d L.
  eapply run_cat.
  - apply phase_AB.
  - eapply run_cat.
    + eapply run_1. apply st_K5_bl.
    + eapply run_cat.
      * eapply run_1. apply st_K6_on.
      * eapply run_1. apply st_K7_on.
Qed.

(** The two right ends, put back into the canonical shape [zeros (S G) ++
    destination]. *)

Lemma shape_pos : forall G d,
  bl :: zeros G ++ bl :: ones (S (d + 1)) ++ on :: []
  = zeros (S (S G)) ++ ones (S (S (S d))).
Proof.
  intros G d.
  rewrite ones_succ. rewrite app_nil_r.
  rewrite zeros_succ.
  replace (S (S (d + 1))) with (S (S (S d))) by nia.
  reflexivity.
Qed.

Lemma shape_zero : forall d,
  bl :: ones (S (d + 1)) ++ on :: []
  = zeros (S 0) ++ ones (S (S (S d))).
Proof.
  intros d.
  rewrite ones_succ. rewrite app_nil_r.
  replace (S (S (d + 1))) with (S (S (S d))) by nia.
  reflexivity.
Qed.

(** ** The cycle as one theorem, at cost [2*G + 2*d + 9] *)

Lemma mark_cycle : forall s G d L,
  run ktbl (2 * G + 2 * d + 9)
    (mkConf K2 (ones (S (S s)) ++ L) bl (zeros G ++ ones (S d))) =
  Some (mkConf K2 (ones (S s) ++ L) bl
                  (zeros (S G) ++ ones (S (S (S d))))).
Proof.
  intros s G d L.
  destruct G as [|G].
  - replace (2 * 0 + 2 * d + 9)
      with (((S 0 + (d + 2)) + S (S (d + 1))) + (1 + (1 + 1))) by nia.
    rewrite cycle_zero_raw, shape_zero. reflexivity.
  - replace (2 * S G + 2 * d + 9)
      with (((S (S G) + (d + 2)) + S (S (d + 1))) + (1 + ((G + 2) + 1))) by nia.
    rewrite cycle_pos_raw, shape_pos. reflexivity.
Qed.

(** ** Iterating the cycle over a source block *)

(** The cost of [n] cycles, defined by the same recursion the run follows: one
    cycle costs [2*G + 2*d + 9], and each cycle grows the gap by one and the
    destination by two, so the next cycle is dearer. *)

Fixpoint cycles (n G d : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => (2*G + 2*d + 9) + cycles n' (S G) (d + 2)
  end.

(** Closed form: [2*n*G + 2*n*d + 3*n*n + 6*n].  The [3*n*n + 6*n] is the sum of
    that growth -- not [2*n*n + 7*n], which is what a first guess gave before
    the destination was known to grow by two per cycle. *)

Lemma cycles_closed : forall n G d,
  cycles n G d = 2*n*G + 2*n*d + 3*n*n + 6*n.
Proof.
  induction n as [|n IH]; intros G d.
  - reflexivity.
  - cbn [cycles]. rewrite IH. nia.
Qed.

(** [n] cycles eat [n] source marks: from [n + 3] marks they leave [3], and the
    gap and destination grow as they go.  The count is kept in front, so every
    intermediate configuration is syntactically one of the cycle's own shapes. *)

Lemma cycles_run : forall n G d L,
  run ktbl (cycles n G d)
    (mkConf K2 (ones (S (S (S n))) ++ L) bl (zeros G ++ ones (S d))) =
  Some (mkConf K2 (ones 3 ++ L) bl
                  (zeros (G + n) ++ ones (S (d + 2 * n)))).
Proof.
  induction n as [|n IH]; intros G d L.
  - cbn. repeat rewrite Nat.add_0_r. reflexivity.
  - cbn [cycles].
    replace (d + 2) with (S (S d)) by nia.
    eapply run_cat.
    + apply mark_cycle.
    + replace (G + S n) with (S G + n) by nia.
      replace (S (d + 2 * S n)) with (S (S (S d) + 2 * n)) by nia.
      apply IH.
Qed.

(** ** The halt *)

(** The last source mark: the erase leaves K7 on a blank, and K7 has no row for
    a blank -- which is the halt test, not a walk. *)

Lemma walk_k6_last : forall g R,
  run ktbl (g + 2) (mkConf K6 (zeros g ++ ones 1) bl R) =
  Some (mkConf K7 [] bl (bl :: bl :: zeros g ++ R)).
Proof.
  intros g R.
  change (run ktbl (g + (1 + 1))
            (mkConf K6 (zeros g ++ ones 1) bl R) =
          Some (mkConf K7 [] bl (bl :: bl :: zeros g ++ R))).
  eapply run_cat.
  - apply walk_k6_zeros.
  - eapply run_cat.
    + eapply run_1. apply st_K6_bl.
    + eapply run_1. apply st_K6_on.
Qed.

Lemma k_halt_step : forall g R,
  step ktbl (mkConf K7 [] bl (bl :: bl :: zeros g ++ R)) = None.
Proof. reflexivity. Qed.

(** So the module does not merely stop being simulated -- the run itself is
    [None] one step later. *)

Lemma module_k_halt : forall g R,
  run ktbl (g + 3) (mkConf K6 (zeros g ++ ones 1) bl R) = None.
Proof.
  intros g R.
  replace (g + 3) with ((g + 2) + 1) by nia.
  rewrite run_add, walk_k6_last.
  cbn. reflexivity.
Qed.

Print Assumptions run_1.
Print Assumptions walk_k6_erase_ctx.
Print Assumptions phase_A.
Print Assumptions phase_AB.
Print Assumptions cycle_pos_raw.
Print Assumptions cycle_zero_raw.
Print Assumptions shape_pos.
Print Assumptions shape_zero.
Print Assumptions mark_cycle.
Print Assumptions cycles_closed.
Print Assumptions cycles_run.
Print Assumptions walk_k6_last.
Print Assumptions k_halt_step.
Print Assumptions module_k_halt.

(** ** A whole source block: the halted case *)

(** When one source mark is left, the cycle still has to copy it twice, and then
    the erase walk steps onto a blank -- so the phase ends in K7 on blank tape
    and the next step is the halt.  Two costs, because with no gap the turn
    lands the head on the last mark and the erase is one step instead of a walk
    over [G] blanks. *)

Definition last_cost (G d : nat) : nat :=
  match G with
  | 0 => 1 + (d + 2) + S (S (d + 1)) + (1 + (1 + 1))
  | S G' => S (S G') + (d + 2) + S (S (d + 1)) + (1 + (G' + (1 + (1 + 1))))
  end.

(** The run up to K7 on a blank, no gap. *)

Lemma last_k7_zero : forall d j L,
  run ktbl (((S 0 + (d + 2)) + S (S (d + 1))) + (1 + 1))
    (mkConf K2 (ones 1 ++ zeros (S j) ++ L) bl (ones (S d))) =
  Some (mkConf K7 (zeros j ++ L) bl
                  (bl :: bl :: ones (S (d + 1)) ++ on :: [])).
Proof.
  intros d j L.
  eapply run_cat.
  - apply phase_AB.
  - eapply run_cat.
    + eapply run_1. apply st_K5_bl.
    + eapply run_1. apply st_K6_on.
Qed.

(** The same with a gap of at least one: the erase becomes a walk. *)

Lemma last_k7_pos : forall G d j L,
  run ktbl (((S (S G) + (d + 2)) + S (S (d + 1))) + (1 + (G + (1 + 1))))
    (mkConf K2 (ones 1 ++ zeros (S j) ++ L) bl (zeros (S G) ++ ones (S d))) =
  Some (mkConf K7 (zeros j ++ L) bl
                  (bl :: bl :: zeros G ++ bl :: ones (S (d + 1)) ++ on :: [])).
Proof.
  intros G d j L.
  eapply run_cat.
  - apply phase_AB.
  - eapply run_cat.
    + eapply run_1. apply st_K5_bl.
    + eapply run_cat.
      * apply walk_k6_zeros.
      * eapply run_cat.
        -- eapply run_1. apply st_K6_bl.
        -- eapply run_1. apply st_K6_on.
Qed.

(** And the halt one step later: [step] of a K7 configuration whose head is on
    a blank. *)

Lemma last_halt_zero : forall d j L,
  run ktbl (last_cost 0 d)
    (mkConf K2 (ones 1 ++ zeros (S j) ++ L) bl (ones (S d))) = None.
Proof.
  intros d j L.
  replace (last_cost 0 d)
    with ((((S 0 + (d + 2)) + S (S (d + 1))) + (1 + 1)) + 1) by (cbn; lia).
  rewrite run_add, last_k7_zero.
  cbn. reflexivity.
Qed.

Lemma last_halt_pos : forall G d j L,
  run ktbl (last_cost (S G) d)
    (mkConf K2 (ones 1 ++ zeros (S j) ++ L) bl (zeros (S G) ++ ones (S d))) = None.
Proof.
  intros G d j L.
  replace (last_cost (S G) d)
    with ((((S (S G) + (d + 2)) + S (S (d + 1))) + (1 + (G + (1 + 1)))) + 1)
    by (cbn; lia).
  rewrite run_add, last_k7_pos.
  cbn. reflexivity.
Qed.

(** ** The block theorem *)

(** The cost of consuming [x] source marks, by the same recursion the run
    follows: one cycle per mark, then the last-mark phase. *)

Fixpoint k_cost (x G d : nat) : nat :=
  match x with
  | 0 => 0
  | S x' =>
      match x' with
      | 0 => last_cost G d
      | S _ => (2 * G + 2 * d + 9) + k_cost x' (S G) (d + 2)
      end
  end.

(** Module K on a source block of [x] marks runs out of tape: [x] copies at two
    destination marks each, then the halt.  The left context is a nonempty
    block of blanks ([zeros (S j)]), which is what the halt test looks at. *)

Theorem k_block : forall x G d j L,
  run ktbl (k_cost (S x) G d)
    (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl (zeros G ++ ones (S d))) = None.
Proof.
  induction x as [|x IH]; intros G d j L.
  - destruct G as [|G'].
    + apply last_halt_zero.
    + apply last_halt_pos.
  - replace (k_cost (S (S x)) G d)
      with ((2 * G + 2 * d + 9) + k_cost (S x) (S G) (d + 2)) by (cbn; lia).
    replace (d + 2) with (S (S d)) by lia.
    rewrite run_add, mark_cycle.
    change (run ktbl (k_cost (S x) (S G) (S (S d)))
              (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl
                      (zeros (S G) ++ ones (S (S (S d))))) = None).
    apply IH.
Qed.

Print Assumptions last_k7_zero.
Print Assumptions last_k7_pos.
Print Assumptions last_halt_zero.
Print Assumptions last_halt_pos.
Print Assumptions k_block.

Lemma ones_snoc : forall n, ones n ++ on :: [] = ones (S n).
Proof. intros n. rewrite ones_succ. rewrite app_nil_r. reflexivity. Qed.

(** ** The block one step short of the halt

    The drive around module K does not stop where the module does: its K7 row
    continues into the return walk.  So the drive needs the block's run up to
    the K7-on-blank configuration, not the run to [None].  Same recursion as
    [k_cost], with the last phase one step short of the halt -- [last_pre] is
    that phase, the cost of [last_k7_zero] and [last_k7_pos] before the step
    that halts. *)

Definition last_pre (G d : nat) : nat :=
  match G with
  | 0 => ((S 0 + (d + 2)) + S (S (d + 1))) + (1 + 1)
  | S G' => ((S (S G') + (d + 2)) + S (S (d + 1))) + (1 + (G' + (1 + 1)))
  end.

Lemma last_cost_pos : forall G d, 0 < last_cost G d.
Proof. intros G d. destruct G as [|G']; cbn [last_cost]; lia. Qed.

Lemma last_pre_is : forall G d, last_pre G d = last_cost G d - 1.
Proof. intros G d. destruct G as [|G']; cbn [last_pre last_cost]; lia. Qed.

Fixpoint k_pre (x G d : nat) : nat :=
  match x with
  | 0 => 0
  | S x' =>
      match x' with
      | 0 => last_pre G d
      | S _ => (2 * G + 2 * d + 9) + k_pre x' (S G) (d + 2)
      end
  end.

Lemma k_pre_last : forall G d, k_pre 1 G d = last_pre G d.
Proof. intros. reflexivity. Qed.

Lemma k_pre_cycle : forall x G d,
  k_pre (S (S x)) G d = (2 * G + 2 * d + 9) + k_pre (S x) (S G) (d + 2).
Proof. intros. reflexivity. Qed.

(** ** The block's exit configuration

    One step before the halt the module is in K7 on a blank, with the source
    block gone and the destination holding [1 + 2x] marks for [S x] source
    marks.  The blank run in front of it is [G + x + 2] cells: the two the
    append leaves, the gap, and one per cycle. *)

Theorem k_pre_block : forall x G d j L,
  run ktbl (k_pre (S x) G d)
    (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl (zeros G ++ ones (S d))) =
  Some (mkConf K7 (zeros j ++ L) bl
                  (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x)))))).
Proof.
  induction x as [|x IH]; intros G d j L.
  - destruct G as [|G'].
    + cbn [k_pre last_pre].
      rewrite last_k7_zero.
      rewrite ones_snoc.
      replace (0 + 0 + 2) with 2 by lia.
      replace (S (S (d + 1))) with (S (S (S d))) by lia.
      replace (S (S (S (d + 2 * 0)))) with (S (S (S d))) by lia.
      reflexivity.
    + cbn [k_pre last_pre].
      rewrite last_k7_pos.
      rewrite ones_snoc.
      rewrite zeros_succ.
      replace (S (S (d + 1))) with (S (S (S d))) by lia.
      replace (S G' + 0 + 2) with (S (S (S G'))) by lia.
      replace (S (S (S (d + 2 * 0)))) with (S (S (S d))) by lia.
      reflexivity.
  - replace (k_pre (S (S x)) G d)
      with ((2 * G + 2 * d + 9) + k_pre (S x) (S G) (d + 2)) by reflexivity.
    rewrite run_add, mark_cycle.
    replace (d + 2) with (S (S d)) by lia.
    change (run ktbl (k_pre (S x) (S G) (S (S d)))
              (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl
                      (zeros (S G) ++ ones (S (S (S d))))) =
            Some (mkConf K7 (zeros j ++ L) bl
                            (zeros (G + S x + 2) ++ ones (S (S (S (d + 2 * S x))))))).
    rewrite (IH (S G) (S (S d)) j L).
    replace (S G + x + 2) with (G + S x + 2) by lia.
    replace (S (S d) + 2 * x) with (d + 2 * S x) by lia.
    reflexivity.
Qed.

Print Assumptions last_pre_is.
(** The pre-block cost is the block cost less the halt step: what the drive
    needs is the run that *stops* on the cell where the module would halt. *)

Lemma k_pre_is : forall x G d, k_cost (S x) G d = k_pre (S x) G d + 1.
Proof.
  intros x. induction x as [|x IH]; intros G d.
  - cbn [k_cost k_pre]. rewrite last_pre_is.
    pose proof (last_cost_pos G d). lia.
  - replace (k_cost (S (S x)) G d)
      with ((2 * G + 2 * d + 9) + k_cost (S x) (S G) (d + 2)) by (cbn; lia).
    replace (k_pre (S (S x)) G d)
      with ((2 * G + 2 * d + 9) + k_pre (S x) (S G) (d + 2)) by (cbn; lia).
    rewrite IH. lia.
Qed.

Print Assumptions k_pre_block.
Print Assumptions k_pre_is.

Print Assumptions walk_gap.
Print Assumptions walk_k3_on.
Print Assumptions walk_k5.
