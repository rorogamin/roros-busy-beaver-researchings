(** * Eps0Drive.v -- the eps0 machine's drive, and its loop around module K *)

(** The eps0 machine of [tools/eps0_machine.py] has 33 states.  It spends a
    whole block of marks (the "stage block") one mark at a time; every mark
    spent is one *stage*, and every stage runs the module-K block once.  This
    file proves that the drive around module K is exactly the module's block
    with its states shifted by 26, and that the shift is sound: the drive's
    rows for the module's states are the module's rows, target states shifted,
    with one exception only.

    The exception is the module's halting cell: the module stops when it has
    no row at (K7, blank), while the drive must *keep going* there -- it turns
    the head around and hands over to the return walk (state [A5]).

    Everything here is symbolic: no [vm_compute] and no simulation is used to
    establish a claim. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Top Require Import TM ModuleK.

(** ** The drive's states *)

(** Counter and drive *) 
Definition R0 : nat := 0.    (* wall walk, left *)
Definition R1 : nat := 1.    (* decide: mark spent -> erase, blank -> stage block *)
Definition R2 : nat := 2.    (* erase one counter mark *)
Definition R4 : nat := 3.    (* cross the hole run *)
Definition R5 : nat := 4.    (* cross the value *)
Definition R6 : nat := 5.    (* re-enter module K *)

(** Return walk, after module K *) 
Definition A5 : nat := 6.
Definition A6 : nat := 7.
Definition A7 : nat := 8.
Definition A8 : nat := 9.
Definition A9 : nat := 10.
Definition AA : nat := 11.   (* back to R1 *)

(** Fuel phase *)
Definition F0 : nat := 12.
Definition F1 : nat := 13.
Definition F2 : nat := 14.
Definition F3 : nat := 15.
Definition F4 : nat := 16.
Definition F5 : nat := 17.

(** Stage-block phase *)
Definition P0 : nat := 18.
Definition P1 : nat := 19.
Definition P2 : nat := 20.

(** Stage-block branch: spend the leftmost mark of the block *)
Definition S0 : nat := 21.
Definition S1 : nat := 22.
Definition S2 : nat := 23.
Definition S3 : nat := 24.
Definition S4 : nat := 25.

(** Module K, shifted by 26: state [K1 + 26] of the drive is the module's [K1] *)
Definition SH : nat := 26.

(** ** The drive table *)

Definition dtbl : table := fun s b =>
  match s, b with
  (* R0: walk left to the wall *)
  | 0, bl => Some (bl, false, 0)
  | 0, on => Some (on, false, 1)
  (* R1 *)
  | 1, on => Some (on, true, 2)
  | 1, bl => Some (bl, false, 21)
  (* R2: erase the last counter mark *)
  | 2, on => Some (bl, true, 3)
  (* R4: cross the hole run *)
  | 3, bl => Some (bl, true, 3)
  | 3, on => Some (on, true, 4)
  (* R5: cross the value *)
  | 4, on => Some (on, true, 4)
  | 4, bl => Some (bl, false, 5)
  (* R6: re-enter module K *)
  | 5, on => Some (on, true, 27)
  (* module K, shifted *)
  | 26, on => Some (on, true, 27)
  | 27, bl => Some (bl, true, 27)
  | 27, on => Some (on, true, 28)
  | 28, bl => Some (on, true, 29)
  | 28, on => Some (on, true, 28)
  | 29, bl => Some (on, false, 30)
  | 30, bl => Some (bl, false, 31)
  | 30, on => Some (on, false, 30)
  | 31, bl => Some (bl, false, 31)
  | 31, on => Some (bl, false, 32)
  | 32, on => Some (on, true, 27)
  | 32, bl => Some (bl, true, 6)
  (* A5: turn around, cross the new value's gap *)
  | 6, bl => Some (bl, true, 6)
  | 6, on => Some (on, true, 7)
  (* A6: cross the new value *)
  | 7, on => Some (on, true, 7)
  | 7, bl => Some (bl, true, 8)
  (* A7: write the new seed *)
  | 8, bl => Some (on, false, 9)
  (* A8 *)
  | 9, bl => Some (bl, false, 10)
  (* A9: walk back over the value *)
  | 10, on => Some (on, false, 10)
  | 10, bl => Some (bl, false, 11)
  (* AA: walk back over the holes, back to R1 *)
  | 11, bl => Some (bl, false, 11)
  | 11, on => Some (on, false, 1)
  (* fuel *)
  | 12, bl => Some (bl, true, 12)
  | 12, on => Some (bl, true, 13)
  | 13, on => Some (on, false, 14)
  | 13, bl => Some (bl, false, 15)
  | 14, bl => Some (bl, false, 14)
  | 14, on => Some (on, true, 16)
  | 15, bl => Some (bl, false, 15)
  | 15, on => Some (on, true, 17)
  | 16, bl => Some (on, true, 12)
  | 17, bl => Some (on, true, 18)
  (* stage block *)
  | 18, bl => Some (bl, true, 18)
  | 18, on => Some (on, false, 19)
  | 19, bl => Some (bl, false, 20)
  | 20, bl => Some (on, false, 0)
  (* stage branch: spend the block's leftmost mark *)
  | 21, on => Some (on, false, 21)
  | 21, bl => Some (bl, true, 22)
  | 22, on => Some (bl, true, 23)
  | 23, on => Some (on, true, 24)
  | 24, on => Some (on, true, 24)
  | 24, bl => Some (bl, true, 25)
  | 25, on => Some (on, true, 12)
  | _, _ => None
  end.

(** ** Running the drive *)

Lemma run_cat_d : forall (k1 k2 : nat) (c1 c2 c3 : conf),
  run dtbl k1 c1 = Some c2 ->
  run dtbl k2 c2 = Some c3 ->
  run dtbl (k1 + k2) c1 = Some c3.
Proof.
  intros k1 k2 c1 c2 c3 H1 H2.
  rewrite run_add, H1. cbn. exact H2.
Qed.

(** ** One-step facts *)

Lemma dR1_on : forall L R,
  step dtbl (mkConf R1 L on R) = Some (mkConf R2 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dR1_bl : forall L R,
  step dtbl (mkConf R1 L bl R) = Some (mkConf S0 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma dR2_on : forall L R,
  step dtbl (mkConf R2 L on R) = Some (mkConf R4 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dR4_bl : forall L R,
  step dtbl (mkConf R4 L bl R) = Some (mkConf R4 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dR4_on : forall L R,
  step dtbl (mkConf R4 L on R) = Some (mkConf R5 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dR5_on : forall L R,
  step dtbl (mkConf R5 L on R) = Some (mkConf R5 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dR5_bl : forall L R,
  step dtbl (mkConf R5 L bl R) = Some (mkConf R6 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma dR6_on : forall L R,
  step dtbl (mkConf R6 L on R) = Some (mkConf (SH + K2) (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dK7_bl : forall L R,
  step dtbl (mkConf (SH + K7) L bl R) = Some (mkConf A5 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dA5_bl : forall L R,
  step dtbl (mkConf A5 L bl R) = Some (mkConf A5 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dA5_on : forall L R,
  step dtbl (mkConf A5 L on R) = Some (mkConf A6 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dA6_on : forall L R,
  step dtbl (mkConf A6 L on R) = Some (mkConf A6 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dA6_bl : forall L R,
  step dtbl (mkConf A6 L bl R) = Some (mkConf A7 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma dA7_bl : forall L R,
  step dtbl (mkConf A7 L bl R) = Some (mkConf A8 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma dA8_bl : forall L R,
  step dtbl (mkConf A8 L bl R) = Some (mkConf A9 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma dA9_on : forall L R,
  step dtbl (mkConf A9 L on R) = Some (mkConf A9 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma dA9_bl : forall L R,
  step dtbl (mkConf A9 L bl R) = Some (mkConf AA (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma dAA_bl : forall L R,
  step dtbl (mkConf AA L bl R) = Some (mkConf AA (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma dAA_on : forall L R,
  step dtbl (mkConf AA L on R) = Some (mkConf R1 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

(** ** The splice: module K inside the drive *)

(** The drive's rows for the module's states are the module's rows with the
    target state shifted by 26.  The shift is recorded by [bump]. *)

Definition bump (o : option (sym * dirn * nat)) : option (sym * dirn * nat) :=
  match o with
  | None => None
  | Some (w, d, s) => Some (w, d, s + SH)
  end.

Lemma ktbl_none_ge : forall s b, 7 <= s -> ktbl s b = None.
Proof.
  intros s b H.
  destruct s as [|[|[|[|[|[|[|s']]]]]]]; try lia; reflexivity.
Qed.

(** The only row of the module that the drive changes is the halting one,
    [ktbl K7 bl = None], which the drive sends to [A5].  For every row the
    module can actually *take*, the drive agrees.  [row_K] records the
    agreement for states 0..5 (module [K1]..[K6]); the two [K7] rows are
    handled by [row_K7_on] and [row_K7_bl]. *)

Lemma row_K : forall s b, s <= 5 -> dtbl (SH + s) b = bump (ktbl s b).
Proof.
  intros s b H.
  destruct s as [|[|[|[|[|[|s']]]]]]; try (exfalso; lia).
  all: destruct b; cbn; reflexivity.
Qed.

Lemma row_K7_on : dtbl (SH + 6) on = bump (ktbl 6 on).
Proof. reflexivity. Qed.

Lemma row_K7_bl : dtbl (SH + K7) bl = Some (bl, true, A5).
Proof. reflexivity. Qed.

(** ** The renaming lemma *)

Definition ren (c : conf) : conf :=
  mkConf (SH + cst c) (clft c) (ccur c) (crgt c).

Lemma bump_Some : forall w d s,
  bump (Some (w, d, s)) = Some (w, d, s + SH).
Proof. reflexivity. Qed.

Lemma step_ren : forall c c',
  step ktbl c = Some c' -> step dtbl (ren c) = Some (ren c').
Proof.
  intros [s L b R] c' H.
  destruct s as [|[|[|[|[|[|[|s']]]]]]].
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - destruct b; cbn [step ktbl ren] in *; try discriminate H;
      injection H as <-; reflexivity.
  - cbn [ktbl] in H. discriminate H.
Qed.

(** A module run composed of steps is a drive run with the states shifted.
    No extra hypothesis is needed: a *running* module never sits on its
    halting cell, because the module has no row there, so the one place where
    the two tables disagree is never used. *)

Lemma run_ren : forall k c c',
  run ktbl k c = Some c' -> run dtbl k (ren c) = Some (ren c').
Proof.
  induction k as [|k IH]; intros c c' H.
  - cbn [run] in *. injection H as <-. cbn [run]. reflexivity.
  - cbn [run] in H.
    destruct (step ktbl c) as [c1|] eqn:E; [|discriminate H].
    rewrite run_S, (step_ren c c1 E). cbn. eapply IH. exact H.
Qed.

(** ** Module K runs inside the drive, at cost [k_pre] *)

Lemma k_block_ren : forall (x G d j : nat) (L : list sym),
  run dtbl (k_pre (S x) G d)
    (ren (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl
                  (zeros G ++ ones (S d)))) =
  Some (ren (mkConf K7 (zeros j ++ L) bl
                    (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x))))))).
Proof.
  intros. apply run_ren. apply k_pre_block.
Qed.

Lemma k_block_drive : forall (x G d j : nat) (L : list sym),
  run dtbl (k_pre (S x) G d)
    (mkConf (SH + K2) (ones (S x) ++ zeros (S j) ++ L) bl
            (zeros G ++ ones (S d))) =
  Some (mkConf (SH + K7) (zeros j ++ L) bl
               (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x)))))).
Proof.
  intros.
  change (run dtbl (k_pre (S x) G d)
            (ren (mkConf K2 (ones (S x) ++ zeros (S j) ++ L) bl
                          (zeros G ++ ones (S d)))) =
          Some (ren (mkConf K7 (zeros j ++ L) bl
                            (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x)))))))).
  apply k_block_ren.
Qed.

(** The exit of the block, in the drive's own states, with the handover step
    the module does not have: [K7] on a blank spends one step and turns the
    drive round into [A5], on the erased count. *)

Lemma k_block_drive_exit : forall (x G d j : nat) (L : list sym),
  run dtbl (k_pre (S x) G d + 1)
    (mkConf (SH + K2) (ones (S x) ++ zeros (S j) ++ L) bl
            (zeros G ++ ones (S d))) =
  Some (mkConf A5 (bl :: zeros j ++ L) (hd bl (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x))))))
            (tl (zeros (G + x + 2) ++ ones (S (S (S (d + 2 * x))))))).
Proof.
  intros.
  rewrite run_add, k_block_drive. cbn.
  cbn [run A5]. reflexivity.
Qed.

(** ** Checks *)

Print Assumptions run_cat_d.
Print Assumptions step_ren.
Print Assumptions run_ren.
Print Assumptions k_block_drive.
Print Assumptions k_block_drive_exit.

(** * Rounding: the drive's walk lemmas, proved for every [m] and [v]

    Every phase of one round of the counter engine is a walk: a run of blanks
    crossed, a run of marks consumed, a handover.  Each is proved here by
    induction on the length of the run, with a concrete instance beside it so
    that the evaluator arbitrates the shape.  [round_v0] assembles the whole
    round for a value of length one; the phase lemmas above it are parametric
    in [v], so the return side of the round is already proved for every value
    length.  *)

(** ** Crossing a run of blanks, then stepping onto the first mark *)

Lemma walk_bl_R4 : forall m A Y,
  run dtbl (m + 2) (mkConf R4 A bl (zeros m ++ on :: Y)) =
  Some (mkConf R5 (on :: zeros (m + 1) ++ A) (hd bl Y) (tl Y)).
Proof.
  intros m. induction m as [|m IH]; intros A Y.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S m + 2) with (S (m + 2)) by lia.
    rewrite run_S. cbn [zeros]. rewrite dR4_bl. cbn.
    rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.

Example walk_bl_R4_ex :
  run dtbl 4 (mkConf R4 [on] bl (zeros 2 ++ on :: [on; bl])) =
  Some (mkConf R5 (on :: zeros 3 ++ [on]) on [bl]).
Proof. reflexivity. Qed.

(** ** A single mark step at R4 *)

Lemma walk_hit_R4 : forall A Y,
  run dtbl 1 (mkConf R4 A on Y) =
  Some (mkConf R5 (on :: A) (hd bl Y) (tl Y)).
Proof. intros. cbn. reflexivity. Qed.

(** ** The same blank walk at A5 *)

Lemma walk_bl_A5 : forall m A Y,
  run dtbl (m + 2) (mkConf A5 A bl (zeros m ++ on :: Y)) =
  Some (mkConf A6 (on :: zeros (m + 1) ++ A) (hd bl Y) (tl Y)).
Proof.
  intros m. induction m as [|m IH]; intros A Y.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S m + 2) with (S (m + 2)) by lia.
    rewrite run_S. cbn [zeros]. rewrite dA5_bl. cbn.
    rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.

Example walk_bl_A5_ex :
  run dtbl 5 (mkConf A5 [bl] bl (zeros 3 ++ on :: [on; on])) =
  Some (mkConf A6 (on :: zeros 4 ++ [bl]) on [on]).
Proof. reflexivity. Qed.

(** ** Crossing marks at R5, then the blank step back *)

Lemma walk_on_R5 : forall k A X,
  run dtbl (k + 2) (mkConf R5 A on (ones k ++ bl :: X)) =
  Some (mkConf R6 (ones k ++ A) on (bl :: X)).
Proof.
  intros k. induction k as [|k IH]; intros A X.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S k + 2) with (S (k + 2)) by lia.
    rewrite run_S. cbn [ones]. rewrite dR5_on. cbn.
    rewrite IH. rewrite ones_succ. reflexivity.
Qed.

Example walk_on_R5_ex :
  run dtbl 3 (mkConf R5 [on] on (ones 1 ++ bl :: [on])) =
  Some (mkConf R6 (ones 1 ++ [on]) on [bl; on]).
Proof. reflexivity. Qed.

Lemma walk_bl_R5 : forall A X,
  run dtbl 1 (mkConf R5 A bl X) =
  Some (mkConf R6 (tl A) (hd bl A) (bl :: X)).
Proof. intros. cbn. reflexivity. Qed.

(** ** Crossing the whole value at A6, then the blank step *)

Lemma walk_on_A6 : forall k A,
  run dtbl (k + 2) (mkConf A6 A on (ones k)) =
  Some (mkConf A7 (bl :: ones (k + 1) ++ A) bl []).
Proof.
  intros k. induction k as [|k IH]; intros A.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S k + 2) with (S (k + 2)) by lia.
    rewrite run_S. cbn [ones]. rewrite dA6_on. cbn.
    rewrite IH. rewrite ones_succ. reflexivity.
Qed.

Example walk_on_A6_ex :
  run dtbl 3 (mkConf A6 [on] on (ones 1)) =
  Some (mkConf A7 (bl :: ones 2 ++ [on]) bl []).
Proof. reflexivity. Qed.

(** ** Walking back over the value at A9 *)

Lemma walk_A9 : forall k Z X,
  run dtbl (k + 2) (mkConf A9 (ones k ++ bl :: Z) on X) =
  Some (mkConf AA (tl Z) (hd bl Z) (bl :: ones (k + 1) ++ X)).
Proof.
  intros k. induction k as [|k IH]; intros Z X.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S k + 2) with (S (k + 2)) by lia.
    rewrite run_S. cbn [ones]. rewrite dA9_on. cbn.
    rewrite IH. rewrite ones_succ. reflexivity.
Qed.

Example walk_A9_ex :
  run dtbl 3 (mkConf A9 (ones 1 ++ bl :: [bl; on]) on [on]) =
  Some (mkConf AA [on] bl (bl :: ones 2 ++ [on])).
Proof. reflexivity. Qed.

(** ** Walking back over the holes at AA *)

Lemma walk_AA : forall k Y X,
  run dtbl (k + 2) (mkConf AA (zeros k ++ on :: Y) bl X) =
  Some (mkConf R1 (tl Y) (hd bl Y) (on :: zeros (k + 1) ++ X)).
Proof.
  intros k. induction k as [|k IH]; intros Y X.
  - cbn [Nat.add]. cbn. reflexivity.
  - replace (S k + 2) with (S (k + 2)) by lia.
    rewrite run_S. cbn [zeros]. rewrite dAA_bl. cbn.
    rewrite IH. rewrite zeros_succ. reflexivity.
Qed.

Example walk_AA_ex :
  run dtbl 4 (mkConf AA (zeros 2 ++ on :: [on; bl]) bl [on]) =
  Some (mkConf R1 [bl] on (on :: zeros 3 ++ [on])).
Proof. reflexivity. Qed.

(** ** The two "phase" lemmas: R4 up to R5, R5 up to R6, with [hd]/[tl] entries *)

Lemma walk_R4_phase : forall m A v,
  run dtbl (m + 1)
    (mkConf R4 A (hd bl (zeros m ++ ones (S v) ++ bl :: on :: []))
            (tl (zeros m ++ ones (S v) ++ bl :: on :: []))) =
  Some (mkConf R5 (on :: zeros m ++ A)
                  (hd bl (ones v ++ bl :: on :: []))
                  (tl (ones v ++ bl :: on :: []))).
Proof.
  intros m. induction m as [|m IH]; intros A v.
  - change (run dtbl 1 (mkConf R4 A on (ones v ++ bl :: on :: [])) =
            Some (mkConf R5 (on :: A) (hd bl (ones v ++ bl :: on :: []))
                            (tl (ones v ++ bl :: on :: [])))).
    apply walk_hit_R4.
  - change (run dtbl (S (m + 1))
              (mkConf R4 A bl
                (zeros m ++ on :: (ones v ++ bl :: on :: []))) =
            Some (mkConf R5 (on :: zeros (S m) ++ A)
                            (hd bl (ones v ++ bl :: on :: []))
                            (tl (ones v ++ bl :: on :: [])))).
    replace (S (m + 1)) with (m + 2) by lia.
    rewrite walk_bl_R4.
    replace (m + 1) with (S m) by lia.
    reflexivity.
Qed.

(** ** The return-side phases, with the value's length as the parameter *)

Lemma walk_A5_phase : forall v A,
  run dtbl (v + 3)
    (mkConf A5 A bl (zeros (v + 1) ++ ones (2 * v + 3))) =
  Some (mkConf A6 (on :: zeros (v + 2) ++ A) on (ones (2 * v + 1))).
Proof.
  intros v A.
  replace (v + 3) with (v + 1 + 2) by lia.
  replace (2 * v + 3) with (S (2 * v + 2)) by lia.
  change (run dtbl (v + 1 + 2)
            (mkConf A5 A bl (zeros (v + 1) ++ on :: ones (2 * v + 2))) =
          Some (mkConf A6 (on :: zeros (v + 2) ++ A) on (ones (2 * v + 1)))).
  rewrite walk_bl_A5.
  replace (v + 1 + 1) with (v + 2) by lia.
  replace (2 * v + 2) with (S (2 * v + 1)) by lia.
  rewrite hd_ones_nil, tl_ones_nil.
  reflexivity.
Qed.

Lemma walk_A6_phase : forall v A,
  run dtbl (2 * v + 3) (mkConf A6 A on (ones (2 * v + 1))) =
  Some (mkConf A7 (bl :: ones (2 * v + 2) ++ A) bl []).
Proof.
  intros v A.
  replace (2 * v + 3) with (2 * v + 1 + 2) by lia.
  replace (2 * v + 2) with (2 * v + 1 + 1) by lia.
  apply walk_on_A6.
Qed.

Lemma walk_A9_phase : forall v Z,
  run dtbl (2 * v + 4)
    (mkConf A9 (ones (2 * v + 2) ++ bl :: Z) on (bl :: on :: [])) =
  Some (mkConf AA (tl Z) (hd bl Z) (bl :: ones (2 * v + 3) ++ bl :: on :: [])).
Proof.
  intros v Z.
  replace (2 * v + 4) with (2 * v + 2 + 2) by lia.
  replace (2 * v + 3) with (2 * v + 2 + 1) by lia.
  apply walk_A9.
Qed.

(** ** The round, one stage of the drive *)

Definition round_sum (m v : nat) : nat :=
  1 + 1 + (m + 1) + (v + 1) + 1 + (k_pre (S v) 0 0 + 1)
    + (v + 3) + (2 * v + 3) + 1 + 1 + (2 * v + 4) + (v + m + 3).

Lemma round_v0 : forall m L,
  run dtbl (round_sum m 0)
    (mkConf R1 (on :: L) on (on :: zeros m ++ ones 1 ++ bl :: on :: [])) =
  Some (mkConf R1 L on (on :: zeros (m + 3) ++ ones 3 ++ bl :: on :: [])).
Proof.
  intros m L.
  set (E := mkConf R1 (on :: L) on (on :: zeros m ++ ones 1 ++ bl :: on :: [])).
  set (C1 := mkConf R2 (ones 2 ++ L) on (zeros m ++ ones 1 ++ bl :: on :: [])).
  set (C2 := mkConf R4 (bl :: ones 2 ++ L)
                 (hd bl (zeros m ++ ones 1 ++ bl :: on :: []))
                 (tl (zeros m ++ ones 1 ++ bl :: on :: []))).
  set (C3 := mkConf R5 (on :: zeros m ++ bl :: ones 2 ++ L)
                 (hd bl (ones 0 ++ bl :: on :: []))
                 (tl (ones 0 ++ bl :: on :: []))).
  set (C4 := mkConf R6 (zeros (S m) ++ ones 2 ++ L) on (bl :: on :: [])).
  set (C5 := mkConf (SH + K2) (on :: zeros (S m) ++ ones 2 ++ L) bl (on :: [])).
  set (C6 := mkConf A5 (bl :: zeros m ++ ones 2 ++ L) bl (zeros 1 ++ ones 3)).
  set (C7 := mkConf A6 (on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) on (ones 1)).
  set (C8 := mkConf A7 (bl :: ones 2 ++ on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) bl []).
  set (C9 := mkConf A8 (ones 2 ++ on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) bl (on :: [])).
  set (C10 := mkConf A9 (ones 1 ++ on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) on (bl :: on :: [])).
  set (C11 := mkConf AA (bl :: zeros m ++ ones 2 ++ L) bl (bl :: ones 3 ++ bl :: on :: [])).
  set (C12 := mkConf R1 L on (on :: zeros (S m + 1) ++ bl :: ones 3 ++ bl :: on :: [])).
  assert (H1 : run dtbl 1 E = Some C1) by (subst E C1; rewrite run_S; cbn; reflexivity).
  assert (H2 : run dtbl 1 C1 = Some C2) by (subst C1 C2; rewrite run_S; cbn; reflexivity).
  assert (H3 : run dtbl (m + 1) C2 = Some C3) by (subst C2 C3; apply walk_R4_phase).
  assert (H4 : run dtbl 1 C3 = Some C4)
    by (subst C3 C4; change (run dtbl 1
          (mkConf R5 (on :: zeros m ++ bl :: ones 2 ++ L) bl (on :: [])) =
        Some (mkConf R6 (zeros (S m) ++ ones 2 ++ L) on (bl :: on :: [])));
        rewrite walk_bl_R5; cbn;
        replace (m + 1) with (S m) by lia; rewrite zeros_succ; reflexivity).
  assert (H5 : run dtbl 1 C4 = Some C5) by (subst C4 C5; rewrite run_S; cbn; reflexivity).
  assert (H6 : run dtbl (k_pre 1 0 0 + 1) C5 = Some C6)
    by (subst C5 C6;
        change (run dtbl (k_pre (S 0) 0 0 + 1)
          (mkConf (SH + K2) (ones (S 0) ++ zeros (S m) ++ ones 2 ++ L) bl (on :: [])) =
        Some (mkConf A5 (bl :: zeros m ++ ones 2 ++ L) bl (zeros 1 ++ ones 3)));
        apply k_block_drive_exit).
  assert (H7 : run dtbl 3 C6 = Some C7).
  { subst C6 C7.
    change (run dtbl (1 + 2)
      (mkConf A5 (bl :: zeros m ++ ones 2 ++ L) bl (zeros 1 ++ on :: ones 2)) =
      Some (mkConf A6 (on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) on (ones 1))).
    rewrite walk_bl_A5.
    rewrite hd_ones_nil, tl_ones_nil. reflexivity. }
  assert (H8 : run dtbl 3 C7 = Some C8).
  { subst C7 C8.
    change (run dtbl (1 + 2)
      (mkConf A6 (on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) on (ones 1)) =
      Some (mkConf A7 (bl :: ones 2 ++ on :: zeros 2 ++ bl :: zeros m ++ ones 2 ++ L) bl [])).
    apply walk_on_A6. }
  assert (H9 : run dtbl 1 C8 = Some C9) by (subst C8 C9; rewrite run_S; cbn; reflexivity).
  assert (H10 : run dtbl 1 C9 = Some C10) by (subst C9 C10; rewrite run_S; cbn; reflexivity).
  assert (H11 : run dtbl 4 C10 = Some C11).
  { subst C10 C11.
    change (run dtbl (2 + 2)
      (mkConf A9 (ones 2 ++ bl :: (bl :: bl :: zeros m ++ ones 2 ++ L)) on (bl :: on :: [])) =
      Some (mkConf AA (bl :: zeros m ++ ones 2 ++ L) bl (bl :: ones 3 ++ bl :: on :: []))).
    rewrite (walk_A9 2 (bl :: bl :: zeros m ++ ones 2 ++ L) (bl :: on :: [])).
    reflexivity. }
  assert (H12 : run dtbl (m + 3) C11 = Some C12).
  { subst C11 C12.
    replace (m + 3) with (S m + 2) by lia.
    change (run dtbl (S m + 2)
      (mkConf AA (zeros (S m) ++ on :: (on :: L)) bl
                 (bl :: ones 3 ++ bl :: on :: [])) =
      Some (mkConf R1 L on (on :: zeros (S m + 1) ++ bl :: ones 3 ++ bl :: on :: []))).
    apply walk_AA. }
  pose proof (run_cat_d 1 1 E C1 C2 H1 H2) as H12_.
  pose proof (run_cat_d (1 + 1) (m + 1) E C2 C3 H12_ H3) as H123.
  pose proof (run_cat_d (1 + 1 + (m + 1)) 1 E C3 C4 H123 H4) as H1234.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1) 1 E C4 C5 H1234 H5) as H12345.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1) (k_pre 1 0 0 + 1) E C5 C6 H12345 H6) as H123456.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1)) 3 E C6 C7 H123456 H7) as H7'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3) 3 E C7 C8 H7' H8) as H8'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3 + 3) 1 E C8 C9 H8' H9) as H9'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3 + 3 + 1) 1 E C9 C10 H9' H10) as H10'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3 + 3 + 1 + 1) 4 E C10 C11 H10' H11) as H11'.
  pose proof (run_cat_d (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3 + 3 + 1 + 1 + 4) (m + 3) E C11 C12 H11' H12) as H12''.
  subst E C12.
  replace (on :: zeros (S m + 1) ++ bl :: ones 3 ++ bl :: on :: [])
    with (on :: zeros (m + 3) ++ ones 3 ++ bl :: on :: []) in H12''
    by (rewrite zeros_succ; replace (S (S m + 1)) with (m + 3) by lia; reflexivity).
  replace (round_sum m 0)
    with (1 + 1 + (m + 1) + 1 + 1 + (k_pre 1 0 0 + 1) + 3 + 3 + 1 + 1 + 4 + (m + 3))
    by (unfold round_sum; lia).
  exact H12''.
Qed.

Print Assumptions walk_bl_R4.
Print Assumptions walk_hit_R4.
Print Assumptions walk_bl_A5.
Print Assumptions walk_on_R5.
Print Assumptions walk_bl_R5.
Print Assumptions walk_on_A6.
Print Assumptions walk_A9.
Print Assumptions walk_AA.
Print Assumptions walk_R4_phase.
Print Assumptions walk_A5_phase.
Print Assumptions walk_A6_phase.
Print Assumptions walk_A9_phase.
Print Assumptions round_v0.
