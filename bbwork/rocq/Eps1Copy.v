(* The eps_1 machine at tape level: the copy's phases.

   Eps1Tape.v proves the rung branch: the entry frame reaches [WALK] with one
   budget mark spent, the block region flush and blank, and the value region
   untouched.  This file is the next piece under it -- the copy's table, its
   rows, and the parametric walks its phases are built from.

   The copy's job is to turn

       [block: empty] 1(wall) blanks 1^v 0 1(seed)

   into the same frame with the block holding 1^v, the value still holding 1^v
   (shifted one cell left), the seed where it was, and the rung budget pushed v
   cells left so that it stays clear of the growing block.  It is one sweep and
   not two: each trip rewrites the value's left end one cell left *and* writes
   one block mark, so the block grows at exactly the rate the budget recedes.

   What is in this file:

     * the copy's rows (24 of them, generated from tools/eps1_machine.py by
       tools/emit_eps1_copy.py, so the machine proved about is the machine that
       runs) and one step lemma per row;
     * the walks the trip is made of, each stated for an arbitrary run length
       with an exact step count: [walk_WALK] over the gap to the value's left
       end, [steps_C1] back over the erased mark, [walk_CL_marks] and
       [walk_CL_blank] over the prefix, [walk_CG] over the gap to the wall,
       [step_B1] past the wall, [walk_B2] over the block, and [walk_P1] out to
       the budget's rightmost mark.

   What is also here: the whole trip, [trip].  A trip is the copy's unit of
   work: from the frame [trip_frame (S m) D (S n) A] with the head on the
   source's next mark, it erases that mark, writes the value's mark one cell
   left, writes the block's mark at the block's left end, carries the rung
   budget one cell left, walks back over the budget, the gap, the block and the
   wall, and comes back along the copy to the next source cell.  In

     4m + 2D + 2(S n) + 21

   steps it reaches [trip_frame (S (S m)) D (S n) A] -- the same frame with
   both runs one mark longer, the budget one cell further left and the head on
   the source's next cell.  The two halves are separate theorems, each with its
   own count and each chained out of single-phase lemmas:

     * [trip_out] (2m + D + 11 steps): R3 -> P2, the block written flush;
     * [trip_back] (2(S n) + 2m + D + 12 steps): P2 -> R3, the budget carried
       and the head back on the source.

   And the triangle is closed: [trip0] is the same trip at j = 0, from an empty
   block and empty copy, in 2D + 2(S n) + 17 steps; [trip_step] is one trip at
   *any* frame index j <= N (it dispatches to [trip0] at j = 0 and to [trip]
   above it); and [sweep] inducts on the number of trips.  From the head on the
   source's first mark with w marks behind it, [sweep] reaches

     sweep_steps (S w) j d n = v * (4j + 2(S d) + 2(S n) + 15) + 2vv   (v = S w)

   steps later [trip_frame (j + S w) D k] with the head on the blank after the
   source: block and copy both 1^(j + S w), the budget S w cells further left,
   and the value's tail [skipn (j + S w) A] untouched.  So every mark the copy
   eats is one the block keeps and the value still holds.

   Every phase lemma in this file, [trip_out], [trip_back], [trip], [trip0],
   [trip_step] and [sweep] itself is checked against the running machine by
   tools/check_eps1_copy.py (994 frames, all matching) -- the composed
   statements, not only the phases.  The 96 sweep cases run up to four trips
   from frames j = 0, 1, 2 with [sweep_steps]' own count; raising that count by
   one makes all 96 fail, so the composed cases test the count too.

   What is NOT in this file, and must not be read as done:

     * the eps_0 stage branch above the copy (the [a] count of halves), which
       decides when the rung recurses; the copy is proved about in the frame
       that branch hands over;
     * the blank-tape prologue (step 4 of FGH_MACHINES_PLAN.md), which writes
       that frame and lands the head on the wall.

   So what is proved here is "the copy copies, for every v", not "the machine
   runs the ladder".  The measured whole copy, 2v^2 + 2vD + 2vk + 12v + 2G + 6
   for gap D and budget k, is [sweep]'s count plus the entrance and the exit
   outside it; no theorem here depends on that number. *)

From Stdlib Require Import List Arith Lia.
From Top Require Import TM Eps1Tape.
Import ListNotations.
Open Scope nat_scope.

(** ** States *)

(* [WALK] (34) is imported from Eps1Tape.v: the rung branch hands over there. *)

Definition C1 : nat := 35.       (* one past the erased source mark *)
Definition C2 : nat := 36.       (* back over it *)
Definition C3 : nat := 37.       (* write the prefix's new mark *)
Definition CL : nat := 38.       (* left over the prefix *)
Definition CG : nat := 39.       (* left over the gap to the wall *)
Definition B1 : nat := 40.       (* left of the wall *)
Definition B2 : nat := 41.       (* walk the block, then write its new mark *)
Definition P1 : nat := 43.       (* left to the budget's rightmost mark *)
Definition P2 : nat := 44.       (* carry it to the budget's left end *)
Definition P3 : nat := 45.       (* right again over the budget *)
Definition P4 : nat := 46.       (* right over the gap *)
Definition P5 : nat := 47.       (* right over the block *)
Definition BQ : nat := 48.       (* the blank right of the block *)
Definition BW : nat := 49.       (* cross the wall, going right *)
Definition R1 : nat := 50.       (* right over the gap *)
Definition R2 : nat := 51.       (* right over the prefix *)
Definition R3 : nat := 52.       (* the next source mark, or the handover *)

Definition ZA : nat := 60.       (* handover: back over the value *)
Definition ZB : nat := 61.
Definition ZC : nat := 62.
Definition ZD : nat := 63.
Definition S4 : nat := 25.       (* where the handover rejoins eps_0's rounds *)
Definition F0 : nat := 12.       (* the stage branch: a round starts here *)

(** ** The table *)

(* BEGIN TABLE -- generated by tools/emit_eps1_copy.py; do not edit *)
Definition ctbl : table := fun s b =>
  match s, b with
  | 25, on => Some (on, true, 12)  (* S4 -> F0 *)
  | 34, bl => Some (bl, true, 34)  (* WALK -> WALK *)
  | 34, on => Some (bl, true, 35)  (* WALK -> C1 *)
  | 35, bl => Some (bl, false, 36)  (* C1 -> C2 *)
  | 35, on => Some (on, false, 36)  (* C1 -> C2 *)
  | 36, bl => Some (bl, false, 37)  (* C2 -> C3 *)
  | 36, on => Some (on, false, 37)  (* C2 -> C3 *)
  | 37, bl => Some (on, false, 38)  (* C3 -> CL *)
  | 37, on => Some (on, false, 38)  (* C3 -> CL *)
  | 38, bl => Some (bl, false, 39)  (* CL -> CG *)
  | 38, on => Some (on, false, 38)  (* CL -> CL *)
  | 39, bl => Some (bl, false, 39)  (* CG -> CG *)
  | 39, on => Some (on, false, 40)  (* CG -> B1 *)
  | 40, bl => Some (bl, false, 41)  (* B1 -> B2 *)
  | 40, on => Some (on, false, 41)  (* B1 -> B2 *)
  | 41, bl => Some (on, false, 43)  (* B2 -> P1 *)
  | 41, on => Some (on, false, 41)  (* B2 -> B2 *)
  | 43, bl => Some (bl, false, 43)  (* P1 -> P1 *)
  | 43, on => Some (bl, false, 44)  (* P1 -> P2 *)
  | 44, bl => Some (on, true, 45)  (* P2 -> P3 *)
  | 44, on => Some (on, false, 44)  (* P2 -> P2 *)
  | 45, bl => Some (bl, true, 46)  (* P3 -> P4 *)
  | 45, on => Some (on, true, 45)  (* P3 -> P3 *)
  | 46, bl => Some (bl, true, 46)  (* P4 -> P4 *)
  | 46, on => Some (on, true, 47)  (* P4 -> P5 *)
  | 47, bl => Some (bl, true, 48)  (* P5 -> BQ *)
  | 47, on => Some (on, true, 47)  (* P5 -> P5 *)
  | 48, bl => Some (bl, true, 49)  (* BQ -> BW *)
  | 48, on => Some (on, true, 49)  (* BQ -> BW *)
  | 49, bl => Some (bl, true, 50)  (* BW -> R1 *)
  | 49, on => Some (on, true, 50)  (* BW -> R1 *)
  | 50, bl => Some (bl, true, 50)  (* R1 -> R1 *)
  | 50, on => Some (on, true, 51)  (* R1 -> R2 *)
  | 51, bl => Some (bl, true, 52)  (* R2 -> R3 *)
  | 51, on => Some (on, true, 51)  (* R2 -> R2 *)
  | 52, bl => Some (bl, false, 60)  (* R3 -> ZA *)
  | 52, on => Some (bl, true, 35)  (* R3 -> C1 *)
  | 60, bl => Some (bl, false, 61)  (* ZA -> ZB *)
  | 61, bl => Some (bl, false, 62)  (* ZB -> ZC *)
  | 61, on => Some (on, false, 61)  (* ZB -> ZB *)
  | 62, bl => Some (bl, false, 62)  (* ZC -> ZC *)
  | 62, on => Some (on, false, 63)  (* ZC -> ZD *)
  | 63, bl => Some (bl, true, 25)  (* ZD -> S4 *)
  | _, _ => None
  end.
(* END TABLE *)

(** ** One-step facts, one per row of the copy and its handover *)

Lemma st_WALK_bl : forall L R,
  step ctbl (mkConf WALK L bl R) = Some (mkConf WALK (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_WALK_on : forall L R,
  step ctbl (mkConf WALK L on R) = Some (mkConf C1 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_C1_bl : forall L R,
  step ctbl (mkConf C1 L bl R) = Some (mkConf C2 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_C1_on : forall L R,
  step ctbl (mkConf C1 L on R) = Some (mkConf C2 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_C2_bl : forall L R,
  step ctbl (mkConf C2 L bl R) = Some (mkConf C3 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_C2_on : forall L R,
  step ctbl (mkConf C2 L on R) = Some (mkConf C3 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_C3_bl : forall L R,
  step ctbl (mkConf C3 L bl R) = Some (mkConf CL (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_C3_on : forall L R,
  step ctbl (mkConf C3 L on R) = Some (mkConf CL (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_C3_any : forall L c R,
  step ctbl (mkConf C3 L c R) = Some (mkConf CL (tl L) (hd bl L) (on :: R)).
Proof. intros L c R. destruct c; reflexivity. Qed.

Lemma st_CL_bl : forall L R,
  step ctbl (mkConf CL L bl R) = Some (mkConf CG (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_CL_on : forall L R,
  step ctbl (mkConf CL L on R) = Some (mkConf CL (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_CG_bl : forall L R,
  step ctbl (mkConf CG L bl R) = Some (mkConf CG (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_CG_on : forall L R,
  step ctbl (mkConf CG L on R) = Some (mkConf B1 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_B1_bl : forall L R,
  step ctbl (mkConf B1 L bl R) = Some (mkConf B2 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_B1_on : forall L R,
  step ctbl (mkConf B1 L on R) = Some (mkConf B2 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_B2_bl : forall L R,
  step ctbl (mkConf B2 L bl R) = Some (mkConf P1 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_B2_on : forall L R,
  step ctbl (mkConf B2 L on R) = Some (mkConf B2 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_P1_bl : forall L R,
  step ctbl (mkConf P1 L bl R) = Some (mkConf P1 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_P1_on : forall L R,
  step ctbl (mkConf P1 L on R) = Some (mkConf P2 (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_P2_bl : forall L R,
  step ctbl (mkConf P2 L bl R) = Some (mkConf P3 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P2_on : forall L R,
  step ctbl (mkConf P2 L on R) = Some (mkConf P2 (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_P3_bl : forall L R,
  step ctbl (mkConf P3 L bl R) = Some (mkConf P4 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P3_on : forall L R,
  step ctbl (mkConf P3 L on R) = Some (mkConf P3 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P4_bl : forall L R,
  step ctbl (mkConf P4 L bl R) = Some (mkConf P4 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P4_on : forall L R,
  step ctbl (mkConf P4 L on R) = Some (mkConf P5 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P5_bl : forall L R,
  step ctbl (mkConf P5 L bl R) = Some (mkConf BQ (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_P5_on : forall L R,
  step ctbl (mkConf P5 L on R) = Some (mkConf P5 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_BQ_bl : forall L R,
  step ctbl (mkConf BQ L bl R) = Some (mkConf BW (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_BQ_on : forall L R,
  step ctbl (mkConf BQ L on R) = Some (mkConf BW (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_BW_bl : forall L R,
  step ctbl (mkConf BW L bl R) = Some (mkConf R1 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_BW_on : forall L R,
  step ctbl (mkConf BW L on R) = Some (mkConf R1 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_R1_bl : forall L R,
  step ctbl (mkConf R1 L bl R) = Some (mkConf R1 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_R1_on : forall L R,
  step ctbl (mkConf R1 L on R) = Some (mkConf R2 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_R2_bl : forall L R,
  step ctbl (mkConf R2 L bl R) = Some (mkConf R3 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_R2_on : forall L R,
  step ctbl (mkConf R2 L on R) = Some (mkConf R2 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_R3_bl : forall L R,
  step ctbl (mkConf R3 L bl R) = Some (mkConf ZA (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_R3_on : forall L R,
  step ctbl (mkConf R3 L on R) = Some (mkConf C1 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_ZA_bl : forall L R,
  step ctbl (mkConf ZA L bl R) = Some (mkConf ZB (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_ZB_bl : forall L R,
  step ctbl (mkConf ZB L bl R) = Some (mkConf ZC (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_ZB_on : forall L R,
  step ctbl (mkConf ZB L on R) = Some (mkConf ZB (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_ZC_bl : forall L R,
  step ctbl (mkConf ZC L bl R) = Some (mkConf ZC (tl L) (hd bl L) (bl :: R)).
Proof. reflexivity. Qed.

Lemma st_ZC_on : forall L R,
  step ctbl (mkConf ZC L on R) = Some (mkConf ZD (tl L) (hd bl L) (on :: R)).
Proof. reflexivity. Qed.

Lemma st_ZD_bl : forall L R,
  step ctbl (mkConf ZD L bl R) = Some (mkConf S4 (bl :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

Lemma st_S4_on : forall L R,
  step ctbl (mkConf S4 L on R) = Some (mkConf F0 (on :: L) (hd bl R) (tl R)).
Proof. reflexivity. Qed.

(** ** Runs of cells *)

Lemma zeros_S : forall n L, zeros (S n) ++ L = bl :: zeros n ++ L.
Proof. reflexivity. Qed.

Lemma ones_S : forall n L, ones (S n) ++ L = on :: ones n ++ L.
Proof. reflexivity. Qed.

Lemma hd_zeros_S : forall n, hd bl (zeros (S n)) = bl.
Proof. reflexivity. Qed.

Lemma tl_zeros_S : forall n, tl (zeros (S n)) = zeros n.
Proof. reflexivity. Qed.

Lemma hd_ones_S : forall n L, hd bl (ones (S n) ++ L) = on.
Proof. reflexivity. Qed.

Lemma tl_ones_S : forall n L, tl (ones (S n) ++ L) = ones n ++ L.
Proof. reflexivity. Qed.

Lemma ones_S_any : forall n (L : list sym), ones n ++ on :: L = ones (S n) ++ L.
Proof. intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.


Lemma ones_0 : ones 0 = []. Proof. reflexivity. Qed.
Lemma zeros_0 : zeros 0 = []. Proof. reflexivity. Qed.

Lemma hd_zeros_app : forall n L, hd bl (zeros (S n) ++ L) = bl.
Proof. intros n L. reflexivity. Qed.

Lemma tl_zeros_app : forall n L, tl (zeros (S n) ++ L) = zeros n ++ L.
Proof. intros n L. reflexivity. Qed.

Lemma hd_ones_app : forall n L, hd bl (ones (S n) ++ L) = on.
Proof. intros n L. reflexivity. Qed.

Lemma tl_ones_app : forall n L, tl (ones (S n) ++ L) = ones n ++ L.
Proof. intros n L. reflexivity. Qed.

Lemma zeros_S_any : forall n (L : list sym), zeros n ++ bl :: L = zeros (S n) ++ L.
Proof. intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma zeros_swap : forall n (L : list sym), zeros n ++ (bl :: L) = bl :: (zeros n ++ L).
Proof. intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - change ((bl :: zeros n) ++ (bl :: L) = bl :: ((bl :: zeros n) ++ L)).
    cbn [app]. rewrite IH. reflexivity.
Qed.

Lemma ones_swap : forall n (L : list sym), ones n ++ (on :: L) = on :: (ones n ++ L).
Proof. intros n. induction n as [|n IH]; intros L.
  - reflexivity.
  - change ((on :: ones n) ++ (on :: L) = on :: ((on :: ones n) ++ L)).
    cbn [app]. rewrite IH. reflexivity.
Qed.

Lemma tl_ones_on : forall n (L : list sym), tl (ones n ++ on :: L) = ones n ++ L.
Proof. intros n L. rewrite ones_swap. reflexivity. Qed.

Lemma hd_ones_on : forall n (L : list sym), hd bl (ones n ++ on :: L) = on.
Proof. intros n L. rewrite ones_swap. reflexivity. Qed.

(** ** Phase 1: [WALK] over the gap to the value's left end, which it erases *)

Lemma walk_WALK : forall m L Y,
  run ctbl (m + 2) (mkConf WALK L bl (zeros m ++ on :: Y)) =
  Some (mkConf C1 (bl :: zeros (S m) ++ L) (hd bl Y) (tl Y)).
Proof.
  intros m. induction m as [|m IH]; intros L Y.
  - cbn [Nat.add]. rewrite run_S, st_WALK_bl.
    change (run ctbl 1 (mkConf WALK (bl :: L) on Y) =
            Some (mkConf C1 (bl :: bl :: L) (hd bl Y) (tl Y))).
    rewrite run_S, st_WALK_on. reflexivity.
  - replace (S m + 2) with (S (m + 2)) by lia.
    rewrite run_S, st_WALK_bl.
    rewrite tl_zeros_app, hd_zeros_app.
    rewrite IH. rewrite zeros_S_any. reflexivity.
Qed.

(** ** Phase 2: the three fixed moves that put the value's mark at [x-1] *)

Lemma steps_C1 : forall A c Y,
  run ctbl 3 (mkConf C1 (bl :: A) c Y) =
  Some (mkConf CL (tl (tl A)) (hd bl (tl A)) (on :: bl :: c :: Y)).
Proof.
  intros A c Y. destruct c.
  - rewrite run_S, st_C1_bl. cbn [hd tl].
    rewrite run_S, st_C2_bl. cbn [hd tl].
    rewrite run_S, st_C3_any. reflexivity.
  - rewrite run_S, st_C1_on. cbn [hd tl].
    rewrite run_S, st_C2_bl. cbn [hd tl].
    rewrite run_S, st_C3_any. reflexivity.
Qed.

(** ** Phase 3: left over the prefix, then the gap, to the wall *)

Lemma walk_CL_marks : forall m Z Y,
  run ctbl (S (S m)) (mkConf CL (ones m ++ bl :: Z) on Y) =
  Some (mkConf CG (tl Z) (hd bl Z) (bl :: ones (S m) ++ Y)).
Proof.
  intros m. induction m as [|m IH]; intros Z Y.
  - rewrite run_S, st_CL_on.
    change (run ctbl 1 (mkConf CL Z bl (on :: Y)) =
            Some (mkConf CG (tl Z) (hd bl Z) (bl :: on :: Y))).
    rewrite run_S, st_CL_bl. reflexivity.
  - replace (S (S (S m))) with (S (S (S m))) by lia.
    rewrite run_S, st_CL_on. rewrite tl_ones_app, hd_ones_app.
    rewrite IH. rewrite ones_S_any. reflexivity.
Qed.

Lemma walk_CL_blank : forall Z Y,
  run ctbl 1 (mkConf CL Z bl Y) = Some (mkConf CG (tl Z) (hd bl Z) (bl :: Y)).
Proof. intros Z Y. rewrite run_S, st_CL_bl. reflexivity. Qed.

Lemma walk_CG : forall q W Y,
  run ctbl (S q) (mkConf CG (tl (zeros q ++ on :: W)) (hd bl (zeros q ++ on :: W)) Y) =
  Some (mkConf B1 (tl W) (hd bl W) (on :: zeros q ++ Y)).
Proof.
  intros q. induction q as [|q IH]; intros W Y.
  - cbn [Nat.add].
    change (run ctbl 1 (mkConf CG W on Y) =
            Some (mkConf B1 (tl W) (hd bl W) (on :: Y))).
    rewrite run_S, st_CG_on. reflexivity.
  - rewrite run_S. rewrite tl_zeros_app, hd_zeros_app.
    rewrite st_CG_bl.
    rewrite IH. rewrite zeros_S_any. reflexivity.
Qed.

(** ** Phase 4: one step past the wall, then out over the block *)

Lemma step_B1 : forall L c Y,
  run ctbl 1 (mkConf B1 L c Y) = Some (mkConf B2 (tl L) (hd bl L) (c :: Y)).
Proof.
  intros L c Y. rewrite run_S. destruct c.
  - rewrite st_B1_bl. reflexivity.
  - rewrite st_B1_on. reflexivity.
Qed.

Lemma walk_B2 : forall m Z Y,
  run ctbl (S (S m)) (mkConf B2 (ones m ++ bl :: Z) on Y) =
  Some (mkConf P1 (tl Z) (hd bl Z) (ones (S (S m)) ++ Y)).
Proof.
  intros m. induction m as [|m IH]; intros Z Y.
  - rewrite run_S, st_B2_on.
    change (run ctbl 1 (mkConf B2 Z bl (on :: Y)) =
            Some (mkConf P1 (tl Z) (hd bl Z) (on :: on :: Y))).
    rewrite run_S, st_B2_bl. reflexivity.
  - replace (S (S (S m))) with (S (S (S m))) by lia.
    rewrite run_S, st_B2_on. rewrite tl_ones_app, hd_ones_app.
    rewrite IH. rewrite ones_S_any. reflexivity.
Qed.

(** ** Phase 5: the carry starts -- the budget's rightmost mark is erased *)

Lemma walk_P1 : forall q V Y,
  run ctbl (S q) (mkConf P1 (tl (zeros q ++ on :: V)) (hd bl (zeros q ++ on :: V)) Y) =
  Some (mkConf P2 (tl V) (hd bl V) (bl :: zeros q ++ Y)).
Proof.
  intros q. induction q as [|q IH]; intros V Y.
  - cbn [Nat.add].
    change (run ctbl 1 (mkConf P1 V on Y) =
            Some (mkConf P2 (tl V) (hd bl V) (bl :: Y))).
    rewrite run_S, st_P1_on. reflexivity.
  - rewrite run_S. rewrite tl_zeros_app, hd_zeros_app.
    rewrite st_P1_bl.
    rewrite IH. rewrite zeros_S_any. reflexivity.
Qed.

(** ** Composing the phases: the trip out *)

Definition trip_frame (j D kk : nat) (A : list sym) : list sym :=
  bl :: ones j ++ bl :: on :: bl :: ones j ++ bl :: zeros D ++ ones (S kk) ++ skipn j A.

Definition budget_l (m kk : nat) (A : list sym) : list sym := ones kk ++ skipn (S m) A.

Lemma run_cat_c : forall (k1 k2 : nat) (c1 c2 c3 : conf),
  run ctbl k1 c1 = Some c2 -> run ctbl k2 c2 = Some c3 ->
  run ctbl (k1 + k2) c1 = Some c3.
Proof. intros k1 k2 c1 c2 c3 H1 H2. rewrite run_add, H1. exact H2. Qed.

(** The one step at the wall, from the walk's [q = 0] instance. *)
Lemma walk_CG_0 : forall W Y,
  run ctbl 1 (mkConf CG W on Y) = Some (mkConf B1 (tl W) (hd bl W) (on :: Y)).
Proof. intros W Y. rewrite run_S, st_CG_on. reflexivity. Qed.

(** The return half's first two runs.  The carry off the value's left end --
    [P2] writes the mark it took from the wall back into the run it walked over
    and turns about -- and [P3]'s walk back over that run to its blank. *)

Lemma walk_P2 : forall n L Y,
  run ctbl (n + 2) (mkConf P2 (ones n ++ bl :: L) on Y) =
  Some (mkConf P3 (on :: L) on (ones n ++ Y)).
Proof.
  intros n. induction n as [|n IH]; intros L Y.
  - cbn [Nat.add].
    change (run ctbl 2 (mkConf P2 (bl :: L) on Y) =
            Some (mkConf P3 (on :: L) on Y)).
    rewrite run_S, st_P2_on.
    change (run ctbl 1 (mkConf P2 L bl (on :: Y)) =
            Some (mkConf P3 (on :: L) on Y)).
    rewrite run_S, st_P2_bl. reflexivity.
  - replace (S n + 2) with (S (n + 2)) by lia.
    rewrite run_S, st_P2_on.
    change (run ctbl (n + 2) (mkConf P2 (ones n ++ bl :: L) on (on :: Y)) =
            Some (mkConf P3 (on :: L) on (ones (S n) ++ Y))).
    rewrite IH. rewrite ones_S_any. reflexivity.
Qed.

Lemma walk_P3 : forall n L Y,
  run ctbl (S (S n)) (mkConf P3 (on :: L) on (ones n ++ bl :: Y)) =
  Some (mkConf P4 (bl :: ones (S n) ++ on :: L) (hd bl Y) (tl Y)).
Proof.
  intros n. induction n as [|n IH]; intros L Y.
  - rewrite run_S, st_P3_on.
    change (run ctbl 1 (mkConf P3 (on :: on :: L) bl Y) =
            Some (mkConf P4 (bl :: on :: on :: L) (hd bl Y) (tl Y))).
    rewrite run_S, st_P3_bl. reflexivity.
  - rewrite run_S, st_P3_on.
    change (run ctbl (S (S n)) (mkConf P3 (on :: on :: L) on (ones n ++ bl :: Y)) =
            Some (mkConf P4 (bl :: ones (S (S n)) ++ on :: L) (hd bl Y) (tl Y))).
    rewrite (IH (on :: L) Y). rewrite ones_S_any. reflexivity.
Qed.

(** ** The return half's remaining runs: over the gap, the block and the wall,
    then back along the copy to the next source cell. *)

Lemma walk_P4 : forall q L Z,
  run ctbl (q + 2) (mkConf P4 L bl (zeros q ++ on :: Z)) =
  Some (mkConf P5 (on :: zeros (S q) ++ L) (hd bl Z) (tl Z)).
Proof.
  intros q. induction q as [|q IH]; intros L Z.
  - cbn [Nat.add].
    change (run ctbl 2 (mkConf P4 L bl (on :: Z)) =
            Some (mkConf P5 (on :: bl :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_P4_bl.
    change (run ctbl 1 (mkConf P4 (bl :: L) on Z) =
            Some (mkConf P5 (on :: bl :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_P4_on. reflexivity.
  - replace (S q + 2) with (S (q + 2)) by lia.
    rewrite run_S, st_P4_bl.
    change (run ctbl (q + 2) (mkConf P4 (bl :: L) bl (zeros q ++ on :: Z)) =
            Some (mkConf P5 (on :: zeros (S (S q)) ++ L) (hd bl Z) (tl Z))).
    rewrite IH. rewrite zeros_S_any. reflexivity.
Qed.

Lemma walk_P5 : forall m L Z,
  run ctbl (m + 2) (mkConf P5 L on (ones m ++ bl :: Z)) =
  Some (mkConf BQ (bl :: ones m ++ on :: L) (hd bl Z) (tl Z)).
Proof.
  intros m. induction m as [|m IH]; intros L Z.
  - cbn [Nat.add].
    change (run ctbl 2 (mkConf P5 L on (bl :: Z)) =
            Some (mkConf BQ (bl :: on :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_P5_on.
    change (run ctbl 1 (mkConf P5 (on :: L) bl Z) =
            Some (mkConf BQ (bl :: on :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_P5_bl. reflexivity.
  - replace (S m + 2) with (S (m + 2)) by lia.
    rewrite run_S, st_P5_on.
    change (run ctbl (m + 2) (mkConf P5 (on :: L) on (ones m ++ bl :: Z)) =
            Some (mkConf BQ (bl :: ones (S m) ++ on :: L) (hd bl Z) (tl Z))).
    rewrite IH. rewrite ones_S_any. reflexivity.
Qed.

Lemma st_BQ_any : forall L (c : sym) Y,
  step ctbl (mkConf BQ L c Y) = Some (mkConf BW (c :: L) (hd bl Y) (tl Y)).
Proof. intros L c Y. destruct c; reflexivity. Qed.

Lemma st_BW_any : forall L (c : sym) Y,
  step ctbl (mkConf BW L c Y) = Some (mkConf R1 (c :: L) (hd bl Y) (tl Y)).
Proof. intros L c Y. destruct c; reflexivity. Qed.

Lemma walk_R2 : forall r L Z,
  run ctbl (r + 2) (mkConf R2 L on (ones r ++ bl :: Z)) =
  Some (mkConf R3 (bl :: ones r ++ on :: L) (hd bl Z) (tl Z)).
Proof.
  intros r. induction r as [|r IH]; intros L Z.
  - cbn [Nat.add].
    change (run ctbl 2 (mkConf R2 L on (bl :: Z)) =
            Some (mkConf R3 (bl :: on :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_R2_on.
    change (run ctbl 1 (mkConf R2 (on :: L) bl Z) =
            Some (mkConf R3 (bl :: on :: L) (hd bl Z) (tl Z))).
    rewrite run_S, st_R2_bl. reflexivity.
  - replace (S r + 2) with (S (r + 2)) by lia.
    rewrite run_S, st_R2_on.
    change (run ctbl (r + 2) (mkConf R2 (on :: L) on (ones r ++ bl :: Z)) =
            Some (mkConf R3 (bl :: ones (S r) ++ on :: L) (hd bl Z) (tl Z))).
    rewrite IH. rewrite ones_S_any. reflexivity.
Qed.

(** The trip out, spelled out.  Seven runs: the step off the wall's mark, the
    three steps back over the cell it erased, the walk over the prefix, the wall
    step, the step across the wall, the walk over the block, and the walk out to
    the budget's rightmost mark. *)
Lemma trip_out_lit : forall m D kk (c : sym) (Y A : list sym),
  run ctbl (2 * m + D + 11)
    (mkConf R3
      (bl :: ones (S m) ++ bl :: on :: bl :: ones (S m) ++ bl :: zeros D
           ++ ones (S kk) ++ skipn (S m) A)
      on (c :: Y)) =
  Some (mkConf P2
    (tl (ones kk ++ skipn (S m) A))
    (hd bl (ones kk ++ skipn (S m) A))
    (bl :: zeros D ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
         ++ on :: bl :: c :: Y)).
Proof.
  intros m D kk c Y A.
  assert (H1 : run ctbl 1
      (mkConf R3 (bl :: ones (S m) ++ bl :: on :: bl :: ones (S m) ++ bl :: zeros D
                    ++ ones (S kk) ++ skipn (S m) A) on (c :: Y)) =
      Some (mkConf C1 (bl :: bl :: ones (S m) ++ bl :: on :: bl :: ones (S m)
                         ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A) c Y)).
  { rewrite run_S, st_R3_on. reflexivity. }
  assert (H2 : run ctbl 3
      (mkConf C1 (bl :: bl :: ones (S m) ++ bl :: on :: bl :: ones (S m)
                    ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A) c Y) =
      Some (mkConf CL (ones m ++ bl :: on :: bl :: ones (S m) ++ bl :: zeros D
                         ++ ones (S kk) ++ skipn (S m) A) on (on :: bl :: c :: Y))).
  { rewrite (steps_C1 (bl :: ones (S m) ++ bl :: on :: bl :: ones (S m)
                         ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A) c Y).
    cbn [tl hd]. rewrite tl_ones_app, hd_ones_app. reflexivity. }
  assert (H3 : run ctbl (S (S m))
      (mkConf CL (ones m ++ bl :: on :: bl :: ones (S m) ++ bl :: zeros D
                    ++ ones (S kk) ++ skipn (S m) A) on (on :: bl :: c :: Y)) =
      Some (mkConf CG (bl :: ones (S m) ++ bl :: zeros D ++ ones (S kk)
                         ++ skipn (S m) A) on
              (bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite (walk_CL_marks m (on :: bl :: ones (S m) ++ bl :: zeros D ++ ones (S kk)
                               ++ skipn (S m) A) (on :: bl :: c :: Y)).
    cbn [tl hd]. reflexivity. }
  assert (H4 : run ctbl 1
      (mkConf CG (bl :: ones (S m) ++ bl :: zeros D ++ ones (S kk)
                    ++ skipn (S m) A) on (bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf B1 (ones (S m) ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A)
              bl (on :: bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite walk_CG_0. cbn [tl hd]. reflexivity. }
  assert (H5 : run ctbl 1
      (mkConf B1 (ones (S m) ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A)
              bl (on :: bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf B2 (ones m ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A)
              on (bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite (step_B1 (ones (S m) ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A)
               bl (on :: bl :: ones (S m) ++ on :: bl :: c :: Y)).
    cbn [tl hd]. rewrite tl_ones_app, hd_ones_app. reflexivity. }
  assert (H6 : run ctbl (S (S m))
      (mkConf B2 (ones m ++ bl :: zeros D ++ ones (S kk) ++ skipn (S m) A) on
              (bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf P1 (tl (zeros D ++ ones (S kk) ++ skipn (S m) A))
              (hd bl (zeros D ++ ones (S kk) ++ skipn (S m) A))
              (ones (S (S m)) ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite (walk_B2 m (zeros D ++ ones (S kk) ++ skipn (S m) A)
               (bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)).
    reflexivity. }
  assert (H7 : run ctbl (S D)
      (mkConf P1 (tl (zeros D ++ ones (S kk) ++ skipn (S m) A))
              (hd bl (zeros D ++ ones (S kk) ++ skipn (S m) A))
              (ones (S (S m)) ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf P2 (tl (ones kk ++ skipn (S m) A))
              (hd bl (ones kk ++ skipn (S m) A))
              (bl :: zeros D ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
                   ++ on :: bl :: c :: Y))).
  { change (run ctbl (S D)
      (mkConf P1 (tl (zeros D ++ on :: (ones kk ++ skipn (S m) A)))
              (hd bl (zeros D ++ on :: (ones kk ++ skipn (S m) A)))
              (ones (S (S m)) ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf P2 (tl (ones kk ++ skipn (S m) A))
              (hd bl (ones kk ++ skipn (S m) A))
              (bl :: zeros D ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
                   ++ on :: bl :: c :: Y))).
    rewrite (walk_P1 D (ones kk ++ skipn (S m) A)
               (ones (S (S m)) ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)).
    cbn [tl hd]. reflexivity. }
  replace (2 * m + D + 11)
    with (1 + (3 + (S (S m) + (1 + (1 + (S (S m) + (S D))))))) by lia.
  eapply run_cat_c; [exact H1 | eapply run_cat_c; [exact H2 |
    eapply run_cat_c; [exact H3 | eapply run_cat_c; [exact H4 |
      eapply run_cat_c; [exact H5 | eapply run_cat_c; [exact H6 | exact H7]]]]]].
Qed.

(** The trip out as the copy's own shape: from one trip's start frame to the
    next trip's start, the frame's block index does not move but the head does,
    and the budget is one mark longer on the left. *)
Theorem trip_out : forall m D kk (c : sym) (Y A : list sym),
  run ctbl (2 * m + D + 11)
    (mkConf R3 (trip_frame (S m) D kk A) on (c :: Y)) =
  Some (mkConf P2
    (tl (budget_l m kk A)) (hd bl (budget_l m kk A))
    (bl :: zeros D ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
         ++ on :: bl :: c :: Y)).
Proof. intros. unfold trip_frame, budget_l. apply trip_out_lit. Qed.


(** ** The phases, closed *)

Print Assumptions st_R3_on.
Print Assumptions st_CL_on.
Print Assumptions st_B2_bl.
Print Assumptions st_P1_on.
Print Assumptions steps_C1.
Print Assumptions walk_WALK.
Print Assumptions walk_CL_marks.
Print Assumptions walk_CL_blank.
Print Assumptions walk_CG.
Print Assumptions step_B1.
Print Assumptions walk_B2.
Print Assumptions walk_P1.
Print Assumptions walk_P2.
Lemma trip_back_raw : forall n m e (c : sym) (Y L : list sym),
  run ctbl (2 * n + 2 * m + S e + 12)
    (mkConf P2 (ones n ++ bl :: L) on
      (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
         ++ on :: bl :: c :: Y)) =
  Some (mkConf R3
    (bl :: ones m ++ on :: on :: bl :: on :: bl :: ones m ++ on :: on
       :: zeros (S e) ++ bl :: ones (S n) ++ on :: L) c Y).
Proof.
  intros n m e c Y L.
  assert (H1 : run ctbl (n + 2)
      (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
           ++ on :: bl :: c :: Y)) =
      Some (mkConf P3 (on :: L) on
        (ones n ++ bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl
           :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite (walk_P2 n L
               (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl
                  :: ones (S m) ++ on :: bl :: c :: Y)).
    reflexivity. }
  assert (H2 : run ctbl (S (S n))
      (mkConf P3 (on :: L) on
        (ones n ++ bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl
           :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf P4 (bl :: ones (S n) ++ on :: L) bl
        (zeros e ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
           ++ on :: bl :: c :: Y))).
  { rewrite (walk_P3 n L
               (zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
                  ++ on :: bl :: c :: Y)).
    cbn [hd tl]. reflexivity. }
  assert (H3 : run ctbl (e + 2)
      (mkConf P4 (bl :: ones (S n) ++ on :: L) bl
        (zeros e ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
           ++ on :: bl :: c :: Y)) =
      Some (mkConf P5 (on :: zeros (S e) ++ bl :: ones (S n) ++ on :: L) on
        (ones m ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { change (run ctbl (e + 2)
      (mkConf P4 (bl :: ones (S n) ++ on :: L) bl
        (zeros e ++ on :: (ones (S m) ++ bl :: on :: bl :: ones (S m)
                             ++ on :: bl :: c :: Y))) =
      Some (mkConf P5 (on :: zeros (S e) ++ bl :: ones (S n) ++ on :: L) on
        (ones m ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y))).
    rewrite (walk_P4 e (bl :: ones (S n) ++ on :: L)
               (ones (S m) ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)).
    cbn [hd tl]. reflexivity. }
  assert (H4 : run ctbl (m + 2)
      (mkConf P5 (on :: zeros (S e) ++ bl :: ones (S n) ++ on :: L) on
        (ones m ++ bl :: on :: bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf BQ
        (bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) on (bl :: ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite (walk_P5 m
               (on :: zeros (S e) ++ bl :: ones (S n) ++ on :: L)
               (on :: bl :: ones (S m) ++ on :: bl :: c :: Y)).
    cbn [hd tl]. reflexivity. }
  assert (H5 : run ctbl 1
      (mkConf BQ
        (bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) on (bl :: ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf BW
        (on :: bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) bl (ones (S m) ++ on :: bl :: c :: Y))).
  { rewrite run_S, st_BQ_any. cbn [hd tl]. reflexivity. }
  assert (H6 : run ctbl 1
      (mkConf BW
        (on :: bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) bl (ones (S m) ++ on :: bl :: c :: Y)) =
      Some (mkConf R1
        (bl :: on :: bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) on (ones m ++ on :: bl :: c :: Y))).
  { rewrite run_S, st_BW_any. cbn [hd tl]. reflexivity. }
  assert (H7 : run ctbl 1
      (mkConf R1
        (bl :: on :: bl :: ones m ++ on :: on :: zeros (S e) ++ bl :: ones (S n)
           ++ on :: L) on (ones m ++ on :: bl :: c :: Y)) =
      Some (mkConf R2
        (on :: bl :: on :: bl :: ones m ++ on :: on :: zeros (S e)
           ++ bl :: ones (S n) ++ on :: L) on (ones m ++ bl :: c :: Y))).
  { rewrite run_S, st_R1_on. rewrite hd_ones_on, tl_ones_on. reflexivity. }
  assert (H8 : run ctbl (m + 2)
      (mkConf R2
        (on :: bl :: on :: bl :: ones m ++ on :: on :: zeros (S e)
           ++ bl :: ones (S n) ++ on :: L) on (ones m ++ bl :: c :: Y)) =
      Some (mkConf R3
        (bl :: ones m ++ on :: on :: bl :: on :: bl :: ones m ++ on :: on
           :: zeros (S e) ++ bl :: ones (S n) ++ on :: L) c Y)).
  { rewrite (walk_R2 m
               (on :: bl :: on :: bl :: ones m ++ on :: on :: zeros (S e)
                  ++ bl :: ones (S n) ++ on :: L) (c :: Y)).
    cbn [hd tl]. reflexivity. }
  replace (2 * n + 2 * m + S e + 12)
    with (n + 2 + (S (S n) + (e + 2 + (m + 2 + (1 + (1 + (1 + (m + 2))))))))
    by lia.
  eapply run_cat_c; [exact H1 | eapply run_cat_c; [exact H2 |
    eapply run_cat_c; [exact H3 | eapply run_cat_c; [exact H4 |
      eapply run_cat_c; [exact H5 | eapply run_cat_c; [exact H6 |
        eapply run_cat_c; [exact H7 | exact H8]]]]]]].
Qed.

(** The same run in the shape the next trip's frame takes: the two runs of
    marks written flush, the far end one blank shorter. *)

Lemma trip_back : forall n m e (c : sym) (Y L : list sym),
  run ctbl (2 * n + 2 * m + S e + 12)
    (mkConf P2 (ones n ++ bl :: L) on
      (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
         ++ on :: bl :: c :: Y)) =
  Some (mkConf R3
    (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m)) ++ zeros (S e)
       ++ bl :: ones (S (S n)) ++ L) c Y).
Proof.
  intros n m e c Y L.
  rewrite (trip_back_raw n m e c Y L). rewrite !ones_S_any. reflexivity.
Qed.

(** *** The whole trip *)

Lemma skipn_tl : forall (k : nat) (A : list sym), skipn (S k) A = tl (skipn k A).
Proof.
  intros k. induction k as [|k IH]; intros A.
  - destruct A; reflexivity.
  - destruct A as [|a A].
    + reflexivity.
    + cbn [skipn tl]. exact (IH A).
Qed.

(** The frame the return half hands back is the next trip's start frame. *)

Lemma trip_frame_next : forall n m e (c : sym) (Y A L : list sym),
  skipn (S m) A = bl :: L ->
  Some (mkConf R3
    (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m)) ++ zeros (S e)
       ++ bl :: ones (S (S n)) ++ L) c Y) =
  Some (mkConf R3 (trip_frame (S (S m)) (S e) (S n) A) c Y).
Proof.
  intros n m e c Y A L HA.
  change (Some (mkConf R3
            (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m))
               ++ zeros (S e) ++ bl :: ones (S (S n)) ++ L) c Y) =
          Some (mkConf R3
            (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m))
               ++ bl :: zeros (S e) ++ ones (S (S n)) ++ skipn (S (S m)) A)
            c Y)).
  rewrite (skipn_tl (S m) A), HA. cbn [tl]. rewrite zeros_swap. reflexivity.
Qed.

Lemma trip : forall n m e (c : sym) (Y A L : list sym),
  skipn (S m) A = bl :: L ->
  run ctbl (4 * m + 2 * S e + 2 * S n + 21)
    (mkConf R3 (trip_frame (S m) (S e) (S n) A) on (c :: Y)) =
  Some (mkConf R3 (trip_frame (S (S m)) (S e) (S n) A) c Y).
Proof.
  intros n m e c Y A L HA.
  assert (H1 : run ctbl (2 * m + S e + 11)
      (mkConf R3 (trip_frame (S m) (S e) (S n) A) on (c :: Y)) =
      Some (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
           ++ on :: bl :: c :: Y))).
  { unfold trip_frame. rewrite (trip_out_lit m (S e) (S n) c Y A).
    rewrite HA, tl_ones_app, hd_ones_app. reflexivity. }
  assert (H2 : run ctbl (2 * n + 2 * m + S e + 12)
      (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S e) ++ ones (S (S m)) ++ bl :: on :: bl :: ones (S m)
           ++ on :: bl :: c :: Y)) =
      Some (mkConf R3
        (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m))
           ++ zeros (S e) ++ bl :: ones (S (S n)) ++ L) c Y)).
  { exact (trip_back n m e c Y L). }
  assert (HR : run ctbl (4 * m + 2 * S e + 2 * S n + 21)
      (mkConf R3 (trip_frame (S m) (S e) (S n) A) on (c :: Y)) =
      Some (mkConf R3
        (bl :: ones (S (S m)) ++ bl :: on :: bl :: ones (S (S m))
           ++ zeros (S e) ++ bl :: ones (S (S n)) ++ L) c Y)).
  { replace (4 * m + 2 * S e + 2 * S n + 21)
      with (2 * m + S e + 11 + (2 * n + 2 * m + S e + 12)) by lia.
    eapply run_cat_c; [exact H1 | exact H2]. }
  rewrite HR. apply trip_frame_next. exact HA.
Qed.

(** *** The first trip: empty block, empty copy *)

(** [trip] is stated for [j = S m], so it does not cover the trip that runs from
    an empty block and an empty copy.  At [j = 0] the frame is
    [bl :: bl :: on :: bl :: bl], and the phase chain degenerates in three
    places: [CL] meets the wall's blank instead of a prefix mark, the block's
    single mark is written by [B2]'s own blank row, and on the way back [P5]
    lands on a blank while [R2] walks no marks at all. *)

Lemma trip0 : forall n d (c : sym) (Y L : list sym),
  run ctbl (2 * S d + 2 * S n + 17)
    (mkConf R3 (trip_frame 0 (S d) (S n) (bl :: L)) on (c :: Y)) =
  Some (mkConf R3 (trip_frame 1 (S d) (S n) (bl :: L)) c Y).
Proof.
  intros n d c Y L.
  change (run ctbl (2 * S d + 2 * S n + 17)
    (mkConf R3
      (bl :: bl :: on :: bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
      on (c :: Y)) =
  Some (mkConf R3 (trip_frame 1 (S d) (S n) (bl :: L)) c Y)).
  assert (H1 : run ctbl 1
      (mkConf R3
        (bl :: bl :: on :: bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
        on (c :: Y)) =
      Some (mkConf C1
        (bl :: bl :: bl :: on :: bl :: bl :: zeros (S d) ++ ones (S (S n))
           ++ bl :: L) c Y)).
  { rewrite run_S, st_R3_on. reflexivity. }
  assert (H2 : run ctbl 3
      (mkConf C1
        (bl :: bl :: bl :: on :: bl :: bl :: zeros (S d) ++ ones (S (S n))
           ++ bl :: L) c Y) =
      Some (mkConf CL
        (on :: bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
        bl (on :: bl :: c :: Y))).
  { rewrite (steps_C1
               (bl :: bl :: on :: bl :: bl :: zeros (S d) ++ ones (S (S n))
                  ++ bl :: L) c Y).
    cbn [tl hd]. reflexivity. }
  assert (H3 : run ctbl 1
      (mkConf CL (on :: bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
        bl (on :: bl :: c :: Y)) =
      Some (mkConf CG
        (bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L) on
        (bl :: on :: bl :: c :: Y))).
  { rewrite (walk_CL_blank
               (on :: bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
               (on :: bl :: c :: Y)).
    cbn [tl hd]. reflexivity. }
  assert (H4 : run ctbl 1
      (mkConf CG (bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L) on
        (bl :: on :: bl :: c :: Y)) =
      Some (mkConf B1
        (bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L) bl
        (on :: bl :: on :: bl :: c :: Y))).
  { rewrite (walk_CG_0 (bl :: bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L)
               (bl :: on :: bl :: c :: Y)).
    cbn [tl hd]. reflexivity. }
  assert (H5 : run ctbl 1
      (mkConf B1 (bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L) bl
        (on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf B2 (zeros (S d) ++ ones (S (S n)) ++ bl :: L) bl
        (bl :: on :: bl :: on :: bl :: c :: Y))).
  { rewrite (step_B1 (bl :: zeros (S d) ++ ones (S (S n)) ++ bl :: L) bl
               (on :: bl :: on :: bl :: c :: Y)).
    cbn [tl hd]. reflexivity. }
  assert (H6 : run ctbl 1
      (mkConf B2 (zeros (S d) ++ ones (S (S n)) ++ bl :: L) bl
        (bl :: on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf P1 (zeros d ++ ones (S (S n)) ++ bl :: L) bl
        (on :: bl :: on :: bl :: on :: bl :: c :: Y))).
  { rewrite run_S, st_B2_bl. rewrite tl_zeros_app, hd_zeros_app. reflexivity. }
  assert (H7 : run ctbl (S (S d))
      (mkConf P1 (zeros d ++ ones (S (S n)) ++ bl :: L) bl
        (on :: bl :: on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl :: c :: Y))).
  { change (run ctbl (S (S d))
      (mkConf P1
        (tl (zeros (S d) ++ on :: (ones (S n) ++ bl :: L)))
        (hd bl (zeros (S d) ++ on :: (ones (S n) ++ bl :: L)))
        (on :: bl :: on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl :: c :: Y))).
    rewrite (walk_P1 (S d) (ones (S n) ++ bl :: L)
               (on :: bl :: on :: bl :: on :: bl :: c :: Y)).
    cbn [tl hd]. rewrite tl_ones_app. reflexivity. }
  assert (H8 : run ctbl (n + 2)
      (mkConf P2 (ones n ++ bl :: L) on
        (bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf P3 (on :: L) on
        (ones n ++ bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl
           :: c :: Y))).
  { rewrite (walk_P2 n L
               (bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl :: c :: Y)).
    reflexivity. }
  assert (H9 : run ctbl (S (S n))
      (mkConf P3 (on :: L) on
        (ones n ++ bl :: zeros (S d) ++ on :: bl :: on :: bl :: on :: bl
           :: c :: Y)) =
      Some (mkConf P4 (bl :: ones (S n) ++ on :: L) bl
        (zeros d ++ on :: bl :: on :: bl :: on :: bl :: c :: Y))).
  { rewrite (walk_P3 n L
               (zeros (S d) ++ on :: bl :: on :: bl :: on :: bl :: c :: Y)).
    cbn [hd tl]. rewrite tl_zeros_app. reflexivity. }
  assert (H10 : run ctbl (d + 2)
      (mkConf P4 (bl :: ones (S n) ++ on :: L) bl
        (zeros d ++ on :: bl :: on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf P5 (on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L) bl
        (on :: bl :: on :: bl :: c :: Y))).
  { rewrite (walk_P4 d (bl :: ones (S n) ++ on :: L)
               (bl :: on :: bl :: on :: bl :: c :: Y)).
    cbn [hd tl]. reflexivity. }
  assert (H11 : run ctbl 1
      (mkConf P5 (on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L) bl
        (on :: bl :: on :: bl :: c :: Y)) =
      Some (mkConf BQ
        (bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L) on
        (bl :: on :: bl :: c :: Y))).
  { rewrite run_S, st_P5_bl. cbn [tl hd]. reflexivity. }
  assert (H12 : run ctbl 1
      (mkConf BQ (bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L) on
        (bl :: on :: bl :: c :: Y)) =
      Some (mkConf BW
        (on :: bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L) bl
        (on :: bl :: c :: Y))).
  { rewrite run_S, st_BQ_any. cbn [tl hd]. reflexivity. }
  assert (H13 : run ctbl 1
      (mkConf BW (on :: bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L)
        bl (on :: bl :: c :: Y)) =
      Some (mkConf R1
        (bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L)
        on (bl :: c :: Y))).
  { rewrite run_S, st_BW_any. cbn [tl hd]. reflexivity. }
  assert (H14 : run ctbl 1
      (mkConf R1
        (bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n) ++ on :: L)
        on (bl :: c :: Y)) =
      Some (mkConf R2
        (on :: bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n)
           ++ on :: L) bl (c :: Y))).
  { rewrite run_S, st_R1_on. cbn [tl hd]. reflexivity. }
  assert (H15 : run ctbl 1
      (mkConf R2
        (on :: bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n)
           ++ on :: L) bl (c :: Y)) =
      Some (mkConf R3
        (bl :: on :: bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n)
           ++ on :: L) c Y)).
  { rewrite run_S, st_R2_bl. cbn [hd tl]. reflexivity. }
  assert (H16 : run ctbl 1
      (mkConf R2
        (on :: bl :: on :: bl :: on :: zeros (S d) ++ bl :: ones (S n)
           ++ on :: L) bl (c :: Y)) =
      Some (mkConf R3 (trip_frame 1 (S d) (S n) (bl :: L)) c Y)).
  { rewrite H15. unfold trip_frame. cbn [ones skipn].
    rewrite zeros_swap, ones_S_any. reflexivity. }
  replace (2 * S d + 2 * S n + 17) with (1 + (3 + (1 + (1 + (1 + (1 + (S (S d) + (n + 2 + (S (S n) + (d + 2 + (1 + (1 + (1 + (1 + (1))))))))))))))) by lia.
  eapply run_cat_c; [exact H1 | eapply run_cat_c; [exact H2 |
    eapply run_cat_c; [exact H3 | eapply run_cat_c; [exact H4 |
      eapply run_cat_c; [exact H5 | eapply run_cat_c; [exact H6 |
        eapply run_cat_c; [exact H7 | eapply run_cat_c; [exact H8 |
          eapply run_cat_c; [exact H9 | eapply run_cat_c; [exact H10 |
            eapply run_cat_c; [exact H11 | eapply run_cat_c; [exact H12 |
              eapply run_cat_c; [exact H13 | eapply run_cat_c; [exact H14 |
                exact H16]]]]]]]]]]]]]].
Qed.

(** *** The sweep: v trips rebuild the block *)

(** A trip from frame [j] costs [4j + 2D + 2(S n) + 17] steps whatever [j] is:
    [trip0] at [j = 0] and [trip] at [j = S m] are the two cases of one count.
    So the sweep is an induction on the number of trips, and the total is a
    fixed-point sum over the frame index. *)

Fixpoint sweep_steps (v j d n : nat) : nat :=
  match v with
  | O => 0
  | S v' => 4 * j + 2 * S d + 2 * S n + 17 + sweep_steps v' (S j) d n
  end.

Lemma sweep_steps_closed : forall v j d n,
  sweep_steps v j d n = v * (4 * j + 2 * S d + 2 * S n + 15) + 2 * v * v.
Proof.
  intros v. induction v as [|v IH]; intros j d n.
  - reflexivity.
  - cbn [sweep_steps]. rewrite (IH (S j) d n). lia.
Qed.

Lemma skipn_zeros : forall k N, k <= N -> skipn k (zeros N) = zeros (N - k).
Proof.
  intros k. induction k as [|k IH]; intros N H.
  - destruct N; reflexivity.
  - destruct N as [|N]. { lia. }
    change (skipn k (zeros N) = zeros (S N - S k)).
    rewrite IH. { cbn [Nat.sub]. reflexivity. } lia.
Qed.

(** One trip, at any frame index, for a far context of blanks. *)
Lemma trip_step : forall j n d N (c : sym) (Y : list sym),
  j <= N ->
  run ctbl (4 * j + 2 * S d + 2 * S n + 17)
    (mkConf R3 (trip_frame j (S d) (S n) (zeros (S N))) on (c :: Y)) =
  Some (mkConf R3 (trip_frame (S j) (S d) (S n) (zeros (S N))) c Y).
Proof.
  intros j n d N c Y Hj. destruct j as [|j].
  - cbn [Nat.mul].
    change (run ctbl (2 * S d + 2 * S n + 17)
      (mkConf R3 (trip_frame 0 (S d) (S n) (bl :: zeros N)) on (c :: Y)) =
      Some (mkConf R3 (trip_frame 1 (S d) (S n) (bl :: zeros N)) c Y)).
    apply trip0.
  - replace (4 * S j + 2 * S d + 2 * S n + 17)
      with (4 * j + 2 * S d + 2 * S n + 21) by lia.
    rewrite (trip n j d c Y (zeros (S N)) (zeros (N - S j))).
    + cbn [Nat.sub]. reflexivity.
    + rewrite skipn_zeros by lia.
      replace (S N - S j) with (S (N - S j)) by lia.
      reflexivity.
Qed.

(** The sweep.  Starting from the first trip's frame -- empty block, empty copy,
    head on the source's first mark, [v] more marks behind it -- [v] trips leave
    the block [1^v], the copy [1^v], the budget [v] cells further left and the
    head on the blank after the source. *)
Theorem sweep : forall w j n d N (Z : list sym),
  j + S w <= N ->
  run ctbl (sweep_steps (S w) j d n)
    (mkConf R3 (trip_frame j (S d) (S n) (zeros (S N))) on (ones w ++ bl :: Z)) =
  Some (mkConf R3 (trip_frame (j + S w) (S d) (S n) (zeros (S N))) bl Z).
Proof.
  intros w. induction w as [|w IH]; intros j n d N Z H.
  - cbn [sweep_steps ones].
    replace (4 * j + 2 * S d + 2 * S n + 17 + 0)
      with (4 * j + 2 * S d + 2 * S n + 17) by lia.
    change (run ctbl (4 * j + 2 * S d + 2 * S n + 17)
      (mkConf R3 (trip_frame j (S d) (S n) (zeros (S N))) on (bl :: Z)) =
      Some (mkConf R3 (trip_frame (j + 1) (S d) (S n) (zeros (S N))) bl Z)).
    replace (j + 1) with (S j) by lia.
    apply (trip_step j n d N bl Z). lia.
  - cbn [sweep_steps ones].
    replace (j + S (S w)) with (S j + S w) by lia.
    assert (Ht : run ctbl (4 * j + 2 * S d + 2 * S n + 17)
        (mkConf R3 (trip_frame j (S d) (S n) (zeros (S N))) on
          (on :: ones w ++ bl :: Z)) =
        Some (mkConf R3 (trip_frame (S j) (S d) (S n) (zeros (S N))) on
          (ones w ++ bl :: Z))).
    { apply (trip_step j n d N on (ones w ++ bl :: Z)). lia. }
    eapply run_cat_c.
    + exact Ht.
    + apply IH. lia.
Qed.

Print Assumptions walk_P3.
Print Assumptions walk_P4.
Print Assumptions walk_P5.
Print Assumptions st_BQ_any.
Print Assumptions st_BW_any.
Print Assumptions walk_R2.
Print Assumptions trip_back_raw.
Print Assumptions trip_back.
Print Assumptions skipn_tl.
Print Assumptions trip_frame_next.
Print Assumptions trip.
Print Assumptions trip0.
Print Assumptions sweep_steps_closed.
Print Assumptions skipn_zeros.
Print Assumptions trip_step.
Print Assumptions sweep.
Print Assumptions zeros_swap.
Print Assumptions ones_swap.
Print Assumptions tl_ones_on.
Print Assumptions hd_ones_on.
Print Assumptions trip_out_lit.
Print Assumptions trip_out.
