(** * The doubling core: table and block-walk lemmas.

    Layout of a core run:

        0^inf  [C]  0  [U]  0  [W]  0^inf

    A "pass" consumes one cell of [C] and all of [U], appending two cells to
    [W].  Passes repeat until [C] is empty; the final tape is 0^inf [W] 0^inf.

    This file only proves the *block walk* lemmas: sweeps over a homogeneous
    block of cells, stated with a symbolic block length.  Composing them into a
    parametric pass lemma is future work; the machines in Machine1.v ..
    Machine3.v are certified by evaluating their concrete runs instead. *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
From Top Require Import TM.

(** ** The core table *)

Local Notation A := 0.   (* erase the leftmost cell of U *)
Local Notation T := 1.   (* test the cell right of the erased one *)
Local Notation F0 := 2.   (* sweep right over zeros *)
Local Notation F1 := 3.   (* sweep right over U's block *)
Local Notation F2 := 4.   (* sweep right over W's block *)
Local Notation G1 := 5.   (* write the second appended cell *)
Local Notation R1 := 6.   (* sweep left over W's block *)
Local Notation R2 := 7.   (* step over the one-cell gap and test *)
Local Notation R3 := 8.   (* sweep left over U's block *)
Local Notation R4 := 9.   (* (pass end) sweep left over zeros *)
Local Notation R5 := 10.  (* sweep left over C's block *)
Local Notation A2 := 11.  (* erase the leftmost cell of C *)
Local Notation T2 := 12.  (* test the cell right of the erased one *)
Local Notation N0 := 13.  (* sweep right over C's block *)
Local Notation N1 := 14.  (* sweep right over zeros up to U *)

Definition Tcore : table := fun s b =>
  match s, b with
  | 0,  on => Some (bl, true,  1)   (* A  : erase U's leftmost *)
  | 1,  on => Some (on, true,  3)   (* T  : more of U *)
  | 1,  bl => Some (bl, true,  2)   (* T  : U exhausted *)
  | 2,  bl => Some (bl, true,  2)   (* F0 : sweep right over zeros *)
  | 2,  on => Some (on, true,  4)
  | 3,  on => Some (on, true,  3)   (* F1 : sweep right over U *)
  | 3,  bl => Some (bl, true,  4)
  | 4,  on => Some (on, true,  4)   (* F2 : sweep right over W *)
  | 4,  bl => Some (on, true,  5)   (*      append the first cell *)
  | 5,  bl => Some (on, false, 6)   (* G1 : append the second cell *)
  | 6,  on => Some (on, false, 6)   (* R1 : sweep left over W *)
  | 6,  bl => Some (bl, false, 7)
  | 7,  on => Some (on, false, 8)   (* R2 : more of U *)
  | 7,  bl => Some (bl, false, 9)   (* R2 : U exhausted *)
  | 8,  on => Some (on, false, 8)   (* R3 : sweep left over U *)
  | 8,  bl => Some (bl, true,  0)
  | 9,  bl => Some (bl, false, 9)   (* R4 : sweep left over zeros *)
  | 9,  on => Some (on, false, 10)
  | 10, on => Some (on, false, 10)  (* R5 : sweep left over C *)
  | 10, bl => Some (bl, true,  11)
  | 11, on => Some (bl, true,  12)  (* A2 : erase C's leftmost *)
  | 12, on => Some (on, true,  13)  (* T2 : more of C *)
  (* 12, bl : halt *)
  | 13, on => Some (on, true,  13)  (* N0 : sweep right over C *)
  | 13, bl => Some (bl, true,  14)
  | 14, bl => Some (bl, true,  14)  (* N1 : sweep right over zeros *)
  | 14, on => Some (bl, true,  1)   (*    : erase U's leftmost *)
  | _,  _  => None
  end.

(** ** Block walk lemmas *)

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

(** One-transition lemmas. *)

Lemma st_F1_on : forall L R,
  step Tcore (mkConf F1 L on R) = Some (mkConf F1 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_F0_bl : forall L R,
  step Tcore (mkConf F0 L bl R) = Some (mkConf F0 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_F2_on : forall L R,
  step Tcore (mkConf F2 L on R) = Some (mkConf F2 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_R1_on : forall L R,
  step Tcore (mkConf R1 L on R) = Some (mkConf R1 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_R3_on : forall L R,
  step Tcore (mkConf R3 L on R) = Some (mkConf R3 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_R5_on : forall L R,
  step Tcore (mkConf R5 L on R) = Some (mkConf R5 (tl L) (hd bl L) (on :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_R4_bl : forall L R,
  step Tcore (mkConf R4 L bl R) = Some (mkConf R4 (tl L) (hd bl L) (bl :: R)).
Proof. intros. reflexivity. Qed.

Lemma st_N0_on : forall L R,
  step Tcore (mkConf N0 L on R) = Some (mkConf N0 (on :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma st_N1_bl : forall L R,
  step Tcore (mkConf N1 L bl R) = Some (mkConf N1 (bl :: L) (hd bl R) (tl R)).
Proof. intros. reflexivity. Qed.

Lemma walk_F1 : forall n L R,
  run Tcore (S n) (mkConf F1 L on (ones n ++ bl :: R)) =
  Some (mkConf F1 (ones (S n) ++ L) bl R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_F1_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_F2 : forall n L R,
  run Tcore (S n) (mkConf F2 L on (ones n ++ bl :: R)) =
  Some (mkConf F2 (ones (S n) ++ L) bl R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_F2_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_F0 : forall n L R,
  run Tcore (S n) (mkConf F0 L bl (zeros n ++ on :: R)) =
  Some (mkConf F0 (zeros (S n) ++ L) on R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_F0_bl. cbn [hd tl zeros repeat app]. rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.

Lemma walk_R1 : forall n L R,
  run Tcore (S n) (mkConf R1 (ones n ++ bl :: L) on R) =
  Some (mkConf R1 L bl (ones n ++ on :: R)).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_R1_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_R3 : forall n L R,
  run Tcore (S n) (mkConf R3 (ones n ++ bl :: L) on R) =
  Some (mkConf R3 L bl (ones n ++ on :: R)).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_R3_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_R5 : forall n L R,
  run Tcore (S n) (mkConf R5 (ones n ++ bl :: L) on R) =
  Some (mkConf R5 L bl (ones n ++ on :: R)).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_R5_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_R4 : forall n L R,
  run Tcore (S n) (mkConf R4 (zeros n ++ on :: L) bl R) =
  Some (mkConf R4 L on (zeros (S n) ++ R)).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_R4_bl. cbn [hd tl zeros repeat app]. rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.

Lemma walk_N0 : forall n L R,
  run Tcore (S n) (mkConf N0 L on (ones n ++ bl :: R)) =
  Some (mkConf N0 (ones (S n) ++ L) bl R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_N0_on. cbn [hd tl ones repeat app]. rewrite IH.
    rewrite ones_succ. reflexivity.
Qed.

Lemma walk_N1 : forall n L R,
  run Tcore (S n) (mkConf N1 L bl (zeros n ++ on :: R)) =
  Some (mkConf N1 (zeros (S n) ++ L) on R).
Proof.
  intros n. induction n as [|n IH]; intros L R.
  - reflexivity.
  - rewrite run_S, st_N1_bl. cbn [hd tl zeros repeat app]. rewrite IH.
    rewrite zeros_succ. reflexivity.
Qed.
