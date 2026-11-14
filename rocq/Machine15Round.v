(** * Machine 15: the symbolic H..O writer round.

    The local lemmas in [Machine15Outer] are concrete.  This file proves the
    parametric round:

      writer_ctx :  M on 1^(3*S k)   -> (011)^(S k),  3*S k steps
      entry_ctx  :  H on 1^(3k+2)   -> 0 1 (011)^k,  3k+2 steps

    [round_13] is the 38-cell entry instance: the prefix 0 1 plus twelve
    triples, 38 steps;
    [round_40] is the 40-cell block that encodes the 13 loop count;
    [round_42] is the exact 42-bit block [1^40 0 1] with arbitrary left
    and right field-stack contexts.  After 40 steps it is on the [14/0] row;
    the continuation variant's 41st step writes the separator 1, moves onto
    the trailing 1, and enters state H (7).  The theorem is about the literal
    [tbl]; it does not assert f_{w*2}(13). *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Machine15 Machine15Outer.
Import ListNotations.

(** ** List arithmetic for the writer *)

Lemma chain_S : forall k, chain (S k) = tok ++ chain k.
Proof. intros k. unfold chain. reflexivity. Qed.

Lemma rev_append3 : forall (a b c : list sym),
  rev (a ++ b ++ c) = rev c ++ rev b ++ rev a.
Proof.
  intros. rewrite rev_app_distr, rev_app_distr, app_assoc. reflexivity.
Qed.

Lemma rev_append3_ctx : forall (a b c clft : list sym),
  rev c ++ (rev (a ++ b) ++ clft) = rev (a ++ b ++ c) ++ clft.
Proof.
  intros. rewrite rev_append3, rev_app_distr, app_assoc. reflexivity.
Qed.

Lemma hd_ones_S : forall n, hd bl (ones (S n)) = on.
Proof. intros n. reflexivity. Qed.

Lemma tl_ones_S : forall n, tl (ones (S n)) = ones n.
Proof. intros n. reflexivity. Qed.

Lemma hd_ones_pos : forall n, 0 < n -> hd bl (ones n) = on.
Proof. intros [|n] H; [lia|reflexivity]. Qed.

Lemma tl_ones_pos : forall n, 0 < n -> tl (ones n) = ones (n - 1).
Proof. intros [|n] H; [lia|simpl; rewrite Nat.sub_0_r; reflexivity]. Qed.

Lemma hd_ones_app : forall n crgt, 0 < n -> hd bl (ones n ++ crgt) = on.
Proof. intros [|n] crgt H; [lia|reflexivity]. Qed.

Lemma tl_ones_app : forall n crgt, 0 < n ->
  tl (ones n ++ crgt) = ones (n - 1) ++ crgt.
Proof.
  intros [|n] crgt H; [lia|simpl; rewrite Nat.sub_0_r; reflexivity].
Qed.

Lemma ones_3S : forall k, ones (3 * S k + 1) = on :: ones (3 * S k).
Proof.
  intro k. replace (3 * S k + 1) with (S (3 * S k)) by lia.
  reflexivity.
Qed.

Lemma ones_3SS : forall k, ones (3 * S (S k) - 1) = on :: on :: ones (3 * S k).
Proof.
  intro k. replace (3 * S (S k) - 1) with (S (S (3 * S k))) by lia.
  reflexivity.
Qed.

(** ** One triple, with both tape contexts *)

Lemma triple_ctx : forall clft crgt,
  run tbl 3 (mkConf 12 clft on (on :: on :: crgt)) =
  Some (mkConf 12 (rev tok ++ clft) (hd bl crgt) (tl crgt)).
Proof. intros. vm_compute. reflexivity. Qed.

(** ** The H entry, with both tape contexts *)

Lemma pair_ctx : forall clft crgt,
  run tbl 2 (mkConf 7 clft on (on :: crgt)) =
  Some (mkConf 12 (rev [bl; on] ++ clft) (hd bl crgt) (tl crgt)).
Proof. intros. vm_compute. reflexivity. Qed.

(** The two-cell tail after the 38-cell entry. *)
Lemma pair_tail_ctx : forall clft crgt,
  run tbl 2 (mkConf 12 clft on (on :: crgt)) =
  Some (mkConf 14 (rev [bl; on] ++ clft) (hd bl crgt) (tl crgt)).
Proof. intros. vm_compute. reflexivity. Qed.

(** ** The parametric writer round *)

Lemma writer_ctx : forall k clft,
  run tbl (3 * S k) (mkConf 12 clft on (ones (3 * S k - 1))) =
  Some (mkConf 12 (rev (chain (S k)) ++ clft) bl []).
Proof.
  induction k as [|k IH]; intros clft.
  - change (run tbl 3 (mkConf 12 clft on (on :: on :: [])) =
            Some (mkConf 12 (rev tok ++ clft) bl [])).
    rewrite (triple_ctx clft []). reflexivity.
  - rewrite ones_3SS.
    replace (3 * S (S k)) with (3 + 3 * S k) by lia.
    rewrite run_add.
    rewrite (triple_ctx clft (ones (3 * S k))).
    rewrite (hd_ones_pos (3 * S k)) by lia.
    rewrite (tl_ones_pos (3 * S k)) by lia.
    rewrite (IH (rev tok ++ clft)).
    replace (rev (chain (S (S k))) ++ clft)
      with (rev (chain (S k)) ++ (rev tok ++ clft)).
    + reflexivity.
    + rewrite (chain_S (S k)).
      rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(** ** The same writer with an arbitrary trailing tape *)

Lemma writer_ctx_suffix : forall k clft crgt,
  run tbl (3 * S k) (mkConf 12 clft on (ones (3 * S k - 1) ++ crgt)) =
  Some (mkConf 12 (rev (chain (S k)) ++ clft) (hd bl crgt) (tl crgt)).
Proof.
  induction k as [|k IH]; intros clft crgt.
  - change (run tbl 3 (mkConf 12 clft on (on :: on :: crgt)) =
            Some (mkConf 12 (rev tok ++ clft) (hd bl crgt) (tl crgt))).
    rewrite (triple_ctx clft crgt). reflexivity.
  - rewrite ones_3SS.
    replace (3 * S (S k)) with (3 + 3 * S k) by lia.
    change (run tbl (3 + 3 * S k)
      (mkConf 12 clft on (on :: on :: (ones (3 * S k) ++ crgt))) =
      Some (mkConf 12 (rev (chain (S (S k))) ++ clft)
        (hd bl crgt) (tl crgt))).
    rewrite run_add.
    rewrite (triple_ctx clft (ones (3 * S k) ++ crgt)).
    rewrite (hd_ones_app (3 * S k) crgt) by lia.
    rewrite (tl_ones_app (3 * S k) crgt) by lia.
    rewrite (IH (rev tok ++ clft) crgt).
    replace (rev (chain (S (S k))) ++ clft)
      with (rev (chain (S k)) ++ (rev tok ++ clft)).
    + reflexivity.
    + rewrite (chain_S (S k)).
      rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(** ** The parametric entry round *)

Lemma entry_ctx : forall k clft,
  run tbl (3 * k + 2) (mkConf 7 clft on (ones (3 * k + 1))) =
  Some (mkConf 12 (rev ([bl; on] ++ chain k) ++ clft) bl []).
Proof.
  intros [|k] clft.
  - change (run tbl 2 (mkConf 7 clft on (on :: [])) =
            Some (mkConf 12 (rev [bl; on] ++ clft) bl [])).
    rewrite (pair_ctx clft []). reflexivity.
  - replace (3 * S k + 2) with (2 + 3 * S k) by lia.
    rewrite run_add.
    rewrite ones_3S.
    rewrite (pair_ctx clft (ones (3 * S k))).
    rewrite (hd_ones_pos (3 * S k)) by lia.
    rewrite (tl_ones_pos (3 * S k)) by lia.
    rewrite (writer_ctx k (rev [bl; on] ++ clft)).
    rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

(** ** The same entry with an arbitrary trailing tape *)

Lemma entry_ctx_suffix : forall k clft crgt,
  run tbl (3 * k + 2) (mkConf 7 clft on (ones (3 * k + 1) ++ crgt)) =
  Some (mkConf 12 (rev ([bl; on] ++ chain k) ++ clft)
    (hd bl crgt) (tl crgt)).
Proof.
  intros [|k] clft crgt.
  - change (run tbl 2 (mkConf 7 clft on (on :: crgt)) =
            Some (mkConf 12 (rev [bl; on] ++ clft)
              (hd bl crgt) (tl crgt))).
    rewrite (pair_ctx clft crgt). reflexivity.
  - replace (3 * S k + 2) with (2 + 3 * S k) by lia.
    rewrite ones_3S.
    change (run tbl (2 + 3 * S k)
      (mkConf 7 clft on (on :: (ones (3 * S k) ++ crgt))) =
      Some (mkConf 12 (rev ([bl; on] ++ chain (S k)) ++ clft)
        (hd bl crgt) (tl crgt))).
    rewrite run_add.
    rewrite (pair_ctx clft (ones (3 * S k) ++ crgt)).
    rewrite (hd_ones_app (3 * S k) crgt) by lia.
    rewrite (tl_ones_app (3 * S k) crgt) by lia.
    rewrite (writer_ctx_suffix k (rev [bl; on] ++ clft) crgt).
    rewrite rev_app_distr, app_assoc. reflexivity.
Qed.

Lemma entry_12_suffix : forall clft crgt,
  run tbl 38 (mkConf 7 clft on (ones 37 ++ crgt)) =
  Some (mkConf 12 (rev ([bl; on] ++ chain 12) ++ clft)
    (hd bl crgt) (tl crgt)).
Proof. intros. apply (entry_ctx_suffix 12 clft crgt). Qed.

(** ** The 38-cell entry instance: 0 1 plus twelve triples, 38 steps *)

Lemma round_13 :
  run tbl 38 (mkConf 7 [] on (ones 37)) =
  Some (mkConf 12 (rev ([bl; on] ++ chain 12)) bl []).
Proof. apply (entry_ctx 12 []). Qed.

(** ** The 40-cell block: 13 loops, 40 cells, 40 steps to the [14/0] row *)

Lemma round_40 :
  run tbl 40 (mkConf 7 [] on (ones 39)) =
  Some (mkConf 14 (rev ([bl; on] ++ chain 12 ++ [bl; on])) bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma o_zero_next : forall clft crgt,
  step tbl (mkConf 14 clft bl crgt) =
  Some (mkConf 7 (on :: clft) (hd bl crgt) (tl crgt)).
Proof. intros. reflexivity. Qed.

Lemma round_40_next :
  step tbl (mkConf 14 (rev ([bl; on] ++ chain 12 ++ [bl; on])) bl []) =
  Some (mkConf 7
    (on :: rev ([bl; on] ++ chain 12 ++ [bl; on])) bl []).
Proof. apply o_zero_next. Qed.

(** ** The exact 42-bit block: 1^40 0 1 *)

Lemma round_40_suffix : forall clft crgt,
  run tbl 40 (mkConf 7 clft on (ones 39 ++ crgt)) =
  Some (mkConf 14 (rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    (hd bl crgt) (tl crgt)).
Proof.
  intros clft crgt.
  assert (Hsplit : ones 39 ++ crgt = ones 37 ++ (ones 2 ++ crgt)).
  { replace (ones 39) with (ones 37 ++ ones 2) by
      (rewrite <- ones_app; replace (37 + 2) with 39 by lia; reflexivity).
    rewrite app_assoc. reflexivity. }
  rewrite Hsplit.
  replace 40 with (38 + 2) by lia.
  rewrite run_add.
  rewrite (entry_12_suffix clft (ones 2 ++ crgt)).
  replace (hd bl (ones 2 ++ crgt)) with on by reflexivity.
  replace (tl (ones 2 ++ crgt)) with (on :: crgt) by reflexivity.
  rewrite (pair_tail_ctx (rev ([bl; on] ++ chain 12) ++ clft) crgt).
  rewrite rev_append3_ctx. reflexivity.
Qed.

Lemma round_42 : forall clft crgt,
  run tbl 40
    (mkConf 7 clft on (ones 39 ++ [bl; on] ++ crgt)) =
  Some (mkConf 14 (rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    bl (on :: crgt)).
Proof.
  intros clft crgt.
  apply (round_40_suffix clft ([bl; on] ++ crgt)).
Qed.

Lemma round_42_next : forall clft crgt,
  step tbl (mkConf 14 (rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    bl (on :: crgt)) =
  Some (mkConf 7
    (on :: rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    on crgt).
Proof. intros. apply o_zero_next. Qed.

Lemma round_42_next_run : forall clft crgt,
  run tbl 41
    (mkConf 7 clft on (ones 39 ++ [bl; on] ++ crgt)) =
  Some (mkConf 7
    (on :: rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    on crgt).
Proof.
  intros clft crgt.
  replace 41 with (40 + 1) by lia.
  rewrite run_add, (round_42 clft crgt).
  cbn [run].
  rewrite (round_42_next clft crgt). reflexivity.
Qed.

(** Entering the first field of the next 13-field stack: after the
    [41]-step round, H crosses the separator [0] and reaches the first
    [1] of the next field.  The remaining fields stay in [rest]. *)
Lemma round_42_enter_field : forall clft rest,
  run tbl 43
    (mkConf 7 clft on
      (ones 39 ++ [bl; on] ++ (bl :: on :: on :: rest))) =
  Some (mkConf 7
    (on :: bl :: on :: rev ([bl; on] ++ chain 12 ++ [bl; on]) ++ clft)
    on (on :: rest)).
Proof.
  intros clft rest.
  replace 43 with (41 + 2) by lia.
  rewrite run_add, (round_42_next_run clft (bl :: on :: on :: rest)).
  cbn [run]. reflexivity.
Qed.

(** ** The leftward output-growth phase

    After [round_42_enter_field] the writer finishes the first field, then
    the A/G pass sweeps left through the output and the F/B/C/D loop lays
    down a new left block.  The complete first phase ends here: state H on
    the new blank, with the output extended from 43 to the 52-cell prefix
    below and an empty left context.  The remaining field stack [rest] is
    untouched. *)

Definition output_growth_prefix : list sym :=
  [on; on; on; on; on; on; bl; on; bl; on; on; bl; on;
   on; bl; on; on; bl; on; on; bl; on; on; bl; on; on;
   bl; on; on; bl; on; on; bl; on; on; bl; on; on; bl;
   on; on; bl; on; on; bl; on; bl; on; bl; bl; on; on].

Lemma output_growth_phase : forall rest,
  run tbl 62
    (mkConf 7
      (on :: bl :: on :: rev ([bl; on] ++ chain 12 ++ [bl; on]))
      on (on :: bl :: on :: on :: rest)) =
  Some (mkConf 7 [] bl (output_growth_prefix ++ rest)).
Proof. intros. vm_compute. reflexivity. Qed.

Print Assumptions writer_ctx.
Print Assumptions entry_ctx.
Print Assumptions round_13.
Print Assumptions round_40.
Print Assumptions round_40_next.
Print Assumptions writer_ctx_suffix.
Print Assumptions entry_ctx_suffix.
Print Assumptions round_40_suffix.
Print Assumptions round_42.
Print Assumptions round_42_next.
Print Assumptions round_42_next_run.
Print Assumptions round_42_enter_field.
Print Assumptions output_growth_phase.
