(** * Holdout #758: the no-overshoot crossing lemma.

    Let [step : nat -> option nat] send a chain start [A(1,c)] to the next
    chain start [A(1,c')], with [None] meaning the chain halts.  This file
    proves the combinatorial fact behind the proposed halting proof:

    If every [c < H] has [step c = Some (next c)] with [c < next c <= H],
    and [next H = H], then the orbit of [1] under [next] reaches [H].
    Consequently, if [step H = None], the machine halts.

    The analytic/computational obligation is exactly the hypothesis
    [forall c, c < H -> exists c', step c = Some c' /\ c < c' /\ c' <= H];
    this file isolates it. *)

From Stdlib Require Import Arith Lia Classical.

(** [iter next n x] applies [next] exactly [n] times to [x]. *)
Fixpoint iter (next : nat -> nat) (n : nat) (x : nat) : nat :=
  match n with
  | 0 => x
  | S k => next (iter next k x)
  end.

(** ** An infinite strictly increasing sequence bounded by [H] is impossible. *)
Lemma no_infinite_strict_mono_bounded (H : nat) (u : nat -> nat)
    (hmono : forall n, u n < u (S n)) (hub : forall n, u n <= H) : False.
Proof.
  assert (hge : forall n, u 0 + n <= u n).
  { intro n. induction n as [|n ih].
    - lia.
    - specialize (hmono n). lia. }
  specialize (hge (H + 1)).
  specialize (hub (H + 1)).
  lia.
Qed.

(** The orbit stays below [H]. *)
Lemma iter_le (next : nat -> nat) (H : nat) (h1 : 1 <= H)
    (hstep : forall c, c < H -> c < next c /\ next c <= H)
    (hfix : next H = H) :
    forall n, iter next n 1 <= H.
Proof.
  intro n. induction n as [|n ih]; simpl.
  - exact h1.
  - destruct (Nat.lt_ge_cases (iter next n 1) H) as [hlt | hge].
    + exact (proj2 (hstep _ hlt)).
    + assert (heq : iter next n 1 = H) by lia.
      rewrite heq, hfix. apply le_n.
Qed.

(** ** Orbit reaches the halting point. *)
Theorem reaches_of_no_overshoot (next : nat -> nat) (H : nat)
    (h1 : 1 <= H)
    (hstep : forall c, c < H -> c < next c /\ next c <= H)
    (hfix : next H = H) :
    exists n, iter next n 1 = H.
Proof.
  destruct (classic (exists n, iter next n 1 = H)) as [h | h].
  - exact h.
  - exfalso.
    assert (hlt : forall n, iter next n 1 < H).
    { intro n. pose proof (iter_le next H h1 hstep hfix n).
      destruct (Nat.lt_ge_cases (iter next n 1) H) as [hh | hh]; auto.
      exfalso. apply h. exists n. lia. }
    apply (no_infinite_strict_mono_bounded H (fun n => iter next n 1)).
    + intro n. simpl. exact (proj1 (hstep (iter next n 1) (hlt n))).
    + intro n. exact (iter_le next H h1 hstep hfix n).
Qed.

(** ** No-overshoot halting criterion. *)
Corollary halts_of_no_overshoot (step : nat -> option nat) (next : nat -> nat)
    (H : nat) (h1 : 1 <= H) (hH : step H = None)
    (hnext : forall c, c < H ->
      step c = Some (next c) /\ c < next c /\ next c <= H)
    (hfix : next H = H) :
    exists n, step (iter next n 1) = None.
Proof.
  destruct (reaches_of_no_overshoot next H h1
    (fun c hc => let Hs := hnext c hc in
                 conj (proj1 (proj2 Hs)) (proj2 (proj2 Hs))) hfix)
    as [n hn].
  exists n. rewrite hn. exact hH.
Qed.

(** ** Sanity check: a tiny map that increases until the fixed point [3]. *)
Definition demoNext (c : nat) : nat := if Nat.eqb c 3 then 3 else c + 1.
Definition demoStep (c : nat) : option nat :=
  if Nat.eqb c 3 then None else Some (c + 1).

Example demo : exists n, demoStep (iter demoNext n 1) = None.
Proof.
  apply (halts_of_no_overshoot demoStep demoNext 3).
  - lia.
  - reflexivity.
  - intros c hc.
    assert (hc3 : (c =? 3) = false) by (apply Nat.eqb_neq; lia).
    unfold demoStep, demoNext.
    rewrite hc3. simpl. split; [reflexivity | split]; lia.
  - unfold demoNext. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Print the checked statements. *)
Check reaches_of_no_overshoot.
Check halts_of_no_overshoot.
Check demo.
Print Assumptions halts_of_no_overshoot.
