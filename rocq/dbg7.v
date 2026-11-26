(** * fe0_5: the descent, stated on the machine's own measure

    The (1,3) run visits [1^a 4 W] with [W = rep c k = (2233)^c (23)^k].
    A round (one increment of [a]) is either

      - a pop:      [(a, c, k+1) -> (a+1, c, k)], or
      - a level:    [(a, c+1, 0) -> (a+1, c, level c)],

    and the machine halts exactly at [c = k = 0].

    This file:

      - defines the notation [rep], the configuration and the round;
      - proves [rep_halts] by nested induction on the configuration itself
        (no abstract well-founded order, no re-indexing);
      - formalises the 17-state machine and checks the round against it by
        computation: [round_c303_c310] is the A-to-A round of the run, and
        [halt_13] is the whole 15,981-step halting run, both kernel-checked.

    What is still open is the *parametric* statement that the machine
    implements a pop/level round for every [a, c, k]; the per-round machine
    facts proved here are instances, not the general law. *)

From Stdlib Require Import Arith PeanoNat Lia List.
Import ListNotations.

(** ** 1. The word as a binary counter *)

Inductive sy := S0 | S1 | S2 | S3 | S4.

Definition word := list sy.

Definition bit (x : sy) : nat :=
  match x with
  | S2 => 0
  | S3 => 1
  | _ => 0
  end.

Fixpoint val_aux (acc : nat) (w : word) : nat :=
  match w with
  | nil => acc
  | s :: r => val_aux (2 * acc + bit s) r
  end.

Definition val (w : word) : nat := val_aux 0 w.

Lemma val_aux_app1 : forall acc w s,
    val_aux acc (w ++ [s]) = 2 * val_aux acc w + bit s.
Proof.
  intros acc w. revert acc.
  induction w as [|a r IH]; intros acc s.
  - simpl. lia.
  - simpl. apply IH.
Qed.

Lemma val_app1 : forall w s, val (w ++ [s]) = 2 * val w + bit s.
Proof.
  intros w s. unfold val. apply val_aux_app1.
Qed.

Lemma val_pop : forall w, val (w ++ [S2; S3]) = 4 * val w + 1.
Proof.
  intros w.
  assert (E : w ++ [S2; S3] = (w ++ [S2]) ++ [S3]).
  { apply (app_assoc w [S2] [S3]). }
  rewrite E. clear E.
  rewrite val_app1, val_app1.
  simpl. lia.
Qed.

Lemma val_round : forall w, Nat.div (val (w ++ [S2; S3])) 4 = val w.
Proof.
  intros w. rewrite val_pop.
  symmetry. apply Nat.div_unique with (q := val w) (r := 1); lia.
Qed.

Lemma val_round_lt : forall w, val w < val (w ++ [S2; S3]).
Proof.
  intros w. rewrite val_pop. lia.
Qed.

(** ** 2. The notation [rep c k] = (2233)^c (23)^k *)

Definition blk : word := [S2; S2; S3; S3].
Definition pr : word := [S2; S3].

Definition rep (c k : nat) : word := concat (repeat blk c) ++ concat (repeat pr k).

(** A configuration of the notation: [a] ones, then [4], then [rep c k]. *)
Record conf := mkConf { ca : nat; cc : nat; ck : nat }.

Section Level.

(** [level c] is the counter the machine installs when level [c+1] collapses
    to level [c]; the trace gives [level 1 = 8], [level 0 = 18].  The
    termination proof works for any [level]. *)
Variable level : nat -> nat.

Definition rstep (x : conf) : conf :=
  match x with
  | mkConf a c k =>
    match k with
    | S k' => mkConf (S a) c k'
    | 0 => match c with
           | S c' => mkConf (S a) c' (level c')
           | 0 => mkConf a 0 0
           end
    end
  end.

Definition done (x : conf) : bool :=
  match x with
  | mkConf _ c k => andb (Nat.eqb c 0) (Nat.eqb k 0)
  end.

Fixpoint rrun (n : nat) (x : conf) : conf :=
  match n with
  | 0 => x
  | S m => rrun m (rstep x)
  end.

(** Every round either pops the counter or drops a level. *)
Lemma rstep_pop : forall a c k,
    rstep (mkConf a c (S k)) = mkConf (S a) c k.
Proof. reflexivity. Qed.

Lemma rstep_level : forall a c,
    rstep (mkConf a (S c) 0) = mkConf (S a) c (level c).
Proof. reflexivity. Qed.

Lemma rstep_done : rstep (mkConf 0 0 0) = mkConf 0 0 0.
Proof. reflexivity. Qed.

(** ** The halting theorem, on the configuration itself *)

Lemma rep_halts_k :
  forall c a k, exists n, done (rrun n (mkConf a c k)) = true.
Proof.
  induction c as [|c IH].
  - intros a k. revert a. induction k as [|k IHk]; intros a.
    + exists 0. reflexivity.
    + destruct (IHk (S a)) as [n Hn]. exists (S n). simpl. exact Hn.
  - intros a k. revert a. induction k as [|k IHk]; intros a.
    + destruct (IH (S a) (level c)) as [n Hn]. exists (S n). simpl. exact Hn.
    + destruct (IHk (S a)) as [n Hn]. exists (S n). simpl. exact Hn.
Qed.

Theorem rep_halts :
  forall a c k, exists n, done (rrun n (mkConf a c k)) = true.
Proof.
  intros a c k. apply (rep_halts_k c a k).
Qed.

End Level.

(** ** 3. The 17-state machine *)

Inductive st := A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q
              | HALT.

Definition idx (x : sy) : nat :=
  match x with S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3 | S4 => 4 end.

(** [delta s x] is the table: write, direction ([true] = right), next state.
    [B] on [0] is the [1RZ] halt, encoded as a move into [HALT]. *)
Definition delta (s : st) (x : sy) : option (sy * bool * st) :=
  nth (idx x)
    (match s with
     | A => [None; None; Some (S0, true, F); Some (S0, true, D);
             Some (S1, false, Q)]
     | B => [Some (S1, true, HALT); Some (S1, true, B); Some (S2, false, C);
             None; None]
     | C => [Some (S0, false, I); Some (S4, true, C); Some (S2, true, C);
             Some (S3, true, C); Some (S2, true, C)]
     | D => [Some (S1, false, E); Some (S1, true, D); Some (S2, true, D);
             Some (S3, true, D); None]
     | E => [Some (S3, false, A); Some (S1, false, E); Some (S2, false, E);
             Some (S3, false, E); None]
     | F => [Some (S0, false, G); Some (S1, true, F); Some (S2, true, F);
             Some (S3, true, F); None]
     | G => [Some (S0, true, I); Some (S0, false, H); None;
             Some (S3, true, I); None]
     | H => [Some (S2, false, A); Some (S1, false, H); Some (S2, false, H);
             Some (S3, false, H); None]
     | I => [Some (S3, true, N); None; Some (S0, false, A);
             Some (S0, false, I); None]
     | J => [Some (S2, true, O); None; Some (S2, false, J);
             Some (S3, false, J); None]
     | K => [Some (S2, false, L); None; Some (S2, true, K); Some (S3, true, K);
             Some (S4, true, K)]
     | L => [Some (S3, true, O); Some (S2, true, O); Some (S2, false, L);
             Some (S3, false, L); Some (S4, false, L)]
     | M => [Some (S3, false, L); None; Some (S2, true, M); Some (S3, true, M);
             Some (S4, true, M)]
     | N => [Some (S4, false, J); Some (S1, false, N); Some (S2, false, N);
             Some (S3, false, N); Some (S1, false, O)]
     | O => [Some (S1, true, B); Some (S4, true, P); Some (S1, true, K);
             Some (S0, true, M); Some (S4, false, N)]
     | P => [Some (S4, false, J); Some (S1, true, P); Some (S2, true, P);
             Some (S3, true, P); Some (S0, true, P)]
     | Q => [Some (S1, true, B); Some (S1, false, Q); Some (S2, false, Q);
             Some (S3, false, Q); Some (S1, false, Q)]
     | HALT => [None; None; None; None; None]
     end) None.

Definition cfg := (st * word * word)%type.

(** Tape as (state, left cells reversed, head :: right). *)
Definition step (c : cfg) : option cfg :=
  match c with
  | (s, l, r) =>
    match r with
    | [] => None
    | x :: r' =>
      match delta s x with
      | None => None
      | Some (y, d, s') =>
        if d then
          match r' with
          | [] => Some (s', y :: l, [S0])
          | z :: t => Some (s', y :: l, z :: t)
          end
        else
          match l with
          | [] => Some (s', [], S0 :: y :: r')
          | z :: l' => Some (s', l', z :: y :: r')
          end
      end
    end
  end.

Fixpoint runN (n : nat) (c : cfg) : option cfg :=
  match n with
  | 0 => Some c
  | S m => match step c with None => None | Some c' => runN m c' end
  end.

(** ** 4. The machine checked against the trace *)

(** The (1,3) start: [1^1 B> 2^3]. *)
Definition init13 : cfg := (B, [S1], [S2; S2; S2]).

(** Two consecutive A-visits of the run (steps 303 and 310), transcribed
    from the trace. *)
Definition c303 : cfg :=
  (A, [S2;S3;S2;S3;S3;S2;S2;S3;S3;S2;S2;S4;S1;S1;S1], [S3;S2;S3]).

Definition c310 : cfg :=
  (A, [S3;S2;S3;S3;S2;S2;S3;S3;S2;S2;S4;S1;S1;S1], [S2;S3;S2;S3;S1]).

(** One round of the machine, kernel-checked: seven steps take [c303] to
    [c310].  This is the machine side of the round law, and it is a theorem
    about the 17-state table, not a simulation log. *)
Theorem round_c303_c310 : runN 7 c303 = Some c310.
Proof. vm_compute. reflexivity. Qed.

(** The whole (1,3) run halts: at step 15,981 the machine has entered
    [HALT] (the [1RZ] move), and one more step is undefined. *)
Theorem halt_13 : exists l r, runN 15981 init13 = Some (HALT, l, r).
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

Theorem halt_13_stops : runN 15982 init13 = None.
Proof. vm_compute. reflexivity. Qed.

(** The score: 39 ones on the tape at the halt. *)
Definition count1 (w : word) : nat :=
  fold_right (fun x n => match x with S1 => S n | _ => n end) 0 w.

Theorem score_13 : exists l r,
    runN 15981 init13 = Some (HALT, l, r) /\ count1 (l ++ r) = 39.
Proof. vm_compute. do 2 eexists. split; reflexivity. Qed.


(** ** 5. Walk lemmas: the sweeps over [1^a] and over the word

    Each sweep is a run over a homogeneous block in one direction.  These are
    parametric in the block, so they apply to [1^a] and to [(2233)^c (23)^k]
    at any length. *)

(** Composition of two runs. *)
Lemma runN_app : forall n m c c',
  runN n c = Some c' -> runN (n + m) c = runN m c'.
Proof.
  induction n as [|n IH]; intros m c c' H.
  - simpl in *. injection H as <-. reflexivity.
  - simpl in *. destruct (step c) as [c1|] eqn:E; [|discriminate].
    apply (IH m c1 c' H).
Qed.

(** Right-moving sweep over [w], ending on the symbol after it. *)
(** One step in a right sweep. *)
Lemma step_r : forall s l x y t,
  delta s x = Some (x, true, s) ->
  step (s, l, x :: y :: t) = Some (s, x :: l, y :: t).
Proof. intros s l x y t H. unfold step. rewrite H. reflexivity. Qed.

(** Running exactly one step, spelled so that rewrites fire. *)
Lemma runN_1 : forall c, runN 1 c = step c.
Proof. intros c. cbn [runN]. destruct (step c); reflexivity. Qed.

Lemma runN_S : forall n c c', step c = Some c' -> runN (S n) c = runN n c'.
Proof. intros n c c' H. cbn [runN]. rewrite H. reflexivity. Qed.

(** One step in a left sweep. *)
Lemma step_l : forall s l x y t,
  delta s x = Some (x, false, s) ->
  step (s, y :: l, x :: t) = Some (s, l, y :: x :: t).
Proof. intros s l x y t H. unfold step. rewrite H. reflexivity. Qed.

(** Right-moving sweep over [w], ending on the symbol after it. *)
(** Right-moving sweep over [w], ending on the symbol after it. *)
Lemma walk_right : forall s w l x t,
  (forall y, In y w -> delta s y = Some (y, true, s)) ->
  runN (length w) (s, l, w ++ x :: t) = Some (s, rev w ++ l, x :: t).
Proof.
  intros s w. induction w as [|a r IH]; intros l x t H.
  - reflexivity.
  - destruct r as [|b r'].
    + change (runN 1 (s, l, a :: x :: t) = Some (s, a :: l, x :: t)).
      rewrite runN_1, (step_r s l a x t (H a (or_introl eq_refl))). reflexivity.
    + change (runN (S (S (length r'))) (s, l, a :: b :: r' ++ x :: t)
              = Some (s, rev (a :: b :: r') ++ l, x :: t)).
      rewrite (runN_S (S (length r')) (s, l, a :: b :: r' ++ x :: t)
                (s, a :: l, b :: (r' ++ x :: t))
                (step_r s l a b (r' ++ x :: t) (H a (or_introl eq_refl)))).
      change (runN (length (b :: r')) (s, a :: l, (b :: r') ++ x :: t)
              = Some (s, rev (a :: b :: r') ++ l, x :: t)).
      Check (IH (a :: l) x t (fun y Hy => H y (or_intror Hy))).
      Show.
      rewrite (IH (a :: l) x t (fun y Hy => H y (or_intror Hy))).
      simpl. rewrite app_assoc. reflexivity.
Qed.

(** Left-moving sweep: [w] is the block to the left. *)
Lemma walk_left : forall s w l x t,
  (forall y, y = x \/ In y w -> delta s y = Some (y, false, s)) ->
  runN (S (length w)) (s, w ++ l, x :: t)
  = Some (s, tl l, hd S0 l :: rev w ++ x :: t).
Proof.
  intros s w. induction w as [|a r IH]; intros l x t H.
  - destruct l as [|l0 l'].
    + change (runN 1 (s, [], x :: t) = Some (s, [], S0 :: x :: t)).
      rewrite runN_1, (step_l s [] x S0 t (H x (or_introl eq_refl))). reflexivity.
    + change (runN 1 (s, l0 :: l', x :: t) = Some (s, l', l0 :: x :: t)).
      rewrite runN_1, (step_l s l' x l0 t (H x (or_introl eq_refl))). reflexivity.
  - change (runN (S (S (length r))) (s, a :: r ++ l, x :: t)
            = Some (s, tl l, hd S0 l :: rev (a :: r) ++ x :: t)).
    rewrite (runN_S (S (length r)) (s, a :: r ++ l, x :: t) (s, r ++ l, a :: x :: t)
              (step_l s (r ++ l) x a t (H x (or_introl eq_refl)))).
    change (runN (S (length r)) (s, r ++ l, a :: x :: t)
            = Some (s, tl l, hd S0 l :: rev (a :: r) ++ x :: t)).
    rewrite (IH l a (x :: t) (fun y Hy => H y (or_intror Hy))).
    simpl. rewrite app_assoc. reflexivity.
Qed.
