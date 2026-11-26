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

(** Left step at the left end of the tape: the new head is a blank. *)
Lemma step_l0 : forall s x t,
  delta s x = Some (x, false, s) ->
  step (s, [], x :: t) = Some (s, [], S0 :: x :: t).
Proof. intros s x t H. unfold step. rewrite H. reflexivity. Qed.

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
      transitivity (Some (s, rev (b :: r') ++ a :: l, x :: t)).
      * exact (IH (a :: l) x t (fun y Hy => H y (or_intror Hy))).
      * simpl. repeat rewrite <- app_assoc. reflexivity.
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
      rewrite runN_1, (step_l0 s x t (H x (or_introl eq_refl))). reflexivity.
    + change (runN 1 (s, l0 :: l', x :: t) = Some (s, l', l0 :: x :: t)).
      rewrite runN_1, (step_l s l' x l0 t (H x (or_introl eq_refl))). reflexivity.
  - change (runN (S (S (length r))) (s, a :: r ++ l, x :: t)
            = Some (s, tl l, hd S0 l :: rev (a :: r) ++ x :: t)).
    rewrite (runN_S (S (length r)) (s, a :: r ++ l, x :: t) (s, r ++ l, a :: x :: t)
              (step_l s (r ++ l) x a t (H x (or_introl eq_refl)))).
    change (runN (S (length r)) (s, r ++ l, a :: x :: t)
            = Some (s, tl l, hd S0 l :: rev (a :: r) ++ x :: t)).
    transitivity (Some (s, tl l, hd S0 l :: rev r ++ a :: x :: t)).
    * exact (IH l a (x :: t)
              (fun y Hy => H y (or_intror
                (match Hy with
                 | or_introl e => or_introl (eq_sym e)
                 | or_intror Iy => or_intror Iy
                 end)))).
    * simpl. repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** 6. The sweeps of the table, at any length *)

Lemma c_walk : forall w l x t,
  (forall y, In y w -> y = S2 \/ y = S3) ->
  runN (length w) (C, l, w ++ x :: t) = Some (C, rev w ++ l, x :: t).
Proof.
  intros w l x t H. apply walk_right.
  intros y Hy. destruct (H y Hy) as [-> | ->]; reflexivity.
Qed.

Lemma d_walk : forall w l x t,
  (forall y, In y w -> y = S2 \/ y = S3) ->
  runN (length w) (D, l, w ++ x :: t) = Some (D, rev w ++ l, x :: t).
Proof.
  intros w l x t H. apply walk_right.
  intros y Hy. destruct (H y Hy) as [-> | ->]; reflexivity.
Qed.

Lemma f_walk : forall w l x t,
  (forall y, In y w -> y = S1 \/ y = S3) ->
  runN (length w) (F, l, w ++ x :: t) = Some (F, rev w ++ l, x :: t).
Proof.
  intros w l x t H. apply walk_right.
  intros y Hy. destruct (H y Hy) as [-> | ->]; reflexivity.
Qed.

Lemma b_walk : forall w l x t,
  (forall y, In y w -> y = S1) ->
  runN (length w) (B, l, w ++ x :: t) = Some (B, rev w ++ l, x :: t).
Proof.
  intros w l x t H. apply walk_right.
  intros y Hy. rewrite (H y Hy). reflexivity.
Qed.

Lemma q_walk : forall w l x t,
  (forall y, y = x \/ In y w -> y = S1) ->
  runN (S (length w)) (Q, w ++ l, x :: t)
  = Some (Q, tl l, hd S0 l :: rev w ++ x :: t).
Proof.
  intros w l x t H. apply walk_left.
  intros y Hy. rewrite (H y Hy). reflexivity.
Qed.

Lemma e_walk : forall w l x t,
  (forall y, y = x \/ In y w -> y = S1 \/ y = S2 \/ y = S3) ->
  runN (S (length w)) (E, w ++ l, x :: t)
  = Some (E, tl l, hd S0 l :: rev w ++ x :: t).
Proof.
  intros w l x t H. apply walk_left.
  intros y Hy. destruct (H y Hy) as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma h_walk : forall w l x t,
  (forall y, y = x \/ In y w -> y = S1 \/ y = S2 \/ y = S3) ->
  runN (S (length w)) (H, w ++ l, x :: t)
  = Some (H, tl l, hd S0 l :: rev w ++ x :: t).
Proof.
  intros w l x t H. apply walk_left.
  intros y Hy. destruct (H y Hy) as [-> | [-> | ->]]; reflexivity.
Qed.

(** ** 7. Instances from the actual trace

    The run from [1^1 B> 2^3] (the boot that the blank-tape search reaches).
    Configurations are written as the tape is: [l] head-first, then the head
    cell at the front of [r]. *)

(** Round start: [1^7 4 (2233) 2] -- the state [A] at the boundary. *)
Definition d1074 : cfg :=
  (A, [S3;S3;S2;S2;S4;S1;S1;S1;S1;S1;S1;S1], [S2]).

(** One round later: [a] is up by one and the word has grown. *)
Definition d1459 : cfg :=
  (A, [S2;S3;S2;S3;S2;S3;S2;S3;S2;S3;S2;S3;S2;S3;S2;S3;S3;S2;
       S2;S4;S1;S1;S1;S1;S1;S1;S1;S1], [S3;S0;S0;S0]).

(** 385 steps of the table take [d1074] to [d1459]. *)
Theorem round_1074_1459 : runN 385 d1074 = Some d1459.
Proof. vm_compute. reflexivity. Qed.

(** Level drop: [1^16 4 (2233)] with the head on the last [3]. *)
Definition d3675 : cfg :=
  (A, [S3;S2;S2;S4;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1], [S3]).

(** The [2233] block is gone: [1^17 4 2], the [c = 0] phase. *)
Definition d3752 : cfg :=
  (A, [S4;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1],
      [S2;S0;S0;S0;S0;S0;S0]).

(** 77 steps consume the last block: [c] drops from 1 to 0. *)
Theorem leveldrop_3675_3752 : runN 77 d3675 = Some d3752.
Proof. vm_compute. reflexivity. Qed.

(** ** 8. The two blocks the round uses, at any length

    [1^a] on the left of the head and [(2233)^c (23)^k] on the right. *)

Lemma in_repeat_ones : forall n y, In y (repeat S1 n) -> y = S1.
Proof.
  induction n as [|n IH]; intros y Hy.
  - simpl in Hy. destruct Hy.
  - simpl in Hy. destruct Hy as [E | Hy].
    + symmetry. exact E.
    + apply IH. exact Hy.
Qed.

Lemma ones_length : forall n, length (repeat S1 n) = n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma b_scan_ones : forall a l x t,
  runN a (B, l, repeat S1 a ++ x :: t) = Some (B, repeat S1 a ++ l, x :: t).
Proof.
  intros a l x t.
  rewrite <- (ones_length a) at 1.
  rewrite (b_walk (repeat S1 a) l x t).
  - rewrite rev_repeat. reflexivity.
  - intros y Hy. exact (in_repeat_ones a y Hy).
Qed.

Lemma in_concat_repeat : forall (b : word) k y,
  (forall z, In z b -> z = S2 \/ z = S3) ->
  In y (concat (repeat b k)) -> y = S2 \/ y = S3.
Proof.
  intros b k. induction k as [|k IH]; intros y Hb Hy.
  - simpl in Hy. destruct Hy.
  - simpl in Hy. apply in_app_or in Hy. destruct Hy as [Hy | Hy].
    + apply Hb. exact Hy.
    + apply (IH y Hb Hy).
Qed.

Lemma rep_spec : forall c k y, In y (rep c k) -> y = S2 \/ y = S3.
Proof.
  intros c k y Hy. unfold rep in Hy. apply in_app_or in Hy.
  destruct Hy as [Hy | Hy].
  - apply (in_concat_repeat blk c y).
    + intros z Hz. unfold blk in Hz. simpl in Hz.
      destruct Hz as [-> | [-> | [-> | [-> | H]]]];
        try (left; reflexivity); try (right; reflexivity); destruct H.
    + exact Hy.
  - apply (in_concat_repeat pr k y).
    + intros z Hz. unfold pr in Hz. simpl in Hz.
      destruct Hz as [-> | [-> | H]];
        try (left; reflexivity); try (right; reflexivity); destruct H.
    + exact Hy.
Qed.

Lemma c_scan_rep : forall c k l x t,
  runN (length (rep c k)) (C, l, rep c k ++ x :: t)
  = Some (C, rev (rep c k) ++ l, x :: t).
Proof.
  intros c k l x t. apply c_walk.
  intros y Hy. exact (rep_spec c k y Hy).
Qed.

Lemma length_concat_repeat : forall (b : word) n,
  length (concat (repeat b n)) = n * length b.
Proof.
  intros b n. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite app_length, IH. lia.
Qed.

Lemma length_rep : forall c k, length (rep c k) = 4 * c + 2 * k.
Proof.
  intros c k. unfold rep. rewrite app_length, !length_concat_repeat.
  unfold blk, pr. simpl. lia.
Qed.

(** The whole C-sweep over the word, its length made explicit. *)
Lemma c_scan_word : forall c k l x t,
  runN (4 * c + 2 * k) (C, l, rep c k ++ x :: t)
  = Some (C, rev (rep c k) ++ l, x :: t).
Proof.
  intros. rewrite <- length_rep. apply c_scan_rep.
Qed.

Lemma repeat_snoc : forall n, repeat S1 n ++ [S1] = repeat S1 (S n).
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rev_repeat : forall n, rev (repeat S1 n) = repeat S1 n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. apply repeat_snoc.
Qed.

(** The Q-sweep over [1^a]: the head cell must be a 1, as in the run. *)
Lemma q_scan_ones : forall a l t,
  runN (S a) (Q, repeat S1 a ++ l, S1 :: t)
  = Some (Q, tl l, hd S0 l :: repeat S1 a ++ S1 :: t).
Proof.
  intros a l t. rewrite <- (ones_length a) at 1.
  rewrite (q_walk (repeat S1 a) l S1 t).
  - rewrite rev_repeat. reflexivity.
  - intros y Hy. destruct Hy as [-> | Hy].
    + reflexivity.
    + apply in_repeat_ones in Hy. rewrite Hy. reflexivity.
Qed.

(** ** 9. Chaining the sweeps: the pop round, parametric in [a] and in the word

    The machine's pop is: [A] on the [4], then [Q] left over [1^a], then [B]
    right over the ones, then [C] over the word, then [I] erasing the last
    [23].  Every phase is one of the sweeps above, and they are chained with
    [runN_app]. *)

Lemma runN_cat : forall n m c c' c'',
  runN n c = Some c' -> runN m c' = Some c'' -> runN (n + m) c = Some c''.
Proof. intros n m c c' c'' H H0. rewrite (runN_app n m c c' H). exact H0. Qed.

Lemma ones_two : forall n, repeat S1 n ++ [S1; S1] = repeat S1 (n + 2).
Proof.
  intros n. replace (n + 2) with (S (S n)) by lia.
  rewrite <- repeat_snoc, <- repeat_snoc.
  rewrite <- app_assoc. reflexivity.
Qed.

(** The one-step rules the round uses, at the shapes the sweeps leave. *)
Lemma st_A4 : forall a' r,
  step (A, S1 :: repeat S1 a', S4 :: r) = Some (Q, repeat S1 a', S1 :: S1 :: r).
Proof. intros. reflexivity. Qed.

Lemma st_Q0 : forall l z t, step (Q, l, S0 :: z :: t) = Some (B, S1 :: l, z :: t).
Proof. intros. reflexivity. Qed.

Lemma st_B2 : forall l r, step (B, S1 :: l, S2 :: r) = Some (C, l, S1 :: S2 :: r).
Proof. intros. reflexivity. Qed.

Lemma st_C1 : forall l z t, step (C, l, S1 :: z :: t) = Some (C, S4 :: l, z :: t).
Proof. intros. reflexivity. Qed.

Lemma st_C0 : forall x l r, step (C, x :: l, S0 :: r) = Some (I, l, x :: S0 :: r).
Proof. intros. reflexivity. Qed.

Lemma st_I3 : forall x l r, step (I, x :: l, S3 :: r) = Some (I, l, x :: S0 :: r).
Proof. intros. reflexivity. Qed.

Lemma st_I2 : forall x l r, step (I, x :: l, S2 :: r) = Some (A, l, x :: S0 :: r).
Proof. intros. reflexivity. Qed.

(** [Q] left over [1^a] from a ones block, ending on the blank. *)
Lemma q_scan_nil : forall a t,
  runN (S a) (Q, repeat S1 a, S1 :: t) = Some (Q, [], S0 :: repeat S1 a ++ S1 :: t).
Proof.
  intros a t.
  replace (repeat S1 a) with (repeat S1 a ++ [])
    by (rewrite app_nil_r; reflexivity).
  rewrite (q_scan_ones a [] t).
  rewrite app_nil_r. reflexivity.
Qed.

Lemma in_four : forall (y a1 a2 a3 a4 : sy),
  In y [a1; a2; a3; a4] -> y = a1 \/ y = a2 \/ y = a3 \/ y = a4.
Proof.
  intros y a1 a2 a3 a4 H. simpl in H.
  destruct H as [E | [E | [E | [E | H]]]].
  - left. symmetry. exact E.
  - right. left. symmetry. exact E.
  - right. right. left. symmetry. exact E.
  - right. right. right. symmetry. exact E.
  - destruct H.
Qed.

Lemma rep_spec_w : forall (u : word) (c b : sy),
  (c = S2 \/ c = S3) -> (b = S2 \/ b = S3) ->
  (forall y, In y u -> y = S2 \/ y = S3) ->
  forall y, In y (u ++ [c; b; S2; S3]) -> y = S2 \/ y = S3.
Proof.
  intros u c b Hc Hb Hu y Hy.
  apply in_app_or in Hy. destruct Hy as [Hy | Hy].
  - apply Hu. exact Hy.
  - apply in_four in Hy.
    destruct Hy as [E | [E | [E | E]]].
    + destruct Hc as [H | H]; rewrite H in E; rewrite E;
        [left; reflexivity | right; reflexivity].
    + destruct Hb as [H | H]; rewrite H in E; rewrite E;
        [left; reflexivity | right; reflexivity].
    + rewrite E. left. reflexivity.
    + rewrite E. right. reflexivity.
Qed.
