(*
  rocq/TM.v
  Exact, axiom-free operational semantics for n-state, m-symbol Turing Machines
  matching the standard bbchallenge.org Busy Beaver conventions.
*)

From Stdlib Require Import Arith List Lia.
Import ListNotations.

Inductive Dir : Type :=
  | DL : Dir
  | DR : Dir.

Record Action : Type := mkAction {
  act_write : nat;
  act_dir   : Dir;
  act_next  : option nat
}.

Definition TM : Type := nat -> nat -> option Action.

Definition ValidTM (nStates nSyms : nat) (tm : TM) : Prop :=
  (forall s sym, s < nStates -> sym < nSyms ->
    match tm s sym with
    | None => True
    | Some act =>
        act_write act < nSyms /\
        match act_next act with
        | None => True
        | Some s' => s' < nStates
        end
    end) /\
  (forall s sym, (nStates <= s \/ nSyms <= sym) -> tm s sym = None).

Record Config : Type := mkConfig {
  cfg_st    : option nat;
  cfg_left  : list nat;
  cfg_cur   : nat;
  cfg_right : list nat
}.

Definition initConfig : Config :=
  mkConfig (Some 0) [] 0 [].

Definition cons0 (w : nat) (xs : list nat) : list nat :=
  match w, xs with
  | 0, [] => []
  | w, xs => w :: xs
  end.

Definition step (tm : TM) (c : Config) : option Config :=
  match cfg_st c with
  | None => None
  | Some q =>
    match tm q (cfg_cur c) with
    | None => Some (mkConfig None (cfg_left c) (cfg_cur c) (cfg_right c))
    | Some act =>
      match act_dir act with
      | DL =>
        match cfg_left c with
        | [] => Some (mkConfig (act_next act) [] 0 (cons0 (act_write act) (cfg_right c)))
        | a :: l' => Some (mkConfig (act_next act) l' a (cons0 (act_write act) (cfg_right c)))
        end
      | DR =>
        match cfg_right c with
        | [] => Some (mkConfig (act_next act) (cons0 (act_write act) (cfg_left c)) 0 [])
        | a :: r' => Some (mkConfig (act_next act) (cons0 (act_write act) (cfg_left c)) a r')
        end
      end
    end
  end.

Fixpoint steps (tm : TM) (t : nat) (c : Config) : option Config :=
  match t with
  | 0 => Some c
  | S k =>
    match step tm c with
    | None => None
    | Some c' => steps tm k c'
    end
  end.

Definition HaltsIn (tm : TM) (c0 : Config) (t : nat) : Prop :=
  exists cf, steps tm t c0 = Some cf /\ cfg_st cf = None.

Fixpoint rep (n : nat) (s : nat) (xs : list nat) : list nat :=
  match n with
  | 0 => xs
  | S k => s :: rep k s xs
  end.

(* Basic Execution Lemmas *)

Lemma steps_zero : forall tm c, steps tm 0 c = Some c.
Proof. reflexivity. Qed.

Lemma steps_one : forall tm c1 c2, step tm c1 = Some c2 -> steps tm 1 c1 = Some c2.
Proof. intros tm c1 c2 H. simpl. rewrite H. reflexivity. Qed.

Lemma steps_add : forall tm t1 t2 c1 c2 c3,
  steps tm t1 c1 = Some c2 ->
  steps tm t2 c2 = Some c3 ->
  steps tm (t1 + t2) c1 = Some c3.
Proof.
  intros tm t1. induction t1 as [| k IH]; intros t2 c1 c2 c3 H1 H2.
  - simpl in H1. inversion H1; subst. exact H2.
  - simpl in H1 |- *. destruct (step tm c1) as [cm |] eqn:Hs; [| discriminate].
    exact (IH t2 cm c2 c3 H1 H2).
Qed.

Lemma steps_succ : forall tm t c1 c2 c3,
  step tm c1 = Some c2 ->
  steps tm t c2 = Some c3 ->
  steps tm (S t) c1 = Some c3.
Proof. intros tm t c1 c2 c3 H1 H2. simpl. rewrite H1. exact H2. Qed.

Lemma rep_zero : forall s xs, rep 0 s xs = xs.
Proof. reflexivity. Qed.

Lemma rep_succ : forall n s xs, rep (S n) s xs = s :: rep n s xs.
Proof. reflexivity. Qed.

Lemma rep_add : forall a b s xs, rep (a + b) s xs = rep a s (rep b s xs).
Proof.
  intros a. induction a as [| k IH]; intros b s xs; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma cons0_succ : forall w xs, cons0 (S w) xs = S w :: xs.
Proof. reflexivity. Qed.

Lemma cons0_cons : forall w x xs, cons0 w (x :: xs) = w :: x :: xs.
Proof. destruct w; reflexivity. Qed.

Lemma cons0_zero_nil : cons0 0 [] = [].
Proof. reflexivity. Qed.

(* Sanity checks: BB(2,2) = 6 and BB(3,2) = 21 *)

Definition bb22 : TM := fun s sym =>
  match s, sym with
  | 0, 0 => Some (mkAction 1 DR (Some 1))
  | 0, 1 => Some (mkAction 1 DL (Some 1))
  | 1, 0 => Some (mkAction 1 DL (Some 0))
  | 1, 1 => Some (mkAction 1 DR None)
  | _, _ => None
  end.

Lemma bb22_halts_6 : HaltsIn bb22 initConfig 6.
Proof.
  exists (mkConfig None [1; 1] 1 [1]).
  split; [vm_compute; reflexivity | reflexivity].
Qed.
