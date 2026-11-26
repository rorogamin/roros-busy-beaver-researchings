From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive Sym3 := S0 | S1 | S2.
Inductive Dir := L | R.
Inductive St2 := A | B.

Record Trans3 := { wr : Sym3; mv : Dir; nx : St2 }.

Definition step_dir (d : Dir) : Z :=
  match d with L => -1 | R => 1 end.

Definition m1 (s : St2) (c : Sym3) : Trans3 :=
  match s, c with
  | A, S0 => {| wr := S2; mv := R; nx := B |}
  | A, S1 => {| wr := S0; mv := L; nx := A |}
  | A, S2 => {| wr := S2; mv := L; nx := A |}
  | B, S0 => {| wr := S1; mv := L; nx := A |}
  | B, S1 => {| wr := S1; mv := R; nx := B |}
  | B, S2 => {| wr := S0; mv := R; nx := B |}
  end.

Definition m2 (s : St2) (c : Sym3) : Trans3 :=
  match s, c with
  | A, S0 => {| wr := S2; mv := L; nx := B |}
  | A, S1 => {| wr := S0; mv := R; nx := A |}
  | A, S2 => {| wr := S0; mv := L; nx := A |}
  | B, S0 => {| wr := S1; mv := R; nx := B |}
  | B, S1 => {| wr := S0; mv := R; nx := A |}
  | B, S2 => {| wr := S0; mv := R; nx := A |}
  end.

(* Tape represented as (left_rev, cur_at_0, right) is slow for random access;
   for 24,180 steps, we can use a simple Z-indexed association list or
   keep it fast with a 2-finger tape? No, p1 and p2 are independent!
   Even simpler: a binary tree / PositiveMap, or just a function Z -> Sym3?
   Wait: function Z -> Sym3 with `if Z.eqb p k` builds a 24,180-deep closure!
   Let's use `BinNums.positive` or `ZMap`? Actually, `PMap` from `FSets` or a simple
   sorted/unsorted list? No, `24,180` steps * `344` cells = `8M` ops, too slow.
   A binary trie on `Z` (or `positive`) has O(10) lookup! *)

Inductive Trie :=
  | Empty : Trie
  | Node : Sym3 -> Trie -> Trie -> Trie.

Fixpoint trie_get (t : Trie) (p : positive) : Sym3 :=
  match t with
  | Empty => S0
  | Node v l r =>
      match p with
      | xH => v
      | xO p' => trie_get l p'
      | xI p' => trie_get r p'
      end
  end.

Fixpoint trie_set (t : Trie) (p : positive) (v : Sym3) : Trie :=
  match t with
  | Empty =>
      match p with
      | xH => Node v Empty Empty
      | xO p' => Node S0 (trie_set Empty p' v) Empty
      | xI p' => Node S0 Empty (trie_set Empty p' v)
      end
  | Node v0 l r =>
      match p with
      | xH => Node v l r
      | xO p' => Node v0 (trie_set l p' v) r
      | xI p' => Node v0 l (trie_set r p' v)
      end
  end.

Definition z_to_pos (z : Z) : positive :=
  match z with
  | Z0 => 1%positive
  | Zpos p => xO p
  | Zneg p => xI p
  end.

Record Cfg := {
  tape : Trie;
  p1 : Z;
  s1 : St2;
  p2 : Z;
  s2 : St2;
  halted : bool
}.

Definition init_cfg : Cfg :=
  {| tape := Empty; p1 := 0; s1 := A; p2 := 0; s2 := A; halted := false |}.

Definition step (c : Cfg) : Cfg :=
  if c.(halted) then c else
  let k1 := z_to_pos c.(p1) in
  let tr1 := m1 c.(s1) (trie_get c.(tape) k1) in
  let t1 := trie_set c.(tape) k1 tr1.(wr) in
  let p1' := c.(p1) + step_dir tr1.(mv) in
  let k2 := z_to_pos c.(p2) in
  let tr2 := m2 c.(s2) (trie_get t1 k2) in
  let t2 := trie_set t1 k2 tr2.(wr) in
  let p2' := c.(p2) + step_dir tr2.(mv) in
  {| tape := t2;
     p1 := p1'; s1 := tr1.(nx);
     p2 := p2'; s2 := tr2.(nx);
     halted := Z.eqb p1' p2' |}.

Fixpoint steps (n : nat) (c : Cfg) : Cfg :=
  match n with
  | O => c
  | S n' => steps n' (step c)
  end.

Lemma cet23_halts_34303 : (steps 34303 init_cfg).(halted) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions cet23_halts_34303.
