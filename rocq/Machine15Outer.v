(** * Machine 15: the decoded H..O outer-carry instruction semantics.

    The candidate's 42-bit block is [1^40 0 1] at the right of the field
    stack.  H..O read it as a loop: H on 1 starts a carry, O on 1 continues
    into M, and M/N/O write the triple [0;1;1] while moving right.  The
    0 cell of the continuation variant writes 1, moves right, and enters
    state H (7); the 1 after it is the first cell of the next block.

    This file verifies the local rules on the literal [tbl], not the
    f_{w*2}(13) value theorem.  The concrete writer instance is 13 triples
    (39 cells); the 40-cell block adds the boundary pair [0;1]. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Machine15.
Import ListNotations.

(** [tok] is the three-cell output of one M/N/O step. *)
Definition tok : list sym := [bl; on; on].

(** [chain k] is k copies of [tok], left to right. *)
Definition chain (k : nat) : list sym := concat (repeat tok k).

(** ** Single-cell transitions *)

Lemma h_one :
  step tbl (mkConf 7 [] on []) = Some (mkConf 14 [bl] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma o_one :
  step tbl (mkConf 14 [] on []) = Some (mkConf 12 [on] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma o_zero :
  step tbl (mkConf 14 [] bl []) = Some (mkConf 7 [on] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma m_one :
  step tbl (mkConf 12 [] on []) = Some (mkConf 13 [bl] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma n_one :
  step tbl (mkConf 13 [] on []) = Some (mkConf 14 [on] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma h_zero :
  step tbl (mkConf 7 [] bl []) = Some (mkConf 5 [on] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma m_zero :
  step tbl (mkConf 12 [] bl []) = Some (mkConf 0 [] bl [bl]).
Proof. vm_compute. reflexivity. Qed.

Lemma n_zero :
  step tbl (mkConf 13 [] bl []) = Some (mkConf 0 [] bl [bl]).
Proof. vm_compute. reflexivity. Qed.

(** ** The triple and its 13-fold writer instance *)

Lemma triple_111 :
  run tbl 3 (mkConf 12 [] on (ones 2)) =
  Some (mkConf 12 [on; on; bl] bl []).
Proof. vm_compute. reflexivity. Qed.

Lemma writer_13 :
  run tbl 39 (mkConf 12 [] on (ones 38)) =
  Some (mkConf 12 (rev (chain 13)) bl []).
Proof. vm_compute. reflexivity. Qed.

(** H on [1^38] writes the prefix [0;1] and twelve triples. *)
Lemma entry_12 :
  run tbl 38 (mkConf 7 [] on (ones 37)) =
  Some (mkConf 12 (rev ([bl; on] ++ chain 12)) bl []).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions triple_111.
Print Assumptions writer_13.
Print Assumptions entry_12.
Print Assumptions h_zero.
Print Assumptions m_zero.
Print Assumptions n_zero.
