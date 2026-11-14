From Stdlib Require Import List Arith.
From Top Require Import TM Eps1Tape.
Import ListNotations.
Open Scope nat_scope.

Example rung_gen_counterexample :
  TM.run Eps1Tape.tbl 3
    (mkConf ENTRY (zeros 1 ++ on :: zeros 0) on []) <>
  Some (mkConf G2 (zeros 0) on (zeros 2 ++ on :: [])).
Proof. vm_compute. intro H. discriminate H. Qed.

Example rung_gen_actual :
  TM.run Eps1Tape.tbl 3
    (mkConf ENTRY (zeros 1 ++ on :: zeros 0) on []) =
  Some (mkConf G2 [] bl [bl; bl; on]).
Proof. vm_compute. reflexivity. Qed.
