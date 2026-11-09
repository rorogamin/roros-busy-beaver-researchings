(** * Machine 5: growing-stack machine with rank omega^k

    250 states, 2 symbols, blank tape, head at 0 in state 0.
    The boot writes the layout `[C 1^c] 00 [11 1^s 0..0 11] 0 ... 0 [11 1^s 11]`.
    One round doubles the counter *leftwards* into blank tape (`c -> 2c + 2`, so
    the counter's right edge never moves and the engine never reaches the stack)
    and then erases one digit of the stack: the field nearest the counter first,
    skipping empty fields.  `r` rounds therefore leave `3*2^(r+1) - 2` marks.
    With digits [2, 2, 2, 2] the numeral is
    `omega^3*2 + omega^2*2 + omega*2 + 2` and the depth is data on the
    tape, not control flow: this is the omega^omega family, one halting instance
    per depth.  The table is literal (see machines/machine_5_stack.txt); the proofs below
    evaluate the concrete run with [vm_compute], so nothing is assumed beyond the
    Rocq kernel. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Bounds.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := 1570374.
Definition claim : nat := 1550.

Definition tbl : table := fun s b =>
  match s with
  | 0 => match b with
    | bl => Some (bl, true, 15)
    | _ => None
    end
  | 15 => match b with
    | bl => Some (on, true, 16)
    | _ => None
    end
  | 16 => match b with
    | bl => Some (bl, true, 17)
    | _ => None
    end
  | 17 => match b with
    | bl => Some (bl, true, 18)
    | _ => None
    end
  | 18 => match b with
    | bl => Some (on, true, 19)
    | _ => None
    end
  | 19 => match b with
    | bl => Some (on, true, 20)
    | _ => None
    end
  | 20 => match b with
    | bl => Some (on, true, 21)
    | _ => None
    end
  | 21 => match b with
    | bl => Some (on, true, 22)
    | _ => None
    end
  | 22 => match b with
    | bl => Some (bl, true, 23)
    | _ => None
    end
  | 23 => match b with
    | bl => Some (on, true, 24)
    | _ => None
    end
  | 24 => match b with
    | bl => Some (on, true, 25)
    | _ => None
    end
  | 25 => match b with
    | bl => Some (bl, true, 26)
    | _ => None
    end
  | 26 => match b with
    | bl => Some (on, true, 27)
    | _ => None
    end
  | 27 => match b with
    | bl => Some (on, true, 28)
    | _ => None
    end
  | 28 => match b with
    | bl => Some (on, true, 29)
    | _ => None
    end
  | 29 => match b with
    | bl => Some (on, true, 30)
    | _ => None
    end
  | 30 => match b with
    | bl => Some (bl, true, 31)
    | _ => None
    end
  | 31 => match b with
    | bl => Some (on, true, 32)
    | _ => None
    end
  | 32 => match b with
    | bl => Some (on, true, 33)
    | _ => None
    end
  | 33 => match b with
    | bl => Some (bl, true, 34)
    | _ => None
    end
  | 34 => match b with
    | bl => Some (on, true, 35)
    | _ => None
    end
  | 35 => match b with
    | bl => Some (on, true, 36)
    | _ => None
    end
  | 36 => match b with
    | bl => Some (on, true, 37)
    | _ => None
    end
  | 37 => match b with
    | bl => Some (on, true, 38)
    | _ => None
    end
  | 38 => match b with
    | bl => Some (bl, true, 39)
    | _ => None
    end
  | 39 => match b with
    | bl => Some (on, true, 40)
    | _ => None
    end
  | 40 => match b with
    | bl => Some (on, true, 41)
    | _ => None
    end
  | 41 => match b with
    | bl => Some (bl, true, 42)
    | _ => None
    end
  | 42 => match b with
    | bl => Some (on, true, 43)
    | _ => None
    end
  | 43 => match b with
    | bl => Some (on, true, 44)
    | _ => None
    end
  | 44 => match b with
    | bl => Some (on, true, 45)
    | _ => None
    end
  | 45 => match b with
    | bl => Some (on, true, 46)
    | _ => None
    end
  | 46 => match b with
    | bl => Some (bl, true, 47)
    | _ => None
    end
  | 47 => match b with
    | bl => Some (on, true, 48)
    | _ => None
    end
  | 48 => match b with
    | bl => Some (on, true, 49)
    | _ => None
    end
  | 49 => match b with
    | bl => Some (bl, true, 50)
    | _ => None
    end
  | 50 => match b with
    | bl => Some (bl, false, 50)
    | on => Some (on, false, 51)
    end
  | 51 => match b with
    | bl => Some (bl, false, 52)
    | on => Some (on, false, 51)
    end
  | 52 => match b with
    | bl => Some (bl, false, 52)
    | on => Some (on, false, 53)
    end
  | 53 => match b with
    | bl => Some (bl, false, 54)
    | on => Some (on, false, 53)
    end
  | 54 => match b with
    | bl => Some (bl, false, 54)
    | on => Some (on, false, 55)
    end
  | 55 => match b with
    | bl => Some (bl, false, 56)
    | on => Some (on, false, 55)
    end
  | 56 => match b with
    | bl => Some (bl, false, 56)
    | on => Some (on, false, 57)
    end
  | 57 => match b with
    | bl => Some (bl, false, 58)
    | on => Some (on, false, 57)
    end
  | 58 => match b with
    | bl => Some (bl, false, 58)
    | on => Some (on, false, 59)
    end
  | 59 => match b with
    | bl => Some (bl, false, 60)
    | on => Some (on, false, 59)
    end
  | 60 => match b with
    | bl => Some (bl, false, 60)
    | on => Some (on, false, 61)
    end
  | 61 => match b with
    | bl => Some (bl, false, 62)
    | on => Some (on, false, 61)
    end
  | 62 => match b with
    | bl => Some (bl, false, 62)
    | on => Some (on, false, 63)
    end
  | 63 => match b with
    | bl => Some (bl, false, 64)
    | on => Some (on, false, 63)
    end
  | 64 => match b with
    | bl => Some (bl, false, 64)
    | on => Some (on, false, 65)
    end
  | 65 => match b with
    | bl => Some (bl, false, 66)
    | on => Some (on, false, 65)
    end
  | 66 => match b with
    | bl => Some (bl, false, 66)
    | on => Some (on, false, 67)
    end
  | 67 => match b with
    | bl => Some (bl, true, 200)
    | on => Some (on, false, 67)
    end
  | 200 => match b with
    | bl => Some (bl, false, 201)
    | on => Some (on, true, 200)
    end
  | 201 => match b with
    | on => Some (bl, false, 202)
    | _ => None
    end
  | 202 => match b with
    | bl => Some (bl, false, 203)
    | on => Some (on, false, 202)
    end
  | 203 => match b with
    | bl => Some (bl, false, 204)
    | _ => None
    end
  | 204 => match b with
    | bl => Some (on, true, 205)
    | on => Some (on, false, 204)
    end
  | 205 => match b with
    | bl => Some (bl, true, 206)
    | on => Some (on, true, 205)
    end
  | 206 => match b with
    | bl => Some (bl, true, 207)
    | _ => None
    end
  | 207 => match b with
    | bl => Some (on, false, 208)
    | on => Some (on, true, 207)
    end
  | 208 => match b with
    | bl => Some (on, false, 209)
    | on => Some (bl, false, 202)
    end
  | 209 => match b with
    | bl => Some (on, false, 210)
    | _ => None
    end
  | 210 => match b with
    | bl => Some (bl, true, 211)
    | on => Some (on, true, 210)
    end
  | 211 => match b with
    | bl => Some (bl, true, 220)
    | _ => None
    end
  | 220 => match b with
    | bl => Some (bl, true, 220)
    | on => Some (on, true, 221)
    end
  | 221 => match b with
    | bl => Some (bl, true, 222)
    | on => Some (on, true, 222)
    end
  | 222 => match b with
    | bl => Some (bl, true, 223)
    | on => Some (on, true, 223)
    end
  | 223 => match b with
    | bl => Some (bl, true, 224)
    | on => Some (on, true, 224)
    end
  | 224 => match b with
    | bl => Some (bl, false, 226)
    | on => Some (bl, true, 236)
    end
  | 225 => match b with
    | bl => Some (bl, false, 226)
    | on => Some (bl, true, 236)
    end
  | 226 => match b with
    | bl => Some (bl, false, 227)
    | on => Some (bl, true, 238)
    end
  | 227 => match b with
    | bl => Some (bl, false, 228)
    | on => Some (bl, true, 239)
    end
  | 228 => match b with
    | bl => Some (bl, true, 229)
    | on => Some (on, true, 229)
    end
  | 229 => match b with
    | bl => Some (bl, true, 230)
    | on => Some (on, true, 230)
    end
  | 230 => match b with
    | bl => Some (bl, true, 231)
    | on => Some (on, true, 231)
    end
  | 231 => match b with
    | bl => Some (bl, true, 232)
    | on => Some (on, true, 232)
    end
  | 232 => match b with
    | bl => Some (bl, true, 233)
    | on => Some (on, true, 233)
    end
  | 233 => match b with
    | bl => Some (bl, true, 234)
    | on => Some (on, true, 234)
    end
  | 234 => match b with
    | bl => Some (bl, true, 235)
    | _ => None
    end
  | 235 => match b with
    | on => Some (on, true, 221)
    | _ => None
    end
  | 236 => match b with
    | bl => Some (bl, true, 237)
    | on => Some (on, true, 237)
    end
  | 237 => match b with
    | bl => Some (bl, false, 241)
    | on => Some (on, false, 241)
    end
  | 238 => match b with
    | bl => Some (bl, true, 236)
    | on => Some (on, true, 236)
    end
  | 239 => match b with
    | bl => Some (bl, true, 238)
    | on => Some (on, true, 238)
    end
  | 240 => match b with
    | bl => Some (bl, false, 241)
    | on => Some (on, false, 241)
    end
  | 241 => match b with
    | bl => Some (bl, false, 242)
    | on => Some (on, false, 242)
    end
  | 242 => match b with
    | bl => Some (bl, false, 243)
    | on => Some (on, false, 243)
    end
  | 243 => match b with
    | bl => Some (bl, false, 244)
    | on => Some (on, false, 244)
    end
  | 244 => match b with
    | bl => Some (bl, false, 245)
    | on => Some (on, false, 245)
    end
  | 245 => match b with
    | bl => Some (bl, false, 246)
    | on => Some (on, false, 246)
    end
  | 246 => match b with
    | bl => Some (bl, false, 247)
    | on => Some (on, false, 247)
    end
  | 247 => match b with
    | bl => Some (bl, false, 248)
    | _ => None
    end
  | 248 => match b with
    | bl => Some (bl, false, 249)
    | on => Some (on, false, 241)
    end
  | 249 => match b with
    | bl => Some (bl, false, 249)
    | on => Some (on, true, 200)
    end
  | _ => None
  end.

(** Machine 5 halts after exactly 1570374 steps with 1550 ones on the tape.
    The counter is 1534, i.e. 3*2^(r+1) - 2 with r = 8 rounds, plus
    the four sentinel cells of each of the 4 fields. *)

Theorem machine5_halts :
  exists c', claim <= nsteps /\ claim <= score c' /\
              run tbl nsteps entry = Some c' /\ halted tbl c'.
Proof.
  apply okb_sound with (ns := claim) (sc := claim).
  vm_compute. reflexivity.
Qed.

(** Score and step count both dominate 2^10. *)
Theorem machine5_depth :
  exists c', run tbl nsteps entry = Some c' /\
              2^10 <= score c' /\ 2^10 <= nsteps.
Proof.
  pose proof (machine5_halts) as [c' [H1 [H2 [H3 H4]]]].
  exists c'. split; [exact H3|].
  assert (Ht : 2^10 <= claim).
  { apply Nat.leb_le. vm_compute. reflexivity. }
  split.
  - apply Nat.le_trans with claim; [exact Ht|exact H2].
  - apply Nat.le_trans with claim; [exact Ht|exact H1].
Qed.

Print Assumptions machine5_halts.
Print Assumptions machine5_depth.
