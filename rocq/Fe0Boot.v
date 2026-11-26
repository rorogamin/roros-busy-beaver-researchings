(** * fe0 boot: the bbsearch machine, and its first descent step

    [machines/found_fe0_5_17s.txt] is the 17-state, 5-symbol machine that
    bbsearch produced on the fe0_5 core (log:
    .tmp_bbsearch/sweep/fe0_s17_b1e10.log, 9.4e9 search steps).  Its table is
    the core's table with the core's free cells filled; it keeps the core's
    halt cell [B/0 = 1RZ], so halting is possible.

    This file:

      - restates that machine's 17x5 table as [deltaF], generated from the
        machine file, and CHECKED against it by tools/check_boot_table.py
        (85/85 cells, run from verify.sh) so proof and simulation cannot drift;
      - proves [deltaF_agrees]: on every cell where the core table [delta] is
        defined, [deltaF] has exactly the same move.  This is what lets the
        core's proved descent facts be reused for this machine;
      - proves [boot_155]: from the blank tape the machine reaches the core's
        input configuration [1^2 B> 2^3] in exactly 155 steps;
      - proves [first_segment_7]: the first segment of the descent after that
        input, from [B] to the next [A] visit.

    Open goal (see the end of the file): the descent parametric in the
    counters, i.e. that this machine reaches [B/0] from [1^2 B> 2^3]. *)

From Stdlib Require Import Arith PeanoNat Lia List Bool.
Require Import Top.Fe0Descent.
Import ListNotations.

(** ** 1. The machine's table (generated from machines/found_fe0_5_17s.txt) *)

Definition deltaF (s : st) (x : sy) : option (sy * bool * st) :=
  nth (idx x)
    (match s with
     | A => [Some (S1, false, C); Some (S0, false, J); Some (S0, true, F);
             Some (S0, true, D); Some (S1, false, Q)]
     | B => [Some (S1, true, HALT); Some (S1, true, B); Some (S2, false, C);
             Some (S0, false, C); Some (S0, false, A)]
     | C => [Some (S0, false, I); Some (S4, true, C); Some (S2, true, C);
             Some (S3, true, C); Some (S2, true, C)]
     | D => [Some (S1, false, E); Some (S1, true, D); Some (S2, true, D);
             Some (S3, true, D); Some (S0, true, A)]
     | E => [Some (S3, false, A); Some (S1, false, E); Some (S2, false, E);
             Some (S3, false, E); Some (S4, true, F)]
     | F => [Some (S0, false, G); Some (S1, true, F); Some (S2, true, F);
             Some (S3, true, F); Some (S2, false, D)]
     | G => [Some (S0, true, I); Some (S0, false, H); Some (S1, false, G);
             Some (S3, true, I); Some (S4, true, D)]
     | H => [Some (S2, false, A); Some (S1, false, H); Some (S2, false, H);
             Some (S3, false, H); Some (S2, false, Q)]
     | I => [Some (S3, true, N); Some (S1, false, J); Some (S0, false, A);
             Some (S0, false, I); Some (S0, false, F)]
     | J => [Some (S2, true, O); Some (S0, false, E); Some (S2, false, J);
             Some (S3, false, J); Some (S0, true, D)]
     | K => [Some (S2, false, L); Some (S0, false, B); Some (S2, true, K);
             Some (S3, true, K); Some (S4, true, K)]
     | L => [Some (S3, true, O); Some (S2, true, O); Some (S2, false, L);
             Some (S3, false, L); Some (S4, false, L)]
     | M => [Some (S3, false, L); Some (S0, false, B); Some (S2, true, M);
             Some (S3, true, M); Some (S4, true, M)]
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

(** The step relation, the same shape as [step] but reading [deltaF]. *)
Definition stepF (c : cfg) : option cfg :=
  match c with
  | (s, l, r) =>
    match r with
    | [] => None
    | x :: r' =>
      match deltaF s x with
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

Fixpoint runNF (n : nat) (c : cfg) : option cfg :=
  match n with
  | 0 => Some c
  | S m => match stepF c with None => None | Some c' => runNF m c' end
  end.

(** ** 2. The found table extends the core table *)

Scheme Equality for sy.
Scheme Equality for st.

Definition all_syms : list sy := [S0; S1; S2; S3; S4].

Definition all_states : list st :=
  [A; B; C; D; E; F; G; H; I; J; K; L; M; N; O; P; Q; HALT].

(** One cell agrees when the core either has no move there (the search was
    free to fill it) or has a move and the found table copies it exactly. *)
Definition agree_cell (s : st) (x : sy) : bool :=
  match delta s x, deltaF s x with
  | None, _ => true
  | Some (y, d, s'), Some (y', d', s'') =>
      andb (sy_beq y y') (andb (Bool.eqb d d') (st_beq s' s''))
  | Some _, None => false
  end.

Theorem deltaF_agrees :
  forallb (fun s => forallb (agree_cell s) all_syms) all_states = true.
Proof. reflexivity. Qed.

(** Consequently the halt cell is the core's: [B] on [S0] moves to [HALT]. *)
Theorem halt_cell_same : deltaF B S0 = Some (S1, true, HALT).
Proof. reflexivity. Qed.

(** ** 3. The boot *)

(** Blank tape, state A. *)
Definition boot0 : cfg := (A, [], [S0]).

(** The core's input configuration [1^2 B> 2^3]; the trailing blanks are the
    cells the machine has already visited. *)
Definition core_input : cfg :=
  (B, [S1; S1], [S2; S2; S2; S0; S0; S0; S0; S0; S0; S0]).

(** Step 155 of the blank-tape run, kernel-checked. *)
Theorem boot_155 : runNF 155 boot0 = Some core_input.
Proof. reflexivity. Qed.

(** The boot lands in the core's input, and the halt cell is untouched, so the
    descent starts exactly where the core list says it does. *)
Theorem boot_reaches_core_input :
  exists l r, runNF 155 boot0 = Some (B, l, r) /\ deltaF B S0 = Some (S1, true, HALT).
Proof.
  exists [S1; S1], [S2; S2; S2; S0; S0; S0; S0; S0; S0; S0].
  split; [apply boot_155 | apply halt_cell_same].
Qed.

(** ** 4. The first segment of the descent *)

(** From the core input the machine's first segment ends at an [A] visit. *)
Definition seg1 : cfg :=
  (A, [S2; S4; S1], [S2; S0; S0; S0; S0; S0; S0; S0; S0]).

Theorem first_segment_7 : runNF 7 core_input = Some seg1.
Proof. reflexivity. Qed.

(** ** 5. Halting of this machine, verified, with the exact step count

    The core's own (1,3) start.  On this input the found machine never reads a
    cell the search filled in: it follows the core table exactly and stops at
    the core's halt. *)

Definition init13F : cfg := (B, [S1], [S2; S2; S2]).

(** Exactly 15,981 steps, then the [HALT] state. *)
Theorem found_halt_13 : exists l r, runNF 15981 init13F = Some (HALT, l, r).
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** One step later the run is undefined: 15,981 is the halting time. *)
Theorem found_halt_13_stops : runNF 15982 init13F = None.
Proof. vm_compute. reflexivity. Qed.

(** And the score at that halt: 39 ones. *)
Theorem found_score_13 : exists l r,
    runNF 15981 init13F = Some (HALT, l, r) /\ count1 (l ++ r) = 39.
Proof. vm_compute. do 2 eexists. split; reflexivity. Qed.

(** ** 6. Open goal

    [deltaF_agrees] says every move the core table has is still there, and
    [boot_155] says the blank-tape run arrives at the core input.  What is
    still to be proved is the descent itself:

      for all visible counters, the run from [1^2 B> 2^3] reaches [B/0]

    i.e. a measure on the configuration that strictly decreases at every
    round and is bounded below, with the round law proved parametric in the
    counters (pop and level, as in Fe0Descent.v).  [first_segment_7] is the
    first instance of that law; the parametric statement is the next step. *)
