"""Emit machines/machine_5_stack.txt and rocq/Machine5.v from tools/stack.py."""
import tm
import stack

DIGITS = [2, 2, 2, 2]
C0 = 1

HDR = """(** * Machine 5: growing-stack machine with rank omega^k

    {nstates} states, 2 symbols, blank tape, head at 0 in state 0.
    The boot writes the layout `[C 1^c] 00 [11 1^s 0..0 11] 0 ... 0 [11 1^s 11]`.
    One round doubles the counter *leftwards* into blank tape (`c -> 2c + 2`, so
    the counter's right edge never moves and the engine never reaches the stack)
    and then erases one digit of the stack: the field nearest the counter first,
    skipping empty fields.  `r` rounds therefore leave `3*2^(r+1) - 2` marks.
    With digits {digits} the numeral is
    `omega^3*{d0} + omega^2*{d1} + omega*{d2} + {d3}` and the depth is data on the
    tape, not control flow: this is the omega^omega family, one halting instance
    per depth.  The table is literal (see machines/{fname}); the proofs below
    evaluate the concrete run with [vm_compute], so nothing is assumed beyond the
    Rocq kernel. *)

From Stdlib Require Import List Arith Lia Bool.
From Top Require Import TM Bounds.
Import ListNotations.

Definition entry : conf := mkConf 0 [] bl [].

Definition nsteps : nat := {steps}.
Definition claim : nat := {claim}.
"""


def table_lines(tbl):
    by_state = {}
    for (s, r), v in tbl.items():
        by_state.setdefault(s, {})[r] = v
    out = ["Definition tbl : table := fun s b =>", "  match s with"]
    for s in sorted(by_state):
        out.append("  | %d => match b with" % s)
        for r in (0, 1):
            if r in by_state[s]:
                ws, d, ns = by_state[s][r]
                rn = "on" if r == 1 else "bl"
                if ns is None:
                    out.append("    | %s => None" % rn)
                else:
                    wn = "on" if ws == 1 else "bl"
                    dn = "true" if d == "R" else "false"
                    out.append("    | %s => Some (%s, %s, %d)" % (rn, wn, dn, ns))
        if len(by_state[s]) < 2:
            out.append("    | _ => None")
        out.append("    end")
    out.append("  | _ => None")
    out.append("  end.")
    out.append("")
    return out


def main():
    tbl, n = stack.build(DIGITS, C0)
    t = tm.TM(n, tbl)
    steps, tape, head, state, halted = t.run(head=0, state=0,
                                              max_steps=50_000_000)
    assert halted, steps
    sc = t.score(tape)
    rk = steps - 1                      # steps until the halting configuration
    assert sc == stack.score_of(DIGITS, C0), (sc, stack.score_of(DIGITS, C0))
    assert rk >= sc

    # ---- 5-tuple text file ------------------------------------------------
    lines = ["# machine_5_stack: growing-stack machine, rank omega^k",
             "# four fields, digits %s -- boot writes the layout itself" % DIGITS,
             "# s r w d ns   (r,w: 0 blank, 1 mark; d: L/R; ns: next state or H)"]
    for (s, r) in sorted(tbl):
        ws, d, ns = tbl[(s, r)]
        lines.append("%d %d %d %s %s" % (s, r, ws, d, "H" if ns is None else ns))
    open("machines/machine_5_stack.txt", "w").write("\n".join(lines) + "\n")

    # ---- Rocq file --------------------------------------------------------
    d = DIGITS + [0] * (4 - len(DIGITS))
    body = [HDR.format(nstates=n, digits=DIGITS, d0=d[0], d1=d[1], d2=d[2],
                       d3=d[3], fname="machine_5_stack.txt", steps=rk,
                       claim=sc)]
    body += table_lines(tbl)
    body.append("(** Machine 5 halts after exactly %d steps with %d ones on the tape."
                % (rk, sc))
    body.append("    The counter is %s, i.e. 3*2^(r+1) - 2 with r = %d rounds, plus"
                % (3 * 2 ** (sum(DIGITS) + 1) - 2, sum(DIGITS)))
    body.append("    the four sentinel cells of each of the %d fields. *)\n" % len(DIGITS))
    body.append("Theorem machine5_halts :")
    body.append("  exists c', claim <= nsteps /\\ claim <= score c' /\\")
    body.append("              run tbl nsteps entry = Some c' /\\ halted tbl c'.")
    body.append("Proof.")
    body.append("  apply okb_sound with (ns := claim) (sc := claim).")
    body.append("  vm_compute. reflexivity.")
    body.append("Qed.")
    body.append("")
    body.append("(** Score and step count both dominate 2^10. *)")
    body.append("Theorem machine5_depth :")
    body.append("  exists c', run tbl nsteps entry = Some c' /\\")
    body.append("              2^10 <= score c' /\\ 2^10 <= nsteps.")
    body.append("Proof.")
    body.append("  pose proof (machine5_halts) as [c' [H1 [H2 [H3 H4]]]].")
    body.append("  exists c'. split; [exact H3|].")
    body.append("  assert (Ht : 2^10 <= claim).")
    body.append("  { apply Nat.leb_le. vm_compute. reflexivity. }")
    body.append("  split.")
    body.append("  - apply Nat.le_trans with claim; [exact Ht|exact H2].")
    body.append("  - apply Nat.le_trans with claim; [exact Ht|exact H1].")
    body.append("Qed.")
    body.append("")
    body.append("Print Assumptions machine5_halts.")
    body.append("Print Assumptions machine5_depth.")
    body.append("")
    open("rocq/Machine5.v", "w").write("\n".join(body))
    print("machine_5_stack: %d states, %d steps, score %d, claim %d"
          % (n, rk, sc, sc))


if __name__ == "__main__":
    main()
