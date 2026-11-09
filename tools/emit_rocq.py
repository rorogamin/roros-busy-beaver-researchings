"""Emit Rocq machine files from the Python tables (table + verified run)."""
import tm
import mk_machines as mk

def tower(h):
    v = 1
    for _ in range(h):
        v = 2 ** v
    return v


HDR = """(** * {title}

    {nstates} states, 2 symbols, blank tape, head at 0 in state 0.
    The table is literal (see machines/{fname}); the proofs below evaluate the
    concrete run with [vm_compute], so nothing is assumed beyond the Rocq kernel. *)

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
                wn = "on" if ws == 1 else "bl"
                dn = "true" if d == "R" else "false"
                if ns is None:
                    out.append("    | %s => None" % rn)
                else:
                    out.append("    | %s => Some (%s, %s, %d)" % (rn, wn, dn, ns))
        if len(by_state[s]) < 2:
            out.append("    | _ => None")
        out.append("    end")
    out.append("  | _ => None")
    out.append("  end.")
    out.append("")
    return out


def emit(fname, mod, title, c, u, w, claim, extra_tower=None):
    tbl, n = mk.machine1(c, u, w)
    t = tm.TM(n, tbl)
    steps, tape, head, state, halted = t.run(head=0, state=0, max_steps=5_000_000_000)
    assert halted, (c, steps)
    sc = t.score(tape)
    assert sc >= claim, (sc, claim)
    rk = steps - 1   # steps until the halting configuration is reached
    assert rk >= claim
    body = [HDR.format(title=title, nstates=n, fname=fname, steps=rk, claim=claim)]
    body += table_lines(tbl)
    body.append("(** Machine %s halts after exactly %d steps with %d ones on the tape. *)"
                % (fn_name(mod), rk, sc))
    body.append("")
    body.append("Theorem %s_halts :" % fn_name(mod))
    body.append("  exists c', claim <= nsteps /\\ claim <= score c' /\\")
    body.append("              run tbl nsteps entry = Some c' /\\ halted tbl c'.")
    body.append("Proof.")
    body.append("  apply okb_sound with (ns := claim) (sc := claim).")
    body.append("  vm_compute. reflexivity.")
    body.append("Qed.")
    body.append("")
    if extra_tower is not None:
        body.append("(** Score and step count both dominate [tower %d]. *)" % extra_tower)
        body.append("Theorem %s_tower :" % fn_name(mod))
        body.append("  exists c', run tbl nsteps entry = Some c' /\\")
        body.append("              tower %d <= score c' /\ tower %d <= nsteps." % (extra_tower, extra_tower))
        body.append("Proof.")
        body.append("  pose proof (%s_halts) as [c' [H1 [H2 [H3 H4]]]]." % fn_name(mod))
        body.append("  exists c'. split; [exact H3|].")
        body.append("  assert (Ht : tower %d <= claim)." % extra_tower)
        body.append("  { apply Nat.leb_le. vm_compute. reflexivity. }")
        body.append("  split.")
        body.append("  - apply Nat.le_trans with claim; [exact Ht|exact H2].")
        body.append("  - apply Nat.le_trans with claim; [exact Ht|exact H1].")
        body.append("Qed.")
        body.append("")
    body.append("Print Assumptions %s_halts." % fn_name(mod))
    if extra_tower is not None:
        body.append("Print Assumptions %s_tower." % fn_name(mod))
    body.append("")
    open(mod + ".v", "w").write("\n".join(body))
    print("%-10s c=%2d states=%2d steps=%7d score=%6d" % (mod, c, n, rk, sc))
    return mod


def fn_name(mod):
    return mod.lower()


if __name__ == "__main__":
    emit("machine_1_omega", "Machine1", "Machine 1: exponential-growth blank-tape machine",
         8, 2, 1, 512, extra_tower=3)
    emit("machine_2_omega", "Machine2", "Machine 2: exponential-growth blank-tape machine",
         10, 2, 1, 2048, extra_tower=3)
    emit("machine_3_omega", "Machine3", "Machine 3: exponential-growth blank-tape machine",
         12, 2, 1, 8192, extra_tower=3)
