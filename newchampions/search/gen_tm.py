"""Generate exact, guaranteed-identical Lean 4 and Rocq 9.1 TM definitions + ValidTM proofs."""
import sys

def parse_tnf(tm_str):
    rows = tm_str.split('_')
    ns = len(rows)
    ms = len(rows[0]) // 3
    grid = []
    for s, row in enumerate(rows):
        assert len(row) == 3 * ms, f"Row {s} len {len(row)} != {3*ms}"
        r = []
        for sym in range(ms):
            c = row[3*sym:3*sym+3]
            assert c != '---', f"Unfilled free cell ({s},{sym})"
            w = int(c[0])
            d = c[1]
            nx = None if c[2] == 'Z' else ord(c[2]) - ord('A')
            assert 0 <= w < ms and d in ('L', 'R') and (nx is None or 0 <= nx < ns)
            r.append((w, d, nx, c))
        grid.append(r)
    return ns, ms, grid

def gen_lean_tm(name, tm_str):
    ns, ms, grid = parse_tnf(tm_str)
    lines = [f"def {name} : TM"]
    for s in range(ns):
        row_txt = ' '.join(cell[3] for cell in grid[s])
        lines.append(f"  -- State {chr(65+s)} ({s}): {row_txt}")
        for sym in range(ms):
            w, d, nx, _ = grid[s][sym]
            nx_s = "none" if nx is None else f"some {nx}"
            lines.append(f"  | {s}, {sym} => some ⟨{w}, Dir.{d}, {nx_s}⟩")
    lines.append("  | _, _ => none")
    lines.append("")
    lines.append(f"theorem {name}_valid : ValidTM {ns} {ms} {name} := by")
    lines.append("  constructor")
    lines.append("  · intro s sym hs hsym")
    lines.append("    match s with")
    for s in range(ns):
        halt_syms = [str(sym) for sym in range(ms) if grid[s][sym][2] is None]
        nonhalt_syms = [str(sym) for sym in range(ms) if grid[s][sym][2] is not None]
        branches = []
        if nonhalt_syms:
            branches.append(f"| {' | '.join(nonhalt_syms)} => exact ⟨by decide, by decide⟩")
        if halt_syms:
            branches.append(f"| {' | '.join(halt_syms)} => exact ⟨by decide, trivial⟩")
        branches.append(f"| _ + {ms} => omega")
        lines.append(f"    | {s} => match sym with {' '.join(branches)}")
    lines.append(f"    | _ + {ns} => omega")
    lines.append("  · intro s sym h")
    lines.append("    match s with")
    for s in range(ns):
        pats = ' | '.join(str(sym) for sym in range(ms))
        lines.append(f"    | {s} => match sym with | {pats} => omega | _ + {ms} => rfl")
    lines.append(f"    | _ + {ns} => rfl")
    return '\n'.join(lines)

def gen_rocq_tm(name, tm_str):
    ns, ms, grid = parse_tnf(tm_str)
    lines = [f"Definition {name} : TM := fun s sym =>", "  match s, sym with"]
    for s in range(ns):
        row_txt = ' '.join(cell[3] for cell in grid[s])
        lines.append(f"  (* State {chr(65+s)} ({s}): {row_txt} *)")
        for sym in range(ms):
            w, d, nx, _ = grid[s][sym]
            nx_s = "None" if nx is None else f"(Some {nx})"
            lines.append(f"  | {s}, {sym} => Some (mkAction {w} D{d} {nx_s})")
    lines.append("  | _, _ => None")
    lines.append("  end.")
    lines.append("")
    lines.append(f"Lemma {name}_valid : ValidTM {ns} {ms} {name}.")
    lines.append("Proof.")
    lines.append("  split.")
    lines.append("  - intros s sym Hs Hsym.")
    lines.append(f"    do {ns} (destruct s as [| s]; [")
    lines.append(f"      do {ms} (destruct sym as [| sym]; [simpl; repeat split; lia |]); lia")
    lines.append("    |]); lia.")
    lines.append("  - intros s sym H.")
    lines.append(f"    do {ns} (destruct s as [| s]; [")
    lines.append(f"      do {ms} (destruct sym as [| sym]; [lia |]); reflexivity")
    lines.append("    |]); reflexivity.")
    lines.append("Qed.")
    return '\n'.join(lines)

if __name__ == '__main__':
    mode, name, tm_str = sys.argv[1], sys.argv[2], sys.argv[3]
    print(gen_lean_tm(name, tm_str) if mode == 'lean' else gen_rocq_tm(name, tm_str))
