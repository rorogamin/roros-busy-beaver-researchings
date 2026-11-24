"""Independent validator & landmark simulator for Busy Beaver champions.
Supports all cores in bbcores_ultimate.txt (KIND_BCFG, KIND_THREE, KIND_ONES, fe01_5)
plus Racheline m=2 pure-stack champions.
"""
import os
import re
from typing import Dict, List, Optional, Tuple
from fgh_order import FApp, FExpr, FVal, Ord, parse_core_bound, strictly_beats, cmp_conservative

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_CORES_PATH = os.path.join(HERE, "bbcores_ultimate.txt")


def st_char(s: int) -> str:
    return chr(ord("A") + s) if s < 25 else chr(ord("a") + (s - 25))


def parse_st_char(c: str) -> int:
    if "A" <= c <= "Y":
        return ord(c) - ord("A")
    if "a" <= c <= "o":
        return 25 + ord(c) - ord("a")
    return -1


def parse_tnf(tnf: str, allow_extended: bool = True) -> Tuple[int, int, List[List[Optional[Tuple[int, int, int]]]]]:
    if not tnf or "[unused]" in tnf:
        raise ValueError("Invalid or incomplete TNF (contains empty or [unused])")
    tnf = tnf.strip()
    rows = tnf.split("_")
    n = len(rows)
    if n < 1 or n > 40:
        raise ValueError(f"Bad state count {n}")
    if not rows[0] or len(rows[0]) % 3 != 0:
        raise ValueError("Bad row length")
    m = len(rows[0]) // 3
    if m < 2 or m > 9:
        raise ValueError(f"Symbol count {m} out of range 2..9")
    tab: List[List[Optional[Tuple[int, int, int]]]] = []
    for s, row in enumerate(rows):
        if len(row) != 3 * m:
            raise ValueError(f"Inconsistent row {s} length")
        rlist: List[Optional[Tuple[int, int, int]]] = []
        for y in range(m):
            cell = row[3 * y : 3 * y + 3]
            if cell == "---":
                rlist.append(None)
            else:
                if not ("0" <= cell[0] <= "9") or cell[1] not in ("L", "R"):
                    raise ValueError(f"Malformed cell {cell}")
                w = int(cell[0])
                if w >= m:
                    raise ValueError(f"Cell {cell} writes symbol {w} >= {m}")
                mv = -1 if cell[1] == "L" else 1
                if cell[2] == "Z":
                    ns = -1
                else:
                    ns = parse_st_char(cell[2])
                    if ns < 0 or ns >= n:
                        raise ValueError(f"Cell {cell} jumps to invalid state {cell[2]} for n={n}")
                    if not allow_extended and n <= 25 and not ("A" <= cell[2] <= "Y"):
                        raise ValueError(f"Non-standard state char {cell[2]} for n={n}")
                rlist.append((w, mv, ns))
        tab.append(rlist)
    return n, m, tab


def parse_cfg_spec(cfg_line: str, slot_line: str) -> dict:
    toks = cfg_line.strip().split()
    if not toks:
        raise ValueError("Empty cfg")
    i = 0
    left5 = None  # None, ('one', 1), ('many', name)
    if len(toks[i]) > 2 and toks[i].startswith("5^"):
        cnt = toks[i][2:]
        if cnt == "1":
            left5 = ("one", "1")
        else:
            left5 = ("many", cnt)
        i += 1
    head = toks[i]
    left_sep = False
    kind = None
    left_counter = None
    left_sep_counter = None
    if head.startswith("BCFG("):
        kind = "BCFG"
        head_chars = head[5 : head.index(")")]
        i += 1
    elif head.startswith("1^"):
        left_counter = head[2:]
        i += 1
        if i + 1 < len(toks) and toks[i] == "0^1" and toks[i + 1].startswith("1^"):
            # fe01_5 style: 1^k 0^1 1^m B> ...
            left_sep = True
            left_sep_counter = left_counter
            i += 1
            left_counter = toks[i][2:]
            i += 1
        head = toks[i]
        assert head.endswith(">"), f"bad head {head}"
        head_chars = head[:-1]
        kind = "ONES"
        i += 1
    else:
        assert head.endswith(">"), f"bad head {head}"
        head_chars = head[:-1]
        kind = "THREE"
        i += 1

    head_states = {parse_st_char(c) for c in head_chars}
    term_blank = (kind == "THREE")
    segs = []
    for t in toks[i:]:
        if t == "BLANK":
            term_blank = True
            continue
        if "^" in t:
            sp, cp = t.split("^", 1)
            sym = int(sp)
            if cp[0].isdigit():
                segs.append({"sym": sym, "counter": False, "count": int(cp), "name": None})
            else:
                segs.append({"sym": sym, "counter": True, "count": None, "name": cp})
        else:
            segs.append({"sym": int(t), "counter": False, "count": 1, "name": None})

    # Parse slot minimums
    mins: Dict[str, int] = {}
    slots_order: List[str] = []
    for t in slot_line.strip().split():
        if ">=" in t:
            nm, v = t.split(">=", 1)
            mins[nm] = int(v)
            slots_order.append(nm)
        else:
            mins[t] = 1
            slots_order.append(t)

    # Fix max_cnt and min_cnt matching exact bbsearch_ultimate.cpp rules
    for idx, sg in enumerate(segs):
        if sg["counter"]:
            sg["min_cnt"] = mins.get(sg["name"], 1)
            sg["max_cnt"] = None
        else:
            sg["min_cnt"] = sg["count"]
            sg["max_cnt"] = sg["count"]
    if not term_blank and segs:
        last = segs[-1]
        if not last["counter"] and last["sym"] != 0:
            last["max_cnt"] = None

    return {
        "kind": kind,
        "left5": left5,
        "left_sep": left_sep,
        "left_sep_counter": left_sep_counter,
        "left_counter": left_counter,
        "head_states": head_states,
        "segs": segs,
        "term_blank": term_blank,
        "mins": mins,
        "slots_order": slots_order,
    }


def load_cores_full(path: str = DEFAULT_CORES_PATH) -> dict:
    cores = {}
    nm = cfg = slot = core = ""
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            l = line.strip()
            if not l or l.startswith("#") or l.startswith("*"):
                continue
            if l.startswith("name "):
                if nm and core:
                    cores[nm] = {"cfg": cfg, "slot": slot, "core": core, "spec": parse_cfg_spec(cfg, slot)}
                nm = l[5:].strip()
                cfg = slot = core = ""
            elif l.startswith("cfg "):
                cfg = l[4:].strip()
            elif l.startswith("slot "):
                slot = l[5:].strip()
            elif l.startswith("core "):
                core = l[5:].strip()
        if nm and core:
            cores[nm] = {"cfg": cfg, "slot": slot, "core": core, "spec": parse_cfg_spec(cfg, slot)}
    for nm, d in cores.items():
        crows = d["core"].split("_")
        d["nfixed"] = len(crows)
        d["nsym"] = len(crows[0]) // 3
        d["rows"] = crows
    return cores


def check_core_preserved(core_entry: dict, tnf: str) -> Tuple[bool, str]:
    n, m, _ = parse_tnf(tnf)
    if n < core_entry["nfixed"]:
        return False, f"states {n} < core nfixed {core_entry['nfixed']}"
    if m < core_entry["nsym"]:
        return False, f"symbols {m} < core nsym {core_entry['nsym']}"
    trows = tnf.strip().split("_")
    for s, crow in enumerate(core_entry["rows"]):
        for y in range(core_entry["nsym"]):
            cc = crow[3 * y : 3 * y + 3]
            if cc != "---":
                actual = trows[s][3 * y : 3 * y + 3]
                if actual != cc:
                    return False, f"core mismatch at ({s},{y}): expected {cc}, got {actual}"
    return True, "ok"


def match_landmark(spec: dict, tape: Dict[int, int], pos: int, st: int, lo: int, hi: int) -> Optional[Dict[str, int]]:
    if st not in spec["head_states"]:
        return None
    kind = spec["kind"]
    args: Dict[str, int] = {}

    if kind == "THREE":
        if not spec["segs"]:
            return None
        if tape.get(pos, 0) != spec["segs"][0]["sym"]:
            return None
        for u in range(lo, pos):
            if tape.get(u, 0) != 0:
                return None
        t = pos
        for idx, sg in enumerate(spec["segs"]):
            cnt = 0
            while t <= hi and tape.get(t, 0) == sg["sym"]:
                cnt += 1
                t += 1
            if cnt < sg["min_cnt"]:
                return None
            if sg["max_cnt"] is not None and cnt > sg["max_cnt"]:
                return None
            if sg["counter"]:
                args[sg["name"]] = cnt
        if spec["term_blank"]:
            for u in range(t, hi + 1):
                if tape.get(u, 0) != 0:
                    return None
        return args

    if kind == "ONES":
        if not spec["segs"]:
            return None
        if tape.get(pos, 0) != spec["segs"][0]["sym"]:
            return None
        l = pos - 1
        m1 = 0
        while l >= lo and tape.get(l, 0) == 1:
            m1 += 1
            l -= 1
        if m1 < spec["mins"].get(spec["left_counter"], 1):
            return None
        args[spec["left_counter"]] = m1
        if spec["left_sep"]:
            if l < lo or tape.get(l, 0) != 0:
                return None
            l -= 1
            k1 = 0
            while l >= lo and tape.get(l, 0) == 1:
                k1 += 1
                l -= 1
            if k1 < spec["mins"].get(spec["left_sep_counter"], 1):
                return None
            args[spec["left_sep_counter"]] = k1
        for u in range(lo, l + 1):
            if tape.get(u, 0) != 0:
                return None
        t = pos
        for idx, sg in enumerate(spec["segs"]):
            if idx == len(spec["segs"]) - 1 and sg["sym"] == 0 and not sg["counter"] and not spec["term_blank"]:
                # Trailing blank sentinel cell (bbsearch_ultimate line 1113)
                if tape.get(t, 0) != 0:
                    return None
                t += 1
                continue
            cnt = 0
            while t <= hi and tape.get(t, 0) == sg["sym"]:
                cnt += 1
                t += 1
            if cnt < sg["min_cnt"]:
                return None
            if sg["max_cnt"] is not None and cnt > sg["max_cnt"]:
                return None
            if sg["counter"]:
                args[sg["name"]] = cnt
        if spec["term_blank"]:
            for u in range(t, hi + 1):
                if tape.get(u, 0) != 0:
                    return None
        return args

    if kind == "BCFG":
        if tape.get(pos, 0) != 1:
            return None
        if pos > lo and tape.get(pos - 1, 0) == 1:
            return None
        j = pos
        n1 = 0
        while j <= hi and tape.get(j, 0) == 1:
            n1 += 1
            j += 1
        if n1 < 1:
            return None
        i = pos - 1
        k2 = 0
        while i >= lo and tape.get(i, 0) == 2:
            k2 += 1
            i -= 1
        if k2 < 1:
            return None
        n3 = 0
        while i >= lo and tape.get(i, 0) == 3:
            n3 += 1
            i -= 1
        if n3 < 1 or (n3 & 1) == 0:
            return None
        m_val = (n3 - 1) // 2
        r5 = 0
        while i >= lo and tape.get(i, 0) == 5:
            r5 += 1
            i -= 1
        l5 = spec["left5"]
        if l5 is None and r5 != 0:
            return None
        if l5 is not None and l5[0] == "one" and r5 != 1:
            return None
        if l5 is not None and l5[0] == "many" and r5 < 1:
            return None
        for u in range(lo, i + 1):
            if tape.get(u, 0) != 0:
                return None
        args["k"] = k2
        args["n"] = n1
        args["m"] = m_val
        if l5 is not None and l5[0] == "many":
            args[l5[1]] = r5
        t = j
        for idx, sg in enumerate(spec["segs"]):
            cnt = 0
            while t <= hi and tape.get(t, 0) == sg["sym"]:
                cnt += 1
                t += 1
            if cnt < sg["min_cnt"]:
                return None
            if sg["max_cnt"] is not None and cnt > sg["max_cnt"]:
                return None
            if sg["counter"]:
                args[sg["name"]] = cnt
        if spec["term_blank"]:
            for u in range(t, hi + 1):
                if tape.get(u, 0) != 0:
                    return None
        return args

    return None


def _expr_rank_tuple(core_name: str, args: dict, expr: FExpr) -> tuple:
    if isinstance(expr, FVal):
        return (0, expr.arrows, expr.val, expr.arg)
    return (1, expr.ord.tier, expr.ord.off, expr.iters, _expr_rank_tuple(core_name, args, expr.inner))


def validate_candidate(
    core_name: str,
    tnf: str,
    cores: Optional[dict] = None,
    sim_cap: int = 25000,
    post_steps: int = 5000,
    require_irred: bool = True,
) -> dict:
    """Validate a candidate TM completely from blank tape.
    Returns dict with keys: ok, reason, n, m, step, args, bound_expr, bound_str, used_states, used_syms, irred.
    """
    if cores is None:
        cores = load_cores_full()
    if core_name not in cores:
        return {"ok": False, "reason": f"unknown core {core_name}"}
    ce = cores[core_name]

    try:
        n, m, tab = parse_tnf(tnf, allow_extended=True)
    except Exception as e:
        return {"ok": False, "reason": f"tnf parse error: {e}"}

    ok_c, msg_c = check_core_preserved(ce, tnf)
    if not ok_c:
        return {"ok": False, "reason": msg_c}

    spec = ce["spec"]
    tape: Dict[int, int] = {}
    pos = 0
    st = 0
    lo = 0
    hi = 0
    used_st = set()
    used_sym = set()

    # Phase 1: run up to sim_cap, recording all valid landmarks and snapshot at the best one
    best_hit = None  # (rank_tuple, step, args, expr, pos, st, lo, hi, used_st_copy, used_sym_copy, tape_copy)
    halted_early = False

    # Wait: simulation speed optimization: keep tape as dict, stop early ONLY after finding good hit?
    # Actually 25,000 steps in pure Python takes ~5ms, very fast.
    for step in range(1, sim_cap + 1):
        sym = tape.get(pos, 0)
        used_st.add(st)
        used_sym.add(sym)
        tr = tab[st][sym]
        if tr is None or tr[2] == -1:
            halted_early = True
            break
        w, mv, nxt = tr
        tape[pos] = w
        pos += mv
        if pos < lo:
            lo = pos
        if pos > hi:
            hi = pos
        st = nxt

        if st in spec["head_states"]:
            args = match_landmark(spec, tape, pos, st, lo, hi)
            if args is not None:
                expr = parse_core_bound(core_name, args)
                if expr is not None:
                    rk = _expr_rank_tuple(core_name, args, expr)
                    if best_hit is None or rk > best_hit[0]:
                        best_hit = (
                            rk,
                            step,
                            dict(args),
                            expr,
                            pos,
                            st,
                            lo,
                            hi,
                            set(used_st),
                            set(used_sym),
                            dict(tape),
                        )

    if best_hit is None:
        return {"ok": False, "reason": f"no valid landmark in {sim_cap} steps (halted_early={halted_early})"}

    _, bstep, bargs, bexpr, p2, st2, lo2, hi2, ust, usy, tape2 = best_hit

    # Phase 2: simulate post_steps cleanly from best_hit
    for _ in range(post_steps):
        sym = tape2.get(p2, 0)
        ust.add(st2)
        usy.add(sym)
        tr = tab[st2][sym]
        if tr is None or tr[2] == -1:
            return {"ok": False, "reason": f"halted or hit UNDEF within {post_steps} post-landmark steps (after landmark step {bstep})"}
        w, mv, nxt = tr
        tape2[p2] = w
        p2 += mv
        st2 = nxt

    irred = (len(ust) == n and len(usy) == m)
    if require_irred and not irred:
        return {
            "ok": False,
            "reason": f"not irreducible: states={len(ust)}/{n}, syms={len(usy)}/{m}",
            "n": n,
            "m": m,
            "step": bstep,
            "args": bargs,
            "used_states": len(ust),
            "used_syms": len(usy),
            "irred": False,
        }

    return {
        "ok": True,
        "reason": "ok",
        "core": core_name,
        "n": n,
        "m": m,
        "tm": tnf.strip(),
        "step": bstep,
        "args": bargs,
        "bound_expr": bexpr,
        "used_states": len(ust),
        "used_syms": len(usy),
        "irred": irred,
    }


def _selftest():
    from fgh_order import fmt_expr
    import json
    cores = load_cores_full()
    w = json.load(open(os.path.join(HERE, "wiki_live_2026_11_24.json"), "r", encoding="utf-8"))

    # 1. Test smoke test fwpw3_7 TM
    tm_14_7 = "0LH3RA1LD2RB4RI---2LE_1RZ3LA4LH2RB3LL2LM5LN_3RA1LA3LC2RC6RJ---3RA_2RE---3LC2RC6LC------_3RA2RE2RE4RF---2LJ---_1LG1RF3LG3RF4LG1RK---_2RJ0LH2LG2LI4LK------_6LL1LH1LG3LH4LH------_2RC1LI3LG3LI4LI---2LL_5LG1RJ2RJ3RJ4RF5LK---_6LM1LK3LE3LK---------_3RA1LL1LL1LL---------_0RC6LD2LM2LM---------_3RN---5LN5LN---2RB---"
    r1 = validate_candidate("fwpw3_7", tm_14_7, cores=cores, sim_cap=5000, post_steps=5000, require_irred=True)
    assert r1["ok"], f"fwpw3_7 failed: {r1}"
    print("Smoke fwpw3_7 OK:", r1["args"], fmt_expr(r1["bound_expr"]), f"st={r1['used_states']}/{r1['n']} sym={r1['used_syms']}/{r1['m']}")

    # 2. Test live wiki 19x8, 20x7, 21x6
    for k, cname in [("19x8", "fe1_8"), ("20x7", "fe1_7"), ("21x6", "fe1_6")]:
        res = validate_candidate(cname, w["cells"][k]["tm"], cores=cores, sim_cap=5000, post_steps=5000, require_irred=False)
        assert res["ok"], f"{k} failed: {res}"
        print(f"Wiki {k} ({cname}) OK:", res["args"], fmt_expr(res["bound_expr"]), f"irred={res['irred']} st={res['used_states']}/{res['n']} sym={res['used_syms']}/{res['m']}")

    print("validator.py selftest: ALL PASSED")


if __name__ == "__main__":
    _selftest()
