"""Audit hits_ultimate.jsonl against live_wiki and compute maximally large strictly 2D-monotone champion set."""
import json
import os
from collections import defaultdict
from typing import Dict, List, Optional, Tuple
from fgh_order import FApp, FExpr, FVal, Ord, cmp_conservative, fmt_expr, parse_core_bound, parse_wiki_latex, strictly_beats
from validator import _expr_rank_tuple

HERE = os.path.dirname(os.path.abspath(__file__))
WIKI_PATH = os.path.join(HERE, "wiki_live_2026_11_24.json")
HITS_PATH = os.path.join(HERE, "hits_ultimate.jsonl")


def load_wiki(path: str = WIKI_PATH):
    with open(path, "r", encoding="utf-8") as f:
        w = json.load(f)
    raw: Dict[Tuple[int, int], Optional[FExpr]] = {}
    meta: Dict[Tuple[int, int], dict] = {}
    for n in range(2, 41):
        for m in range(2, 10):
            c = w["cells"].get(f"{n}x{m}")
            meta[(n, m)] = c or {}
            rt = c.get("runtime_latex") if c else None
            raw[(n, m)] = parse_wiki_latex(rt) if rt else None
    floors: Dict[Tuple[int, int], Optional[FExpr]] = {}
    for n in range(2, 41):
        for m in range(2, 10):
            # Maximal frontier below or equal (n, m)
            best = raw[(n, m)]
            for pn, pm in [(n - 1, m), (n, m - 1)]:
                pe = floors.get((pn, pm))
                if pe is not None:
                    if best is None or strictly_beats(pe, best):
                        best = pe
            floors[(n, m)] = best
    return w, raw, floors, meta


def collect_wiki_floor_set(raw: Dict[Tuple[int, int], Optional[FExpr]], n: int, m: int) -> List[FExpr]:
    """Every raw wiki bound at (n', m') <= (n, m) that isn't already dominated by another in the set."""
    vals = []
    for n2 in range(2, n + 1):
        for m2 in range(2, m + 1):
            v = raw.get((n2, m2))
            if v is not None:
                vals.append(v)
    return vals


def load_hits(path: str = HITS_PATH, max_n: int = 40) -> Dict[Tuple[int, int], List[dict]]:
    by_cell: Dict[Tuple[int, int], Dict[str, dict]] = defaultdict(dict)
    if not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except Exception:
                continue
            if not rec.get("ok", True):
                continue
            if not rec.get("irred", False):
                continue
            n, m = rec["n"], rec["m"]
            if n > max_n:
                continue
            tm = rec["tm"]
            expr = parse_core_bound(rec["core"], rec["args"])
            if expr is None:
                continue
            rec["expr"] = expr
            rec["rank"] = _expr_rank_tuple(rec["core"], rec["args"], expr)
            prev = by_cell[(n, m)].get(tm)
            if prev is None or rec["rank"] > prev["rank"]:
                by_cell[(n, m)][tm] = rec
    out: Dict[Tuple[int, int], List[dict]] = {}
    for k, d in by_cell.items():
        lst = list(d.values())
        lst.sort(key=lambda r: (r["rank"], -r.get("step", 0)), reverse=True)
        out[k] = lst
    return out


def select_monotone(
    by_cell: Dict[Tuple[int, int], List[dict]],
    raw_wiki: Dict[Tuple[int, int], Optional[FExpr]],
    n_max: int = 25,
    m_max: int = 9,
) -> Dict[Tuple[int, int], dict]:
    """Select strongest strictly 2D-monotone champion subset over (2..n_max, 2..m_max)
    such that the union (live_wiki_unreplaced U selected) is strictly 2D-monotone!
    """
    # Filter candidates per cell to those strictly beating ALL raw_wiki[(n',m')] for (n',m') <= (n,m)
    eligible: Dict[Tuple[int, int], List[dict]] = {}
    for (n, m), cands in by_cell.items():
        if n > n_max or m > m_max:
            continue
        floors = collect_wiki_floor_set(raw_wiki, n, m)
        ok_cands = []
        for c in cands:
            e = c["expr"]
            if all(strictly_beats(e, fl) for fl in floors):
                ok_cands.append(c)
        if ok_cands:
            eligible[(n, m)] = ok_cands

    # First, compute maximal transitive lower bounds ignoring conflicts, and iteratively
    # resolve fixed_uppers conflicts ONLY against raw_wiki cells that cannot/will not be replaced,
    # and resolve selected-vs-selected conflicts cleanly without cascading false drops!
    selected: Dict[Tuple[int, int], dict] = {}
    # Phase A: Pick highest valid candidate per cell, iteratively enforcing ok_up vs FIXED raw_wiki only?
    # Better: assign initial candidate for every eligible cell, then iterate until no (ok_up vs fixed) fails,
    # Wait: a cell (n, m) only needs ok_up against raw_wiki cells NOT in selected.
    # Start with all eligible cells picking their highest (or for ties/blocks, demote/resolve).
    for k, v in eligible.items():
        selected[k] = v[0]

    def get_lowers(n: int, m: int, cur_sel: dict) -> List[FExpr]:
        out = []
        for n2 in range(2, n + 1):
            for m2 in range(2, m + 1):
                if (n2, m2) == (n, m):
                    continue
                if (n2, m2) in cur_sel:
                    out.append(cur_sel[(n2, m2)]["expr"])
                elif raw_wiki.get((n2, m2)) is not None:
                    out.append(raw_wiki[(n2, m2)])
        return out

    def get_fixed_uppers(n: int, m: int, cur_sel: dict) -> List[FExpr]:
        out = []
        for n2 in range(n, n_max + 1):
            for m2 in range(m, m_max + 1):
                if (n2, m2) == (n, m):
                    continue
                if (n2, m2) not in cur_sel and raw_wiki.get((n2, m2)) is not None:
                    out.append(raw_wiki[(n2, m2)])
        return out

    # Passes 1 & 2 together in one convergence loop until NEITHER fixed-upper NOR selected-lower violates monotonicity:
    for _ in range(200):
        changed = False
        # Top-down pass: enforce ok_up against ALL fixed un-selected live wiki cells
        for n in range(n_max, 1, -1):
            for m in range(m_max, 1, -1):
                if (n, m) not in selected:
                    continue
                ups = get_fixed_uppers(n, m, selected)
                cur = selected[(n, m)]
                if all(strictly_beats(up, cur["expr"]) for up in ups):
                    continue
                lows = get_lowers(n, m, selected)
                alt = None
                for cand in eligible[(n, m)]:
                    if all(strictly_beats(up, cand["expr"]) for up in ups) and all(
                        strictly_beats(cand["expr"], lo) for lo in lows
                    ):
                        alt = cand
                        break
                if alt is not None:
                    selected[(n, m)] = alt
                else:
                    del selected[(n, m)]
                changed = True

        # Bottom-up pass: enforce ok_down against ALL lowers (selected + fixed wiki)
        for n in range(2, n_max + 1):
            for m in range(2, m_max + 1):
                if (n, m) not in selected:
                    continue
                cur = selected[(n, m)]
                lowers = get_lowers(n, m, selected)
                if all(strictly_beats(cur["expr"], lo) for lo in lowers):
                    continue
                blockers = [
                    (n2, m2)
                    for n2 in range(2, n + 1)
                    for m2 in range(2, m + 1)
                    if (n2, m2) != (n, m) and (n2, m2) in selected
                    and not strictly_beats(cur["expr"], selected[(n2, m2)]["expr"])
                ]
                if not blockers:
                    del selected[(n, m)]
                    changed = True
                    continue
                all_demoted = True
                temp_demotes = {}
                for bk in blockers:
                    b_ups = get_fixed_uppers(bk[0], bk[1], selected)
                    b_lows = get_lowers(bk[0], bk[1], selected)
                    found = None
                    for cand in eligible[bk]:
                        if (
                            strictly_beats(cur["expr"], cand["expr"])
                            and all(strictly_beats(cand["expr"], bl) for bl in b_lows)
                            and all(strictly_beats(bu, cand["expr"]) for bu in b_ups)
                        ):
                            found = cand
                            break
                    if found is not None:
                        temp_demotes[bk] = found
                    else:
                        all_demoted = False
                        break
                if all_demoted and temp_demotes:
                    for bk, cand in temp_demotes.items():
                        selected[bk] = cand
                    changed = True
                else:
                    del selected[(n, m)]
                    changed = True
        if not changed:
            break

    # Pass 3: Re-insertion pass! Try inserting from largest (n+m) down to smallest, keeping any cell that strictly fits between lowers and uppers!
    # Also try a few random/top-down vs bottom-up insertion orders and take the larger set!
    def run_reinsert(base_sel: dict, order: list) -> dict:
        s_map = dict(base_sel)
        readded = True
        while readded:
            readded = False
            for (n, m) in order:
                if (n, m) in s_map or (n, m) not in eligible:
                    continue
                lowers = get_lowers(n, m, s_map)
                ups = []
                for n2 in range(n, n_max + 1):
                    for m2 in range(m, m_max + 1):
                        if (n2, m2) == (n, m):
                            continue
                        if (n2, m2) in s_map:
                            ups.append(s_map[(n2, m2)]["expr"])
                        elif raw_wiki.get((n2, m2)) is not None:
                            ups.append(raw_wiki[(n2, m2)])
                # Try smallest valid candidate first when filling gaps below existing upper bounds, OR highest first if no uppers?
                # Trying highest first that passes `ups` maximizes values, fallback to any that fits!
                for cand in eligible[(n, m)]:
                    if all(strictly_beats(cand["expr"], lo) for lo in lowers) and all(
                        strictly_beats(up, cand["expr"]) for up in ups
                    ):
                        s_map[(n, m)] = cand
                        readded = True
                        break
        return s_map

    coords_desc = sorted(eligible.keys(), key=lambda x: (x[0] + x[1], x[0]), reverse=True)
    coords_asc = sorted(eligible.keys(), key=lambda x: (x[0] + x[1], x[0]))
    s_desc = run_reinsert(selected, coords_desc)
    s_asc = run_reinsert(selected, coords_asc)
    selected = s_desc if len(s_desc) >= len(s_asc) else s_asc

    # Final assertion check: verify strict 2D monotonicity across ALL pairs in combined grid
    combined: Dict[Tuple[int, int], FExpr] = {}
    for n in range(2, n_max + 1):
        for m in range(2, m_max + 1):
            if (n, m) in selected:
                combined[(n, m)] = selected[(n, m)]["expr"]
            elif raw_wiki.get((n, m)) is not None:
                combined[(n, m)] = raw_wiki[(n, m)]

    for (n1, m1), e1 in combined.items():
        for (n2, m2), e2 in combined.items():
            if (n1, m1) != (n2, m2) and n1 <= n2 and m1 <= m2:
                if (n1, m1) in selected or (n2, m2) in selected:
                    assert strictly_beats(e2, e1), f"Monotonicity violation {(n1,m1)}={fmt_expr(e1)} vs {(n2,m2)}={fmt_expr(e2)}"

    return selected


def print_audit(n_max: int = 25):
    w, raw_wiki, floors, meta = load_wiki()
    by_cell = load_hits(max_n=n_max)
    sel_25 = select_monotone(by_cell, raw_wiki, n_max=min(25, n_max), m_max=9)
    print(f"=== AUDIT GRID (n=3..{min(25, n_max)}, m=2..9) ===")
    blanks_filled = sum(1 for k in sel_25 if raw_wiki.get(k) is None)
    live_beaten = len(sel_25) - blanks_filled
    print(f"Total strictly 2D-monotone champions (n<=25): {len(sel_25)}  (blank fills={blanks_filled}, live beats={live_beaten})")

    if n_max > 25:
        by_cell_all = load_hits(max_n=n_max)
        sel_all = select_monotone(by_cell_all, raw_wiki, n_max=n_max, m_max=9)
        print(f"Total strictly 2D-monotone champions (n<={n_max}): {len(sel_all)}")

    for n in range(3, min(25, n_max) + 1):
        parts = []
        for m in range(2, 10):
            if (n, m) in sel_25:
                c = sel_25[(n, m)]
                tag = fmt_expr(c["expr"]).replace("_{", "").replace("}", "")
                parts.append(f"m{m}:WIN({c['core'][:7]}:{tag[:9]})")
            elif (n, m) in by_cell:
                parts.append(f"m{m}:BLK/CONFL({len(by_cell[(n,m)])})")
            elif raw_wiki.get((n, m)) is None:
                parts.append(f"m{m}:[BLANK]")
            else:
                parts.append(f"m{m}:wiki")
        print(f"n={n:2d} | " + " | ".join(f"{p:22s}" for p in parts))
    return sel_25


if __name__ == "__main__":
    print_audit(25)
