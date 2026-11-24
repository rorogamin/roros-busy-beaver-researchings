"""Select maximal strictly 2D-monotone champion set (preserving all n<=25 winners first,
then extending strictly monotonically across n=26..35), and write champions_ultimate.json.
"""
import json
import os
from collections import Counter
from typing import Dict, List, Tuple

from audit_grid import collect_wiki_floor_set, load_hits, load_wiki, select_monotone, HITS_PATH, WIKI_PATH
from fgh_order import FApp, FExpr, FVal, fmt_expr, strictly_beats
from validator import load_cores_full

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "champions_ultimate.json")


def extend_monotone_above_25(
    sel_25: Dict[Tuple[int, int], dict],
    by_cell: Dict[Tuple[int, int], List[dict]],
    raw_wiki: Dict[Tuple[int, int], FExpr],
    n_max: int = 35,
    m_max: int = 9,
) -> Dict[Tuple[int, int], dict]:
    """Keep sel_25 pinned, and greedily/repairably add the maximal set of n=26..n_max champions
    preserving strict 2D monotonicity across (live_wiki_unreplaced U selected).
    """
    selected = dict(sel_25)

    # Filter eligible candidates in n=26..n_max
    eligible_ext: Dict[Tuple[int, int], List[dict]] = {}
    for (n, m), cands in by_cell.items():
        if n <= 25 or n > n_max or m > m_max:
            continue
        floors = collect_wiki_floor_set(raw_wiki, n, m)
        # Also must strictly beat all pinned sel_25[(n', m')] with n'<=25, m'<=m
        pinned_lowers = [r["expr"] for (pn, pm), r in sel_25.items() if pm <= m]
        ok_cands = []
        for c in cands:
            e = c["expr"]
            if all(strictly_beats(e, fl) for fl in floors) and all(strictly_beats(e, pl) for pl in pinned_lowers):
                ok_cands.append(c)
        if ok_cands:
            eligible_ext[(n, m)] = ok_cands

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

    def get_fixed_uppers(n: int, m: int, cur_sel: dict, check_max_n: int = 40) -> List[FExpr]:
        out = []
        for n2 in range(n, check_max_n + 1):
            for m2 in range(m, m_max + 1):
                if (n2, m2) == (n, m):
                    continue
                if (n2, m2) not in cur_sel and raw_wiki.get((n2, m2)) is not None:
                    out.append(raw_wiki[(n2, m2)])
        return out

    # Also verify sel_25 itself respects fixed raw_wiki in 26..40 (31x4, 36x3, etc. - all are e_0 >> omega^2+k, but verify explicitly!)
    for (pn, pm), pr in list(selected.items()):
        ups = get_fixed_uppers(pn, pm, selected, check_max_n=40)
        for up in ups:
            assert strictly_beats(up, pr["expr"]), f"Pinned ({pn},{pm}) violates higher wiki upper {fmt_expr(up)}"

    # Wait: for n=26..35, since each column ideally forms an ascending chain,
    # iterate cell-by-cell bottom-up picking SMALLEST valid candidate > lowers (or picking largest first?
    # Wait: picking smallest rung that beats lowers leaves MAXIMUM headroom for n+1, n+2, ..., 35 AND m+1!!
    # Let's try BOTH strategies (smallest-first ascending vs largest-first descending with repair) and keep whichever yields MORE champions!)
    def try_build(prefer_smallest: bool) -> Dict[Tuple[int, int], dict]:
        cur = dict(sel_25)
        for n in range(26, n_max + 1):
            for m in range(2, m_max + 1):
                if (n, m) not in eligible_ext:
                    continue
                cands = eligible_ext[(n, m)]
                ordered = list(reversed(cands)) if prefer_smallest else list(cands)
                lows = get_lowers(n, m, cur)
                ups = get_fixed_uppers(n, m, cur, check_max_n=40)
                for cand in ordered:
                    if all(strictly_beats(cand["expr"], lo) for lo in lows) and all(
                        strictly_beats(up, cand["expr"]) for up in ups
                    ):
                        cur[(n, m)] = cand
                        break
        # Optional improvement: for selected cells in 26..n_max, bump up to the HIGHEST candidate still < all selected/fixed uppers!
        for n in range(n_max, 25, -1):
            for m in range(m_max, 1, -1):
                if (n, m) not in cur:
                    continue
                lows = get_lowers(n, m, cur)
                ups = []
                for n2 in range(n, 41):
                    for m2 in range(m, m_max + 1):
                        if (n2, m2) == (n, m):
                            continue
                        if (n2, m2) in cur:
                            ups.append(cur[(n2, m2)]["expr"])
                        elif raw_wiki.get((n2, m2)) is not None:
                            ups.append(raw_wiki[(n2, m2)])
                for cand in eligible_ext[(n, m)]:
                    if all(strictly_beats(cand["expr"], lo) for lo in lows) and all(
                        strictly_beats(up, cand["expr"]) for up in ups
                    ):
                        cur[(n, m)] = cand
                        break
        return cur

    res_sm = try_build(prefer_smallest=True)
    res_lg = try_build(prefer_smallest=False)
    best = res_sm if len(res_sm) >= len(res_lg) else res_lg

    # Pass 3: Also try single-cell drop-and-refill in n=26..n_max to escape local maxima (e.g. skipping (27,3)=82 to unlock 28..32,3!)
    improved = True
    while improved:
        improved = False
        ext_keys = sorted([k for k in best if k[0] > 25])
        for drop_k in ext_keys:
            cand_map = {k: v for k, v in best.items() if k != drop_k}
            for n in range(26, n_max + 1):
                for m in range(2, m_max + 1):
                    if (n, m) in cand_map or (n, m) not in eligible_ext:
                        continue
                    lows = get_lowers(n, m, cand_map)
                    ups = []
                    for n2 in range(n, 41):
                        for m2 in range(m, m_max + 1):
                            if (n2, m2) == (n, m):
                                continue
                            if (n2, m2) in cand_map:
                                ups.append(cand_map[(n2, m2)]["expr"])
                            elif raw_wiki.get((n2, m2)) is not None:
                                ups.append(raw_wiki[(n2, m2)])
                    for cand in reversed(eligible_ext[(n, m)]):
                        if all(strictly_beats(cand["expr"], lo) for lo in lows) and all(
                            strictly_beats(up, cand["expr"]) for up in ups
                        ):
                            cand_map[(n, m)] = cand
                            break
            if len(cand_map) > len(best):
                best = cand_map
                improved = True
                break

    # Re-verify every pair across combined grid 2..40 x 2..9
    combined: Dict[Tuple[int, int], FExpr] = {}
    for n in range(2, 41):
        for m in range(2, m_max + 1):
            if (n, m) in best:
                combined[(n, m)] = best[(n, m)]["expr"]
            elif raw_wiki.get((n, m)) is not None:
                combined[(n, m)] = raw_wiki[(n, m)]
    for (n1, m1), e1 in combined.items():
        for (n2, m2), e2 in combined.items():
            if (n1, m1) != (n2, m2) and n1 <= n2 and m1 <= m2:
                if (n1, m1) in best or (n2, m2) in best:
                    assert strictly_beats(e2, e1), f"Monotonicity violation {(n1,m1)}={fmt_expr(e1)} vs {(n2,m2)}={fmt_expr(e2)}"
    return best


def ordinal_family_bucket(e: FExpr) -> str:
    if isinstance(e, FVal):
        return "finite"
    t, o = e.ord.tier, e.ord.off
    if t == 70:
        return "ε₂" if o == 0 else f"ε₂+{o}"
    if t == 60:
        return "ε₁" if o == 0 else f"ε₁+{o}"
    if t == 50:
        return "ε₀" if o == 0 else f"ε₀+{o}"
    if t == 40:
        return "ω^ω" if o == 0 else f"ω^ω+{o}"
    if t == 30:
        return "ω²" if o == 0 else f"ω²+{o}"
    if t == 20:
        return "ω×2" if o == 0 else f"ω×2+{o}"
    if t == 10:
        return "ω" if o == 0 else f"ω+{o}"
    return e.ord.fmt()


def main():
    w, raw_wiki, floors, meta = load_wiki(WIKI_PATH)
    by_cell_25 = load_hits(HITS_PATH, max_n=25)
    by_cell_all = load_hits(HITS_PATH, max_n=35)
    sel_25 = select_monotone(by_cell_25, raw_wiki, n_max=25, m_max=9)
    sel_all = extend_monotone_above_25(sel_25, by_cell_all, raw_wiki, n_max=35, m_max=9)

    items = []
    for (n, m) in sorted(sel_all.keys()):
        r = sel_all[(n, m)]
        wm = meta.get((n, m), {})
        w_prev = wm.get("runtime_latex") or "(BLANK)"
        items.append({
            "states": n,
            "symbols": m,
            "domain": f"BB({n},{m})",
            "std_format": n <= 25,
            "is_blank_fill": (raw_wiki.get((n, m)) is None),
            "core": r["core"],
            "step": r["step"],
            "args": r["args"],
            "bound": fmt_expr(r["expr"]),
            "family": ordinal_family_bucket(r["expr"]),
            "wiki_prev": w_prev,
            "wiki_floor": fmt_expr(floors.get((n, m))),
            "tm": r["tm"],
        })

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(items, f, indent=2, ensure_ascii=False)

    n_std = sum(1 for x in items if x["std_format"])
    n_ext = sum(1 for x in items if not x["std_format"])
    n_blank = sum(1 for x in items if x["is_blank_fill"])
    n_beat = len(items) - n_blank
    print(f"Exported {len(items)} verified strictly 2D-monotone champions -> {OUT_JSON}")
    print(f"  Standard format (n <= 25): {n_std}")
    print(f"  Extended format (n = 26..35): {n_ext}")
    print(f"  Blank-cell fills: {n_blank} | Live-record beats: {n_beat}")
    fam_cnt = Counter(x["family"] for x in items)
    print("  By ordinal family:", dict(sorted(fam_cnt.items())))

    # Show 26..35 grid summary
    print("\n=== EXTENDED GRID (n=26..35, cols 3,5,6,7,8,9) ===")
    for n in range(26, 36):
        row = []
        for col in [3, 5, 6, 7, 8, 9]:
            if (n, col) in sel_all:
                c = sel_all[(n, col)]
                row.append(f"m{col}:WIN({c['core'][:6]}:{fmt_expr(c['expr'])})")
            else:
                cnt = len(by_cell_all.get((n, col), []))
                row.append(f"m{col}:miss({cnt})")
        print(f"n={n:2d} | " + " | ".join(f"{x:24s}" for x in row))


if __name__ == "__main__":
    main()
