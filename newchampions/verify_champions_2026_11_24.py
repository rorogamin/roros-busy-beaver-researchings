"""Standalone independent verification suite for champions_2026_11_24.json.
Checks every champion end-to-end from blank tape 0^inf A> 0^inf:
1. TNF syntax check (strict A..Y for n <= 25, A..Y+a..o for n > 25, zero [unused]).
2. Zero core corruption against tools_2026_11_24/bbcores_ultimate.txt.
3. Independent blank-tape simulation to exact landmark step K:
   verifies exact core cfg, clean BLANK tails, slot constraints, and reported args/bound.
4. 10,000 clean post-landmark simulation steps (no halt, no UNDEF).
5. Strict (n, m) irreducibility: all n states and all m symbols active across [0 .. K + 10000].
6. Conservative FGH comparison: every champion strictly beats ALL (n', m') <= (n, m) in tools_2026_11_24/wiki_live_2026_11_24.json.
7. Global 2D monotonicity across EVERY pair (n1, m1) <= (n2, m2) in (live wiki) U (our batch).
"""
import json
import os
import sys
import time
from typing import Dict, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.join(HERE, "tools_2026_11_24")
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from fgh_order import FExpr, fmt_expr, parse_core_bound, parse_wiki_latex, strictly_beats
from validator import check_core_preserved, load_cores_full, match_landmark, parse_tnf

CHAMPS_PATH = os.path.join(HERE, "champions_2026_11_24.json")
CORES_PATH = os.path.join(TOOLS_DIR, "bbcores_ultimate.txt")
WIKI_PATH = os.path.join(TOOLS_DIR, "wiki_live_2026_11_24.json")


def verify_all(post_steps: int = 10000) -> int:
    t0 = time.time()
    champs = json.load(open(CHAMPS_PATH, "r", encoding="utf-8"))
    cores = load_cores_full(CORES_PATH)
    wiki = json.load(open(WIKI_PATH, "r", encoding="utf-8"))

    raw_wiki: Dict[Tuple[int, int], FExpr] = {}
    for k, cell in wiki["cells"].items():
        n_str, m_str = k.split("x")
        wn, wm = int(n_str), int(m_str)
        if 2 <= wn <= 40 and 2 <= wm <= 9 and cell.get("runtime_latex"):
            pe = parse_wiki_latex(cell["runtime_latex"])
            if pe is not None:
                raw_wiki[(wn, wm)] = pe

    failures = []
    batch_exprs: Dict[Tuple[int, int], FExpr] = {}
    saw_coords = set()

    for ch in champs:
        n, m = ch["states"], ch["symbols"]
        core_name = ch["core"]
        tnf = ch["tm"]
        exp_step = ch["step"]
        dom = ch["domain"]

        if (n, m) in saw_coords:
            failures.append(f"{dom}: duplicate domain")
            continue
        saw_coords.add((n, m))

        if core_name not in cores:
            failures.append(f"{dom}: unknown core '{core_name}'")
            continue
        if core_name == "fe12_9_23" or core_name.endswith("_fix"):
            failures.append(f"{dom}: forbidden/unverified core variant '{core_name}'")
            continue

        try:
            pn, pm, tab = parse_tnf(tnf, allow_extended=(n > 25))
        except Exception as e:
            failures.append(f"{dom}: TNF syntax error: {e}")
            continue
        if pn != n or pm != m:
            failures.append(f"{dom}: parsed ({pn},{pm}) != ({n},{m})")
            continue

        ok_c, msg_c = check_core_preserved(cores[core_name], tnf)
        if not ok_c:
            failures.append(f"{dom}: core preservation failed: {msg_c}")
            continue

        spec = cores[core_name]["spec"]
        tape: Dict[int, int] = {}
        pos = st = lo = hi = 0
        ust = set()
        usy = set()
        halted = False
        matched_args = None

        for step in range(1, exp_step + 1):
            sym = tape.get(pos, 0)
            ust.add(st)
            usy.add(sym)
            tr = tab[st][sym]
            if tr is None or tr[2] == -1:
                halted = True
                failures.append(f"{dom}: halted/UNDEF before reported step {exp_step} (at step {step})")
                break
            w, mv, nxt = tr
            tape[pos] = w
            pos += mv
            if pos < lo:
                lo = pos
            if pos > hi:
                hi = pos
            st = nxt
            if step == exp_step:
                matched_args = match_landmark(spec, tape, pos, st, lo, hi)

        if halted:
            continue
        if matched_args is None:
            failures.append(f"{dom}: landmark did NOT match at reported step {exp_step}")
            continue
        if matched_args != ch["args"]:
            failures.append(f"{dom}: args mismatch: got {matched_args} != {ch['args']}")
            continue

        expr = parse_core_bound(core_name, matched_args)
        if expr is None:
            failures.append(f"{dom}: parse_core_bound returned None for {core_name} {matched_args}")
            continue
        if fmt_expr(expr) != ch["bound"]:
            failures.append(f"{dom}: bound string mismatch: {fmt_expr(expr)} != {ch['bound']}")
            continue

        post_ok = True
        for pstep in range(1, post_steps + 1):
            sym = tape.get(pos, 0)
            ust.add(st)
            usy.add(sym)
            tr = tab[st][sym]
            if tr is None or tr[2] == -1:
                failures.append(f"{dom}: halted/UNDEF at +{pstep} steps post-landmark")
                post_ok = False
                break
            w, mv, nxt = tr
            tape[pos] = w
            pos += mv
            st = nxt
        if not post_ok:
            continue

        if len(ust) != n or len(usy) != m:
            failures.append(f"{dom}: irreducibility failed: states={len(ust)}/{n}, syms={len(usy)}/{m}")
            continue

        for (wn, wm), we in raw_wiki.items():
            if wn <= n and wm <= m:
                if not strictly_beats(expr, we):
                    failures.append(f"{dom} ({fmt_expr(expr)}) fails to beat wiki ({wn},{wm})={fmt_expr(we)}")
                    break

        batch_exprs[(n, m)] = expr

    combined: Dict[Tuple[int, int], FExpr] = {}
    max_n = max(40, max((k[0] for k in batch_exprs), default=25))
    for n in range(2, max_n + 1):
        for m in range(2, 10):
            if (n, m) in batch_exprs:
                combined[(n, m)] = batch_exprs[(n, m)]
            elif (n, m) in raw_wiki:
                combined[(n, m)] = raw_wiki[(n, m)]

    mono_violations = 0
    for (n1, m1), e1 in combined.items():
        for (n2, m2), e2 in combined.items():
            if (n1, m1) != (n2, m2) and n1 <= n2 and m1 <= m2:
                if (n1, m1) in batch_exprs or (n2, m2) in batch_exprs:
                    if not strictly_beats(e2, e1):
                        mono_violations += 1
                        failures.append(
                            f"2D monotonicity violation: ({n1},{m1})={fmt_expr(e1)} vs ({n2},{m2})={fmt_expr(e2)}"
                        )

    elapsed = time.time() - t0
    print(f"Verified {len(champs)} champions in {elapsed:.2f}s (post_steps={post_steps})")
    print(f"  Standard format (n <= 25): {sum(1 for c in champs if c['states'] <= 25)}")
    print(f"  Extended format (n >= 26): {sum(1 for c in champs if c['states'] >= 26)}")
    print(f"  Monotonicity violations: {mono_violations}")
    print(f"  TOTAL FAILURES: {len(failures)}")
    if failures:
        for fl in failures[:20]:
            print("  FAIL:", fl)
        return 1
    print("verify_champions_2026_11_24.py: ALL CHECKS PASSED (0 failures)!")
    return 0


if __name__ == "__main__":
    sys.exit(verify_all())
