import os, sys
sys.path.insert(0, os.path.dirname(__file__))
import eval_towers as et

BASE = et.BASE

def check_alive_and_big(fname, label):
    path = os.path.join(BASE, fname)
    big_cands = []
    alive_nonconst = []
    with open(path) as f:
        for line in f:
            m = et.parse_mech_line(line)
            if not m: continue
            r1 = m["r1"]
            if r1 == "R1=BIG" or r1 == "R1=NOCOL1":
                big_cands.append(m)
            elif r1.startswith("R1=COL1:"):
                t2 = et.trace_from_R1_COL1(m)
                if t2 and not isinstance(t2[3], str):
                    _, seq2, L_next_2, L_orig_3 = t2
                    st, seq3, d = et.exact_tower_rounds(m, seq2[-1], L_orig_3, round_start=3, max_depth=12)
                    if st == "ALIVE":
                        # Check if last 4 gaps are constant (likely infinite loop) vs varying
                        if len(set(seq3[-5:])) > 1:
                            alive_nonconst.append((L_next_2, seq2 + seq3[1:], m))
    print(f"=== {label}: R1=BIG/NOCOL1={len(big_cands)} | ALIVE_14R_nonconst={len(alive_nonconst)} ===")
    for L2, seq, m in alive_nonconst[:10]:
        print(f"  [NONCONST ALIVE 14R] M={m['M']} bt={m['bt']} L2={L2} seq={seq} | {m['pair']}")

    # Wait: test how many R1=BIG candidates have odd factor in M and test random starting (G1, L_orig_2) to see max possible R if starting in each residue class!
    # Also check how many distinct (E_core, G_core) exist among R1=BIG by grouping!
    distinct_pairs = {}
    for m in big_cands:
        # Try sample G1 in B and sample L_orig_2 mod P*M*... wait simply check transition graph!
        P, D, M, mg = m["P"], m["D"], m["M"], m["mg"]
        # Quick heuristic: can ANY G_next ever hit H from a B state? Notice if for ALL B events, A==0 and b^{L}==0 mod M, Wait if M | 2^k, check A!
        distinct_pairs.setdefault(m["pair"], m)
    print(f"  R1=BIG distinct pairs={len(distinct_pairs)}")
    # Test which R1=BIG pairs COULD reach R>=4 for ANY L_orig_2 in [20..80]:
    potential_deep = []
    for pair, m in distinct_pairs.items():
        best_r = 0
        best_info = None
        for g1, ev in m["events"].items():
            if ev[0] != "B": continue
            b = ev[1]
            for L2 in range(max(20, b["L0"]), max(20, b["L0"]) + 12):
                st, seq, d = et.exact_tower_rounds(m, g1, L2, round_start=2, max_depth=6)
                if st == "HALT":
                    tot = 1 + d
                    if tot > best_r:
                        best_r = tot
                        best_info = (tot, L2, seq)
        if best_r >= 4:
            potential_deep.append((best_r, best_info, m))
    potential_deep.sort(key=lambda x: (-x[0], -x[2]["M"]))
    print(f"  R1=BIG pairs capable of R>=4 (tested L2 in 20..43): {len(potential_deep)}")
    for r_cnt, info, m in potential_deep[:15]:
        print(f"    POTENTIAL R={r_cnt} M={m['M']}(P={m['P']},D={m['D']}) bt={m['bt']} (if L2={info[1]} seq={info[2]}) | {m['pair']}")

check_alive_and_big("mechs_cet3.txt", "CET(3)")
check_alive_and_big("mechs_cet23_t1.txt", "CET(2,3) t1")
check_alive_and_big("mechs_cet23_t2.txt", "CET(2,3) t2")
