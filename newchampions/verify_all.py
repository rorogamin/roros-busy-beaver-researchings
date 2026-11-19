"""End-to-end independent verifier & cross-checker for ALL 25 Lean 4 + Rocq 9.1 Busy Beaver Champions."""
import argparse
import os
import re
import subprocess
import sys

LIBS = ['TM', 'FGH', 'Kropitz', 'Fwm2', 'Fwp2', 'Fwp2_7', 'Fwp2_H', 'Fwp2_H8']

# (module, n, m, theorem_name, ordinal_tuple, k, bound_label, prev_best_label)
# ordinal_tuple: (c, a, b) representing ω^2 * c + ω * a + b
CHAMPIONS = [
    ('BB4_8',  4, 8, 'bb48_halts_gt_f_omega_plus_4_7',        (0, 1, 4), 7,  'f_{ω+4}(7)',        'BB(4,7) > f_{ω+3}(34), BB(3,8) > f_{ω+1}^2(f_ω(30))'),
    ('BB6_6',  6, 6, 'bb66_halts_gt_f_omega_mul2_plus_1_2',   (0, 2, 1), 2,  'f_{ω×2+1}(2)',      'BB(6,6) > f_{ω×2}(89) [BEATEN BY +1 ORDINAL]'),
    ('BB6_7',  6, 7, 'bb67_halts_gt_f_omega_mul2_plus_1_6',   (0, 2, 1), 6,  'f_{ω×2+1}(6)',      'BB(5,7) > f_{ω×2}(97), our BB(6,6) > f_{ω×2+1}(2)'),
    ('BB6_8',  6, 8, 'bb68_halts_gt_f_omega_mul2_plus_2_11',  (0, 2, 2), 11, 'f_{ω×2+2}(11)',     'our BB(6,7) > f_{ω×2+1}(6), our BB(4,8) > f_{ω+4}(7)'),
    ('BB6_9',  6, 9, 'bb69_halts_gt_f_omega_mul2_plus_3_6',   (0, 2, 3), 6,  'f_{ω×2+3}(6)',      'our BB(6,8) > f_{ω×2+2}(11), BB(3,9) > f_{ω+2}(4)'),
    ('BB7_6',  7, 6, 'bb76_halts_gt_f_omega2_plus_1_2',       (1, 0, 1), 2,  'f_{ω^2+1}(2)',      'BB(7,6) > f_{ω^2}(110) [BEATEN BY +1 ORDINAL]'),
    ('BB7_7',  7, 7, 'bb77_halts_gt_f_omega2_plus_1_3',       (1, 0, 1), 3,  'f_{ω^2+1}(3)',      'our BB(7,6) > f_{ω^2+1}(2), our BB(6,7) > f_{ω×2+1}(6)'),
    ('BB7_8',  7, 8, 'bb78_halts_gt_f_omega2_plus_2_7',       (1, 0, 2), 7,  'f_{ω^2+2}(7)',      'our BB(7,7) > f_{ω^2+1}(3), our BB(6,8) > f_{ω×2+2}(11)'),
    ('BB7_9',  7, 9, 'bb79_halts_gt_f_omega2_plus_3_7',       (1, 0, 3), 7,  'f_{ω^2+3}(7)',      'our BB(7,8) > f_{ω^2+2}(7), our BB(6,9) > f_{ω×2+3}(6)'),
    ('BB8_6',  8, 6, 'bb86_halts_gt_f_omega2_plus_2_4',       (1, 0, 2), 4,  'f_{ω^2+2}(4)',      'BB(8,6) > f_{ω^2+1}(f_ω(31)) [BEATEN BY +1 ORDINAL]'),
    ('BB8_7',  8, 7, 'bb87_halts_gt_f_omega2_plus_2_8',       (1, 0, 2), 8,  'f_{ω^2+2}(8)',      'our BB(8,6) > f_{ω^2+2}(4), our BB(7,7) > f_{ω^2+1}(3)'),
    ('BB8_8',  8, 8, 'bb88_halts_gt_f_omega2_plus_3_7',       (1, 0, 3), 7,  'f_{ω^2+3}(7)',      'our BB(8,7) > f_{ω^2+2}(8), our BB(7,8) > f_{ω^2+2}(7)'),
    ('BB8_9',  8, 9, 'bb89_halts_gt_f_omega2_plus_4_7',       (1, 0, 4), 7,  'f_{ω^2+4}(7)',      'our BB(8,8) > f_{ω^2+3}(7), our BB(7,9) > f_{ω^2+3}(7)'),
    ('BB9_6',  9, 6, 'bb96_halts_gt_f_omega2_plus_2_7',       (1, 0, 2), 7,  'f_{ω^2+2}(7)',      'our BB(8,6) > f_{ω^2+2}(4), BB(9,5) > f_{ω^2+1}(6)'),
    ('BB9_7',  9, 7, 'bb97_halts_gt_f_omega2_plus_3_7',       (1, 0, 3), 7,  'f_{ω^2+3}(7)',      'our BB(8,7) > f_{ω^2+2}(8), our BB(9,6) > f_{ω^2+2}(7)'),
    ('BB9_8',  9, 8, 'bb98_halts_gt_f_omega2_plus_4_7',       (1, 0, 4), 7,  'f_{ω^2+4}(7)',      'our BB(8,8) > f_{ω^2+3}(7), our BB(9,7) > f_{ω^2+3}(7)'),
    ('BB9_9',  9, 9, 'bb99_halts_gt_f_omega2_plus_5_7',       (1, 0, 5), 7,  'f_{ω^2+5}(7)',      'our BB(8,9) > f_{ω^2+4}(7), our BB(9,8) > f_{ω^2+4}(7)'),
    ('BB10_6', 10, 6, 'bb106_halts_gt_f_omega2_plus_3_7',     (1, 0, 3), 7,  'f_{ω^2+3}(7)',      'our BB(9,6) > f_{ω^2+2}(7), BB(10,5) > f_{ω^2+2}(4)'),
    ('BB10_7', 10, 7, 'bb107_halts_gt_f_omega2_plus_4_4',     (1, 0, 4), 4,  'f_{ω^2+4}(4)',      'our BB(9,7) > f_{ω^2+3}(7), our BB(10,6) > f_{ω^2+3}(7)'),
    ('BB10_8', 10, 8, 'bb108_halts_gt_f_omega2_plus_5_7',     (1, 0, 5), 7,  'f_{ω^2+5}(7)',      'our BB(9,8) > f_{ω^2+4}(7), our BB(10,7) > f_{ω^2+4}(4)'),
    ('BB10_9', 10, 9, 'bb109_halts_gt_f_omega2_plus_6_7',     (1, 0, 6), 7,  'f_{ω^2+6}(7)',      'our BB(9,9) > f_{ω^2+5}(7), our BB(10,8) > f_{ω^2+5}(7)'),
    ('BB11_6', 11, 6, 'bb116_halts_gt_f_omega2_plus_4_8',     (1, 0, 4), 8,  'f_{ω^2+4}(8)',      'our BB(10,6) > f_{ω^2+3}(7), BB(11,4) > f_{ω^2+1}, BB(10,5) > f_{ω^2+2}(4)'),
    ('BB11_7', 11, 7, 'bb117_halts_gt_f_omega2_plus_5_7',     (1, 0, 5), 7,  'f_{ω^2+5}(7)',      'our BB(10,7) > f_{ω^2+4}(4), our BB(11,6) > f_{ω^2+4}(8)'),
    ('BB11_8', 11, 8, 'bb118_halts_gt_f_omega2_plus_6_10',    (1, 0, 6), 10, 'f_{ω^2+6}(10)',     'our BB(10,8) > f_{ω^2+5}(7), our BB(11,7) > f_{ω^2+5}(7)'),
    ('BB11_9', 11, 9, 'bb119_halts_gt_f_omega2_plus_7_7',     (1, 0, 7), 7,  'f_{ω^2+7}(7)',      'our BB(10,9) > f_{ω^2+6}(7), our BB(11,8) > f_{ω^2+6}(10)'),
]

# Wiki upper-envelope entries that could dominate (n <= 11, m <= 9)
WIKI_BOUNDARIES = [
    (4, 7, (0, 1, 3), 34),
    (3, 8, (0, 1, 1), 999999),
    (3, 9, (0, 1, 2), 4),
    (5, 6, (0, 1, 3), 31),
    (5, 7, (0, 2, 0), 97),
    (6, 5, (0, 1, 3), 11),
    (6, 6, (0, 2, 0), 89),
    (7, 5, (0, 1, 3), 999999),
    (7, 6, (1, 0, 0), 110),
    (8, 5, (1, 0, 0), 13),
    (8, 6, (1, 0, 1), 999999),
    (9, 5, (1, 0, 1), 6),
    (10, 5, (1, 0, 2), 4),
    (11, 4, (1, 0, 1), 999999),
]

ALLOWED_LEAN_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def parse_lean_tm(path, ns, ms):
    txt = open(path, encoding='utf-8').read()
    cells = {}
    for m in re.finditer(r'\|\s*(\d+),\s*(\d+)\s*=>\s*some\s*⟨(\d+),\s*Dir\.([LR]),\s*(none|some\s+(\d+))⟩', txt):
        s, sym, w, d, nx_raw, nx_num = int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5), m.group(6)
        nx = 'Z' if nx_raw == 'none' else chr(ord('A') + int(nx_num))
        assert (s, sym) not in cells, f"Duplicate Lean cell ({s},{sym}) in {path}"
        cells[(s, sym)] = f"{w}{d}{nx}"
    assert len(cells) == ns * ms, f"{path}: expected {ns*ms} Lean cells, got {len(cells)}"
    rows = []
    for s in range(ns):
        rows.append(''.join(cells[(s, sym)] for sym in range(ms)))
    return '_'.join(rows)

def parse_rocq_tm(path, ns, ms):
    txt = open(path, encoding='utf-8').read()
    cells = {}
    for m in re.finditer(r'\|\s*(\d+),\s*(\d+)\s*=>\s*Some\s*\(mkAction\s+(\d+)\s+D([LR])\s+(None|\(Some\s+(\d+)\))\)', txt):
        s, sym, w, d, nx_raw, nx_num = int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5), m.group(6)
        nx = 'Z' if nx_raw == 'None' else chr(ord('A') + int(nx_num))
        assert (s, sym) not in cells, f"Duplicate Rocq cell ({s},{sym}) in {path}"
        cells[(s, sym)] = f"{w}{d}{nx}"
    assert len(cells) == ns * ms, f"{path}: expected {ns*ms} Rocq cells, got {len(cells)}"
    rows = []
    for s in range(ns):
        rows.append(''.join(cells[(s, sym)] for sym in range(ms)))
    return '_'.join(rows)

def check_no_cheats(path, lang):
    txt = open(path, encoding='utf-8').read()
    if lang == 'lean':
        code = re.sub(r'/-.*?-/', '', txt, flags=re.S)
        code = re.sub(r'--.*', '', code)
        assert not re.search(r'\b(sorry|admit|axiom)\b', code), f"Forbidden keyword in {path}"
    else:
        code = re.sub(r'\(\*.*?\*\)', '', txt, flags=re.S)
        assert not re.search(r'\b(Admitted|Axiom|Parameter|Conjecture)\b', code), f"Forbidden keyword in {path}"

def up_to_date(src, dst):
    return os.path.exists(dst) and os.path.getmtime(dst) >= os.path.getmtime(src)

def main():
    parser = argparse.ArgumentParser(description="Verify Busy Beaver proofs in Lean 4 and Rocq 9.1.")
    parser.add_argument('--only', nargs='+', help="Compile and check ONLY the specified module names (e.g. Kropitz2 BB2_11)")
    parser.add_argument('--force', action='store_true', help="Force recompilation even when outputs are up to date")
    args = parser.parse_args()
    only_set = set(args.only) if args.only else None

    os.makedirs('lean/build/BB', exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = 'lean/build'

    print(f"1. Checking shared libraries in Lean 4 (-j 1 -M 2048) and Rocq 9.1...", flush=True)
    for lib in LIBS:
        lp = f'lean/BB/{lib}.lean'
        rp = f'rocq/{lib}.v'
        lo = f'lean/build/BB/{lib}.olean'
        ro = f'rocq/{lib}.vo'
        check_no_cheats(lp, 'lean')
        check_no_cheats(rp, 'rocq')
        if only_set is not None and lib not in only_set and not args.force:
            if up_to_date(lp, lo) and up_to_date(rp, ro):
                print(f"  [SKIP] {lib:10s} (up to date)", flush=True)
                continue
        r1 = subprocess.run(['lean', '-j', '1', '-M', '2048', '-o', lo, lp], env=env, capture_output=True, text=True)
        assert r1.returncode == 0 and not r1.stderr.strip() and 'warning:' not in r1.stdout, f"Lean fail on {lib}:\n{r1.stdout}\n{r1.stderr}"
        r2 = subprocess.run(['rocq', 'c', '-Q', 'rocq', 'BB', rp], capture_output=True, text=True)
        assert r2.returncode == 0, f"Rocq fail on {lib}:\n{r2.stdout}\n{r2.stderr}"
        print(f"  [OK] {lib:10s} (Lean 4 + Rocq 9.1)", flush=True)

    print(f"\n2. Compiling, axiom-checking, and cross-checking champions...", flush=True)
    tnf_map = {}
    for mod, ns, ms, thm, ord_t, k, label, prev in CHAMPIONS:
        lp = f'lean/BB/{mod}.lean'
        rp = f'rocq/{mod}.v'
        check_no_cheats(lp, 'lean')
        check_no_cheats(rp, 'rocq')

        # Cross-check exact transition tables & ValidTM dimensions
        lean_tnf = parse_lean_tm(lp, ns, ms)
        rocq_tnf = parse_rocq_tm(rp, ns, ms)
        assert lean_tnf == rocq_tnf, f"TM MISMATCH in {mod}!\n  Lean: {lean_tnf}\n  Rocq: {rocq_tnf}"
        ltxt = open(lp, encoding='utf-8').read()
        rtxt = open(rp, encoding='utf-8').read()
        assert f'ValidTM {ns} {ms}' in ltxt and f'ValidTM {ns} {ms}' in rtxt, f"ValidTM mismatch in {mod}"
        assert f'theorem {thm}' in ltxt and f'Theorem {thm}' in rtxt, f"Theorem name mismatch in {mod}"
        tnf_map[mod] = lean_tnf

        if only_set is not None and mod not in only_set:
            print(f"  [PASS-TM] {mod:6s} ({ns:2d}x{ms}) > {label:14s} (compile skipped by --only)", flush=True)
            continue

        # Compile Lean (-j 1 -M 2048) & verify axioms
        r1 = subprocess.run(['lean', '-j', '1', '-M', '2048', '-o', f'lean/build/BB/{mod}.olean', lp], env=env, capture_output=True, text=True)
        assert r1.returncode == 0 and not r1.stderr.strip() and 'warning:' not in r1.stdout, f"Lean fail on {mod}:\n{r1.stdout}\n{r1.stderr}"
        m_ax = re.search(rf"'{re.escape('BB.' + mod + '.' + thm)}' depends on axioms: \[([^\]]*)\]", r1.stdout)
        assert m_ax, f"Missing #print axioms output for {mod}: {r1.stdout}"
        ax_set = {a.strip() for a in m_ax.group(1).split(',') if a.strip()}
        assert ax_set.issubset(ALLOWED_LEAN_AXIOMS), f"Unexpected Lean axioms for {mod}: {ax_set}"

        # Compile Rocq & verify Closed under the global context
        r2 = subprocess.run(['rocq', 'c', '-Q', 'rocq', 'BB', rp], capture_output=True, text=True)
        assert r2.returncode == 0, f"Rocq fail on {mod}:\n{r2.stdout}\n{r2.stderr}"
        assert 'Closed under the global context' in r2.stdout, f"Rocq not closed for {mod}: {r2.stdout}"

        print(f"  [OK] {mod:6s} ({ns:2d}x{ms}) > {label:14s} | Lean=clean, Rocq=closed, TM=100% identical", flush=True)

    print(f"\n3. Auditing full 2D monotonicity poset (vs Wiki AND mutually among all {len(CHAMPIONS)} champions)...", flush=True)
    # Check against wiki
    for mod, ns, ms, thm, ord_t, k, label, prev in CHAMPIONS:
        for wn, wm, word, wk in WIKI_BOUNDARIES:
            if wn <= ns and wm <= ms:
                assert (ord_t, k) > (word, wk), f"{mod} ({ord_t},{k}) fails to beat wiki BB({wn},{wm}) ({word},{wk})"
    # Check mutually among all champions
    for i, (m1, n1, s1, _, o1, k1, l1, _) in enumerate(CHAMPIONS):
        for j, (m2, n2, s2, _, o2, k2, l2, _) in enumerate(CHAMPIONS):
            if i != j and n1 <= n2 and s1 <= s2:
                assert (o2, k2) > (o1, k1), f"Monotonicity violation: {m2} ({l2}) must beat {m1} ({l1})"
    print(f"  [OK] All {len(CHAMPIONS)} champions strictly beat every dominated wiki entry AND every dominated champion in our set!", flush=True)
    print(f"\nVERIFICATION COMPLETE!!", flush=True)

if __name__ == '__main__':
    main()
