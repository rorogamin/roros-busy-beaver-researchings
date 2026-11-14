import sys, types, io, contextlib, functools, re, os

BUNDLE_CET = "/working_dir/c_b910ffe159ae7b24/bundle/CET"
BUNDLE_ROCQ = "/working_dir/c_b910ffe159ae7b24/bundle/rocq"

et_lines = open(os.path.join(BUNDLE_CET, "eval_towers.py")).read().splitlines()
cut = next(i for i, l in enumerate(et_lines) if l.startswith("process_file("))
et_src = "\n".join(et_lines[:cut]).replace(r"c:\Users\Rowan\Documents\st\bbwork\bb-variants\CET", BUNDLE_CET)
et_mod = types.ModuleType("eval_towers")
exec(et_src, et_mod.__dict__)
sys.modules["eval_towers"] = et_mod

v_lines = open(os.path.join(BUNDLE_CET, "verify_all3_champions.py")).read().splitlines()
v_src = "\n".join(v_lines[:112]).replace("bbwork/bb-variants/CET/", BUNDLE_CET + "/").replace(r"c:\Users\Rowan\Documents\st\bbwork\bb-variants\CET", BUNDLE_CET)
v_mod = types.ModuleType("verify_all3_champions")
exec(v_src, v_mod.__dict__)
sys.modules["verify_all3_champions"] = v_mod

te_src = open(os.path.join(BUNDLE_CET, "true_exact_eval.py")).read().replace("bbwork/bb-variants/CET/", BUNDLE_CET + "/")
te_src = "import functools\n" + te_src
te_src = te_src.replace("def carmichael_lambda(n):", "@functools.lru_cache(None)\ndef carmichael_lambda(n):")
te_src = te_src.replace("    def get_L_mod(r, Q):", "    _memo = {}\n    def get_L_mod(r, Q):\n        if (r, Q) in _memo: return _memo[(r, Q)]")
te_src = te_src.replace("        return L_next_mod", "        _memo[(r, Q)] = L_next_mod\n        return L_next_mod")
te_cut = te_src.index("cet3_line =")
te_mod = types.ModuleType("true_exact_eval")
exec(te_src[:te_cut], te_mod.__dict__)

print("=== 1. VERIFYING NEW CET(4) CHAMPION (R=31) ===")
cet4_line = next(l.strip() for l in open("/working_dir/c_b910ffe159ae7b24/mechs_cet4_hm.txt")
                 if l.startswith("1LB1RA_1RC0LD_1LA0LB_0RB0RA|1RB0LC_1LA0RC_1LD0RA_1RC1RA\t"))
with contextlib.redirect_stdout(io.StringIO()):
    P, D, M, mg, te = te_mod.build_true_table("CET4_R31", cet4_line, 2)
st, rounds, seq, hstp = te_mod.eval_exact_seq(P, D, M, mg, te, 30, 116, max_rounds=40)
print(f"CET(4) R=31: status={st}, rounds={rounds}, halt_step={hstp}, seq={seq}")
assert st == "HALT" and rounds == 31 and hstp == 30

print("\n=== 2. VERIFYING NEW CET(2,3) CHAMPION (R=10) ===")
cet23_line = next(l.strip() for l in open(os.path.join(BUNDLE_CET, "all_high_cet23_t2.txt"))
                  if "1LB2LB2RA_1RB1RA0LB|0RB2RB2LB_2LA1RB1LA\t" in l)
mech23 = "\t".join(cet23_line.split("\t")[1:])
with contextlib.redirect_stdout(io.StringIO()):
    P, D, M, mg, te = te_mod.build_true_table("CET23_R10", mech23, 3)
st, rounds, seq, hstp = te_mod.eval_exact_seq(P, D, M, mg, te, 12, 84, max_rounds=30)
print(f"CET(2,3) R=10: status={st}, rounds={rounds}, halt_step={hstp}, seq={seq}")
assert st == "HALT" and rounds == 10 and hstp == 9

print("\n=== 3. VERIFYING BLANK-TAPE EPS1 MACHINE (btbl_eps1_clean) ===")
txt = open(os.path.join(BUNDLE_ROCQ, "Eps1Tape.v")).read()
tbl = {}
for m in re.finditer(r"\|\s*(\d+),\s*(bl|on)\s*=>\s*Some\s*\((bl|on),\s*(true|false),\s*(\d+)\)", txt):
    s, b, w, d, ns = int(m.group(1)), (0 if m.group(2)=="bl" else 1), (0 if m.group(3)=="bl" else 1), (1 if m.group(4)=="true" else -1), int(m.group(5))
    tbl[(s, b)] = (w, d, ns)

# Add 12-state blank-tape prologue
btbl = {(s + 12, b): (w, d, ns + 12) for (s, b), (w, d, ns) in tbl.items()}
prologue = {
    (0, 0): (1, -1, 1), (0, 1): (1, -1, 1),
    (1, 0): (0, -1, 2), (1, 1): (0, -1, 2),
    (2, 0): (1, -1, 3), (2, 1): (1, -1, 3),
    (3, 0): (0, -1, 4), (3, 1): (0, -1, 4),
    (4, 0): (0, -1, 5), (4, 1): (0, -1, 5),
    (5, 0): (1, -1, 6), (5, 1): (1, -1, 6),
    (6, 0): (0, -1, 7), (6, 1): (0, -1, 7),
    (7, 0): (0, -1, 8), (7, 1): (0, -1, 8),
    (8, 0): (1, -1, 9), (8, 1): (1, -1, 9),
    (9, 0): (1,  1, 10), (9, 1): (1,  1, 10),
    (10, 1): (1, 1, 10), (10, 0): (0, 1, 11),
    (11, 0): (0, 1, 12 + 33), (11, 1): (0, 1, 12 + 33),
}
btbl.update(prologue)

tape = {}; pos = 0; st = 0
for t in range(1, 1000):
    sym = tape.get(pos, 0)
    if t == 15:
        print(f"After prologue (14 steps): pos={pos}, st={st} (expected 45=12+ENTRY)")
        assert st == 12 + 33 and pos == -5
    if (st, sym) not in btbl:
        ones = sum(tape.values())
        print(f"btbl_eps1_clean HALTED from blank tape at step {t-1}, pos={pos}, st={st}, ones={ones}")
        break
    w, d, ns = btbl[(st, sym)]
    tape[pos] = w; pos += d; st = ns
print("ALL VERIFICATIONS PASSED!")