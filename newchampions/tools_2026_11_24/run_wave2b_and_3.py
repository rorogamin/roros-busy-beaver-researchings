"""Surgical Wave 2b (n <= 25 gaps/lifting/fe01 breakthrough) + Wave 3 (epsilon_2 + n=26..33 bonus tier)."""
import argparse
import json
import os
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor, as_completed

from audit_grid import load_hits, load_wiki, print_audit, select_monotone, HITS_PATH, WIKI_PATH
from fgh_order import fmt_expr
from orchestrate import BBSEARCH_EXE, CORES_PATH, HYDRA_EXE, find_matching_seeds, is_hydra_core, load_seed_bank, record_hits
from validator import load_cores_full, parse_tnf, validate_candidate

HERE = os.path.dirname(os.path.abspath(__file__))


def run_task_multi(job: dict) -> dict:
    """Run searcher and return ALL distinct-rank verified irreducible hits (up to 6 per job) for ladder flexibility."""
    t0 = time.time()
    mode = job["mode"]
    core_name = job["core"]
    n = job["n"]
    m = job["m"]
    budget = job["budget"]
    cap = job["cap"]
    seed = job["seed"]
    seed_tm = job.get("seed_tm", "")
    sim_cap = job.get("sim_cap", max(25000, cap + 5000))

    if mode == "hydra":
        cmd = [
            HYDRA_EXE, "--core", core_name, "--cores-file", CORES_PATH,
            "--states", str(n), "--symbols", str(m),
            "--cap", str(cap), "--budget", str(budget), "--seed", str(seed),
        ]
        if seed_tm:
            cmd += ["--seed-tm", seed_tm]
    else:
        cmd = [
            BBSEARCH_EXE, "--mc", "--core", core_name, "--cores-file", CORES_PATH,
            "--states", str(n), "--symbols", str(m),
            "--cap", str(cap), "--budget", str(budget), "--seed", str(seed),
        ]
        if seed_tm:
            cmd += ["--seed-tm", seed_tm]

    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=job.get("timeout", 240))
        out_txt = proc.stdout + "\n" + proc.stderr
    except Exception as e:
        return {"job": job, "valid": [], "elapsed": time.time() - t0, "err": str(e)}

    cand_tms = []
    seen_tm = set()
    for line in out_txt.splitlines():
        s = line.strip()
        if not s or "[unused]" in s:
            continue
        tm_cand = None
        if s.startswith("TM="):
            tm_cand = s[3:].strip()
        elif " | " in s and ("HIT " in s or "NEW BEST" in s):
            tm_cand = s.split(" | ", 1)[1].strip()
        elif "_" in s and len(s) >= 8 and all(ch in "0123456789LRZABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmno-_" for ch in s):
            tm_cand = s
        if tm_cand and tm_cand not in seen_tm:
            seen_tm.add(tm_cand)
            cand_tms.append(tm_cand)

    cores = load_cores_full(CORES_PATH)
    valid_hits = []
    seen_bounds = set()
    for tm_s in reversed(cand_tms):
        res = validate_candidate(core_name, tm_s, cores=cores, sim_cap=sim_cap, post_steps=5000, require_irred=True)
        if res["ok"]:
            bstr = fmt_expr(res["bound_expr"])
            if bstr not in seen_bounds:
                seen_bounds.add(bstr)
                valid_hits.append(res)
                if len(valid_hits) >= 6:
                    break
    return {"job": job, "valid": valid_hits, "elapsed": time.time() - t0}


def dispatch(jobs, label, workers=15):
    print(f"\n=== {label}: {len(jobs)} jobs across {workers} workers ===")
    t0 = time.time()
    hits = 0
    done = 0
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(run_task_multi, j) for j in jobs]
        for fut in as_completed(futs):
            done += 1
            res = fut.result()
            if res["valid"]:
                record_hits(res["valid"])
                hits += len(res["valid"])
                r0 = res["valid"][0]
                print(f"  [{done}/{len(jobs)}] HIT ({r0['n']:2d},{r0['m']}) {r0['core']:15s} -> {fmt_expr(r0['bound_expr'])} (+{len(res['valid'])-1} rungs, {res['elapsed']:.1f}s)")
            elif done % 15 == 0 or done == len(jobs):
                print(f"  [{done}/{len(jobs)}] progress... ({time.time()-t0:.1f}s, valid_hits={hits})")
    print(f"=== {label} finished in {time.time()-t0:.1f}s: {hits} new verified irreducible hits ===")


def best_tm(by_cell, n, m, core_filter=None):
    for r in by_cell.get((n, m), []):
        if core_filter is None or r["core"] == core_filter:
            return r["tm"]
    return ""


def build_wave2b(cores, wiki, seeds):
    by_cell = load_hits(max_n=25)
    jobs = []
    sq = 70001

    def add(n, m, cname, cap, budget, seed_tm="", sim_cap=None):
        nonlocal sq
        mode = "hydra" if is_hydra_core(cname) else "bbsearch"
        jobs.append({
            "mode": mode, "core": cname, "n": n, "m": m,
            "cap": cap, "budget": budget,
            "sim_cap": sim_cap or (cap + 10000),
            "seed": sq, "seed_tm": seed_tm, "timeout": 300,
        })
        sq += 1

    # 1. fe01_5 breakthrough at 22..25 x 5 seeded directly from (21,5) k=227!
    s_21_5 = best_tm(by_cell, 21, 5, "fe01_5")
    for idx, n in enumerate([22, 23, 24, 25]):
        for r in range(3):
            add(n, 5, "fe01_5", 45000 + idx * 5000 + r * 2000, 250000000, s_21_5 if r < 2 else "", 65000)

    # 2. Push 18..20 x 5 (fe01_5) & 18..20 x 6 (fe01_6_17 & fe01_5) past k=215!
    s_18_5 = best_tm(by_cell, 18, 5, "fe01_5")
    s_18_6_17 = best_tm(by_cell, 18, 6, "fe01_6_17")
    s_19_6_5 = best_tm(by_cell, 19, 6, "fe01_5")
    for n in [18, 19, 20]:
        for r in range(4):
            add(n, 5, "fe01_5", 55000, 400000000, s_18_5 if r < 2 else "", 65000)
            add(n, 6, "fe01_6_17", 55000 + (n - 18) * 3000, 400000000, s_18_6_17 if r < 2 else "", 65000)
        add(n, 6, "fe01_5", 55000, 350000000, s_19_6_5 if n >= 19 else s_18_5, 65000)

    # 3. Lift (22,6)=82 -> (23..25, 6) & push (21..23, 9)
    s_22_6 = best_tm(by_cell, 22, 6, "fe1_6")
    for idx, n in enumerate([23, 24, 25]):
        for r in range(2):
            add(n, 6, "fe1_6", 12000 + idx * 3000, 200000000, s_22_6, 20000)
    s_20_9 = best_tm(by_cell, 20, 9, "fe1_8") or best_tm(by_cell, 20, 9)
    s_22_9 = best_tm(by_cell, 22, 9, "fe11_9")
    for r in range(2):
        add(21, 9, "fe11_9", 10000, 200000000, best_tm(by_cell, 21, 9, "fe11_9"), 15000)
        add(23, 9, "fe11_9", 12000, 200000000, s_22_9, 18000)

    # 4. Monotonicity lifting using fixed bbsearch_ultimate.exe
    s_15_6 = best_tm(by_cell, 15, 6, "fwpw3_5")
    for r in range(2):
        add(15, 7, "fwpw3_5", 25000, 150000000, s_15_6, 30000)
        add(15, 7, "fwpw3_7", 25000, 150000000, best_tm(by_cell, 15, 7, "fwpw3_7"), 30000)
    s_9_8 = best_tm(by_cell, 9, 8, "fwpw1_8")
    for r in range(2):
        add(9, 9, "fwpw1_8", 25000, 150000000, s_9_8, 30000)
    s_13_6 = best_tm(by_cell, 13, 6, "fwpw2_6")
    add(13, 7, "fwpw2_6", 20000, 150000000, s_13_6, 25000)

    s_22_3 = best_tm(by_cell, 22, 3, "fwp21_3")
    for n in [23, 24, 25]:
        for r in range(2):
            add(n, 3, "fwp21_3", 20000, 150000000, s_22_3 if r == 0 else best_tm(by_cell, n, 3, "fwp21_3"), 25000)
    add(25, 3, "fwp22_3", 20000, 150000000, "", 25000)

    # 5. (20,4) + 1-step wiki gap pushes
    add(20, 4, "fwp27_4", 20000, 150000000, best_tm(by_cell, 19, 4, "fwp27_4"), 25000)
    add(20, 4, "fwp28_4", 20000, 150000000, "", 25000)
    add(20, 4, "fwp29_4", 20000, 150000000, "", 25000)

    one_step_gaps = [
        (4, 8, "fw4_8"), (4, 9, "fw4_8"),
        (5, 9, "fwm21_8_blank"), (5, 9, "fwm21_8"),
        (8, 7, "fwp22_7"), (9, 4, "fwp2_4"),
        (11, 3, "fwm21_3"), (11, 5, "fwp22_5_sw"), (11, 5, "fwp22_5"),
        (12, 6, "fwpw1_6"), (12, 7, "fwpw1_6"),
        (15, 4, "fwp25_4"), (17, 4, "fwp26_4"),
        (18, 3, "fwp2_3"), (20, 3, "fwp21_3"), (21, 3, "fwp21_3"),
    ]
    for n, m, cn in one_step_gaps:
        ce = cores[cn]
        msds = find_matching_seeds(ce, n, m, seeds)
        stm = best_tm(by_cell, n, m, cn) or (msds[0]["tm"] if msds else "")
        add(n, m, cn, 20000, 150000000, stm, 25000)
        if msds and msds[0]["tm"] != stm:
            add(n, m, cn, 20000, 150000000, msds[0]["tm"], 25000)

    return jobs


def build_wave3_tier(cores, seeds, n_list, cname, m, cap, budget, seed_from_prev=True, copies=3):
    by_cell = load_hits(max_n=35)
    jobs = []
    sq = 90000 + m * 1000
    prev_tm = ""
    if seed_from_prev:
        prev_tm = best_tm(by_cell, n_list[0] - 1, m, cname)
        if not prev_tm:
            ms = find_matching_seeds(cores[cname], n_list[0], m, seeds)
            prev_tm = ms[0]["tm"] if ms else ""
    for n in n_list:
        cur_best = best_tm(by_cell, n, m, cname)
        for c in range(copies):
            stm = cur_best if (c == 0 and cur_best) else (prev_tm if (c <= 1 and prev_tm) else "")
            jobs.append({
                "mode": "hydra" if is_hydra_core(cname) else "bbsearch",
                "core": cname, "n": n, "m": m,
                "cap": cap, "budget": budget, "sim_cap": max(cap + 5000, 20000),
                "seed": sq, "seed_tm": stm, "timeout": 300,
            })
            sq += 1
    return jobs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=["2b", "3", "all"], default="all")
    ap.add_argument("--workers", type=int, default=15)
    args = ap.parse_args()

    cores = load_cores_full(CORES_PATH)
    wiki, raw_wiki, floors, _ = load_wiki(WIKI_PATH)
    seeds = load_seed_bank(cores, wiki)

    if args.stage in ("2b", "all"):
        jobs_2b = build_wave2b(cores, wiki, seeds)
        dispatch(jobs_2b, "Wave 2b (Surgical Rescue & Breakthrough)", workers=args.workers)

    if args.stage in ("3", "all"):
        # Stage 3A: Crown Jewels (25,8) fe2_8 [12 parallel seeds] + (24,9) fe2_9 [6 seeds]
        by_cell = load_hits(max_n=35)
        jobs_cj = []
        sq = 95001
        s_25_8 = best_tm(by_cell, 25, 8, "fe2_8")
        # Also pull any non-irred fe2_8 >=4 if none irred exists yet
        if not s_25_8:
            # Check raw hits_ultimate or seed with fe2_8 cold starts
            pass
        for i in range(12):
            jobs_cj.append({
                "mode": "hydra", "core": "fe2_8", "n": 25, "m": 8,
                "cap": 3500 + (i % 3) * 1500, "budget": 400000000, "sim_cap": 15000,
                "seed": sq + i, "seed_tm": s_25_8 if (s_25_8 and i < 6) else "", "timeout": 300,
            })
        s_24_9 = best_tm(by_cell, 24, 9, "fe2_9")
        for i in range(6):
            jobs_cj.append({
                "mode": "hydra", "core": "fe2_9", "n": 24, "m": 9,
                "cap": 4000, "budget": 300000000, "sim_cap": 15000,
                "seed": sq + 100 + i, "seed_tm": s_24_9 if (s_24_9 and i < 3) else "", "timeout": 300,
            })
        dispatch(jobs_cj, "Wave 3A (Crown Jewels 25x8 fe2_8 & 24x9 fe2_9)", workers=args.workers)

        # Stage 3B: Lift 24x9 -> 25x9, plus Extended n=26..33 tier across cols 5..9 (and 26..30 col 3)!
        by_cell = load_hits(max_n=35)
        s_24_9_new = best_tm(by_cell, 24, 9, "fe2_9")
        jobs_ext = []
        sq = 98001
        for i in range(6):
            jobs_ext.append({
                "mode": "hydra", "core": "fe2_9", "n": 25, "m": 9,
                "cap": 5000 + i * 500, "budget": 300000000, "sim_cap": 15000,
                "seed": sq + i, "seed_tm": s_24_9_new if (s_24_9_new and i < 4) else "", "timeout": 300,
            })
        # Extended rows n=26..33
        specs = [
            (list(range(26, 34)), "fe01_5", 5, 50000, 150000000),
            (list(range(26, 34)), "fe1_6",  6, 10000, 120000000),
            (list(range(26, 34)), "fe11_7", 7,  8000, 150000000),
            (list(range(26, 34)), "fe2_8",  8,  5000, 200000000),
            (list(range(26, 34)), "fe2_9",  9,  6000, 200000000),
            (list(range(26, 31)), "fwp21_3", 3, 20000, 100000000),
        ]
        for nlist, cn, col, cap, bud in specs:
            # Seed from best available in column col (at <= 25)
            seed_pool = []
            for sn in range(25, 17, -1):
                t = best_tm(by_cell, sn, col, cn)
                if t:
                    seed_pool.append(t)
                    if len(seed_pool) >= 2:
                        break
            for idx, n in enumerate(nlist):
                for c in range(2):
                    stm = seed_pool[0] if (seed_pool and c == 0) else ""
                    jobs_ext.append({
                        "mode": "hydra" if is_hydra_core(cn) else "bbsearch",
                        "core": cn, "n": n, "m": col,
                        "cap": cap + idx * 1000, "budget": bud, "sim_cap": max(cap + 10000, 20000),
                        "seed": sq, "seed_tm": stm, "timeout": 300,
                    })
                    sq += 1
        dispatch(jobs_ext, "Wave 3B (25x9 fe2_9 + Extended n=26..33 Bonus Tier)", workers=args.workers)


if __name__ == "__main__":
    main()
