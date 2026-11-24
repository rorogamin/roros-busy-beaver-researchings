"""15-core parallel Busy Beaver champion search orchestrator.
Supports Wave 1 (broad sweep across 3..25 x 3..9), Wave 2 (seeded LNS lifting + m=2),
and Wave 3 (epsilon-2 crown jewels + optional n=26..30 bonus tier).
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Dict, List, Optional, Tuple

from fgh_order import FVal, Ord, parse_core_bound, strictly_beats, fmt_expr
from validator import load_cores_full, validate_candidate, parse_tnf, check_core_preserved
from audit_grid import load_wiki, load_hits, select_monotone, HITS_PATH, WIKI_PATH

HERE = os.path.dirname(os.path.abspath(__file__))
CORES_PATH = os.path.join(HERE, "bbcores_ultimate.txt")
BBSEARCH_EXE = os.path.join(HERE, "bbsearch_ultimate.exe")
HYDRA_EXE = os.path.join(HERE, "find_hydra_boot.exe")
RACH2_BOOST_EXE = os.path.join(os.path.dirname(HERE), "search", "rach2_boost.exe")

SKIP_CORES = {"fe12_9_23"}

def is_hydra_core(name: str) -> bool:
    return name.startswith("fe")

def is_usable_core(name: str) -> bool:
    if name in SKIP_CORES:
        return False
    if name.endswith("_fix"):
        return False
    return True

def load_seed_bank(cores: dict, wiki: dict) -> List[dict]:
    """Load compatible verified TMs from wiki_live, Nov 21 JSON, Rocq BB*.v, and prior hits."""
    seeds = []
    seen_tm = set()

    def add_seed(src: str, tm: str):
        if not tm or tm in seen_tm or "[unused]" in tm:
            return
        try:
            n, m, _ = parse_tnf(tm)
        except Exception:
            return
        seen_tm.add(tm)
        seeds.append({"src": src, "n": n, "m": m, "tm": tm})

    # 1. Existing hits_ultimate.jsonl
    if os.path.exists(HITS_PATH):
        with open(HITS_PATH, "r", encoding="utf-8") as f:
            for line in f:
                try:
                    rec = json.loads(line)
                    add_seed(f"hit_{rec.get('core','')}", rec.get("tm", ""))
                except Exception:
                    pass

    # 2. Live wiki
    for k, cell in wiki["cells"].items():
        add_seed(f"wiki_{k}", cell.get("tm", ""))

    # 3. Nov 21 JSON
    nov21_path = r"E:\Projects\st\bbwork\newchampions\champions_2026_11_21.json"
    if os.path.exists(nov21_path):
        try:
            for item in json.load(open(nov21_path, "r", encoding="utf-8")):
                add_seed(f"nov21_{item['states']}x{item['symbols']}", item.get("tm", ""))
        except Exception:
            pass

    # 4. Rocq BB*.v
    pat = re.compile(r"\|\s*(\d+),\s*(\d+)\s*=>\s*Some\s*\(mkAction\s+(\d+)\s+(DL|DR)\s+\((None|Some\s+(\d+))\)\)")
    for p in glob.glob(r"E:\Projects\st\bbwork\newchampions\rocq\BB*.v"):
        try:
            txt = open(p, "r", encoding="utf-8").read()
            matches = pat.findall(txt)
            if not matches:
                continue
            d = {}
            for s, y, w, dr, ns, _n in matches:
                ns2 = "Z" if ns == "None" else (chr(65 + int(_n)) if int(_n) < 25 else chr(97 + int(_n) - 25))
                d[(int(s), int(y))] = f"{w}" + ("L" if dr == "DL" else "R") + ns2
            ns = max(s for s, _ in d) + 1
            ms = max(y for _, y in d) + 1
            if ns <= 40 and ms <= 9:
                rows = ["".join(d.get((s, y), "---") for y in range(ms)) for s in range(ns)]
                add_seed(f"rocq_{os.path.basename(p)}", "_".join(rows))
        except Exception:
            pass

    return seeds


def find_matching_seeds(core_entry: dict, n: int, m: int, seeds: List[dict]) -> List[dict]:
    """Return all seeds with seed.n <= n and seed.m <= m whose core rows match core_entry."""
    crows = core_entry["rows"]
    nf, nsym = core_entry["nfixed"], core_entry["nsym"]
    out = []
    for sd in seeds:
        if sd["n"] > n or sd["m"] > m or sd["n"] < nf or sd["m"] < nsym:
            continue
        trows = sd["tm"].split("_")
        ok = True
        for s in range(nf):
            for y in range(nsym):
                cc = crows[s][3 * y : 3 * y + 3]
                if cc != "---" and trows[s][3 * y : 3 * y + 3] != cc:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(sd)
    # Prefer highest-ranked hit seeds first, then exact (n, m) or closest (n, m)
    out.sort(key=lambda s: (1 if s.get("rank") is not None else 0, s.get("rank") or (), 1 if (s["n"] == n and s["m"] == m) else 0, s["n"], s["m"]), reverse=True)
    return out


def core_peak_expr(name: str):
    args = {"k": 2000, "m": 4, "n": 2500, "p": 2500, "q": 2500, "r": 2500, "s": 2500, "t": 2500, "c": 5}
    return parse_core_bound(name, args)


def rank_core_tuple(name: str, ce: dict) -> tuple:
    e = core_peak_expr(name)
    if e is None:
        return (0, 0, 0, ce["nfixed"], ce["nsym"])
    return (1, e.ord.tier, e.ord.off, ce["nfixed"], ce["nsym"])


def run_single_task(job: dict) -> dict:
    """Worker process: invoke searcher exe, parse all candidate TMs, validate in Python."""
    t0 = time.time()
    mode = job["mode"]
    core_name = job["core"]
    n = job["n"]
    m = job["m"]
    budget = job["budget"]
    cap = job["cap"]
    seed = job["seed"]
    seed_tm = job.get("seed_tm", "")
    sim_cap = job.get("sim_cap", max(25000, cap))

    if mode == "hydra":
        cmd = [
            HYDRA_EXE,
            "--core", core_name,
            "--cores-file", CORES_PATH,
            "--states", str(n),
            "--symbols", str(m),
            "--cap", str(cap),
            "--budget", str(budget),
            "--seed", str(seed),
        ]
        if seed_tm:
            cmd += ["--seed-tm", seed_tm]
    else:
        cmd = [
            BBSEARCH_EXE,
            "--mc",
            "--core", core_name,
            "--cores-file", CORES_PATH,
            "--states", str(n),
            "--symbols", str(m),
            "--cap", str(cap),
            "--budget", str(budget),
            "--seed", str(seed),
        ]
        if seed_tm:
            cmd += ["--seed-tm", seed_tm]

    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=job.get("timeout", 180))
        out_txt = proc.stdout + "\n" + proc.stderr
    except subprocess.TimeoutExpired:
        return {"job": job, "valid": [], "elapsed": time.time() - t0, "err": "timeout"}
    except Exception as e:
        return {"job": job, "valid": [], "elapsed": time.time() - t0, "err": str(e)}

    # Extract all candidate TNF strings (preferring irred=1 or last/best candidates)
    cand_tms = []
    seen = set()
    for line in out_txt.splitlines():
        s = line.strip()
        if not s:
            continue
        tm_cand = None
        if s.startswith("TM="):
            tm_cand = s[3:].strip()
        elif " | " in s and ("HIT " in s or "NEW BEST" in s):
            tm_cand = s.split(" | ", 1)[1].strip()
        elif "_" in s and "[unused]" not in s and len(s) >= 8 and all(ch in "0123456789LRZABCDEFGHIJKLMNOPQRSTUVWXYYabcdefghijklmno-_" for ch in s):
            tm_cand = s
        if tm_cand and tm_cand not in seen and "[unused]" not in tm_cand:
            seen.add(tm_cand)
            cand_tms.append(tm_cand)

    # Also test up to last 6 unique candidates (newest/best first)
    cores = load_cores_full(CORES_PATH)
    valid_hits = []
    for tm_s in reversed(cand_tms[-8:]):
        res = validate_candidate(core_name, tm_s, cores=cores, sim_cap=sim_cap, post_steps=5000, require_irred=True)
        if res["ok"]:
            valid_hits.append(res)
            break  # already testing newest/best first!
    # Also fallback check all if reversed[-8:] didn't get irred=1 (e.g. best became non-irred while earlier hit was irred!)
    if not valid_hits and len(cand_tms) > 0:
        for tm_s in reversed(cand_tms):
            if "[unused]" in tm_s:
                continue
            res = validate_candidate(core_name, tm_s, cores=cores, sim_cap=sim_cap, post_steps=5000, require_irred=True)
            if res["ok"]:
                valid_hits.append(res)
                break

    return {"job": job, "valid": valid_hits, "elapsed": time.time() - t0, "ncand": len(cand_tms)}


def record_hits(valid_list: List[dict]):
    if not valid_list:
        return
    with open(HITS_PATH, "a", encoding="utf-8") as f:
        for r in valid_list:
            out = {
                "ok": True,
                "core": r["core"],
                "n": r["n"],
                "m": r["m"],
                "step": r["step"],
                "args": r["args"],
                "bound": fmt_expr(r["bound_expr"]),
                "used_states": r["used_states"],
                "used_syms": r["used_syms"],
                "irred": r["irred"],
                "tm": r["tm"],
            }
            f.write(json.dumps(out, ensure_ascii=False) + "\n")


def run_jobs(jobs: List[dict], workers: int = 15, label: str = "Batch"):
    print(f"\n=== Launching {label}: {len(jobs)} jobs across {workers} workers ===")
    t0 = time.time()
    hits = 0
    done = 0
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(run_single_task, j) for j in jobs]
        for fut in as_completed(futs):
            done += 1
            res = fut.result()
            if res["valid"]:
                record_hits(res["valid"])
                hits += len(res["valid"])
                r0 = res["valid"][0]
                if done % 5 == 0 or r0["core"].startswith("fe"):
                    print(f"  [{done}/{len(jobs)}] HIT ({r0['n']:2d},{r0['m']}) {r0['core']:16s} -> {fmt_expr(r0['bound_expr'])} (step={r0['step']}, {res['elapsed']:.1f}s)")
            elif done % 25 == 0 or done == len(jobs):
                print(f"  [{done}/{len(jobs)}] progress... ({time.time()-t0:.1f}s, valid_hits={hits})")
    print(f"=== {label} finished in {time.time()-t0:.1f}s: {hits} new verified irreducible hits ===")


def build_wave1_jobs(cores: dict, wiki: dict, raw_wiki: dict, floors: dict, seeds: List[dict]) -> List[dict]:
    jobs = []
    seed_seq = 1001
    for n in range(3, 26):
        for m in range(3, 10):
            fl = floors.get((n, m))
            # Candidate usable cores fitting in (n, m) whose peak expression can beat floor
            compat = []
            for cname, ce in cores.items():
                if not is_usable_core(cname):
                    continue
                if ce["nfixed"] > n or ce["nsym"] > m:
                    continue
                pk = core_peak_expr(cname)
                if pk is None:
                    continue
                if fl is None or strictly_beats(pk, fl):
                    compat.append((rank_core_tuple(cname, ce), cname, ce))
            compat.sort(reverse=True)
            # Pick top 3 distinct cores per cell
            chosen = compat[:3]
            for _, cname, ce in chosen:
                mode = "hydra" if is_hydra_core(cname) else "bbsearch"
                matching = find_matching_seeds(ce, n, m, seeds)
                cap = 20000
                budget = 60000000
                sim_cap = 25000
                if mode == "hydra":
                    cap = 2500
                    budget = 80000000
                    sim_cap = 10000
                    if cname in ("fe01_5", "fe0_5_16"):
                        cap = 8000
                        budget = 100000000
                        sim_cap = 15000
                # Run seeded job if match exists, plus 1 cold/extra seed for high-value blank/fe cells
                if matching:
                    jobs.append({
                        "mode": mode, "core": cname, "n": n, "m": m,
                        "cap": cap, "budget": budget, "sim_cap": sim_cap,
                        "seed": seed_seq, "seed_tm": matching[0]["tm"], "timeout": 120,
                    })
                    seed_seq += 1
                if not matching or mode == "hydra":
                    jobs.append({
                        "mode": mode, "core": cname, "n": n, "m": m,
                        "cap": cap, "budget": budget, "sim_cap": sim_cap,
                        "seed": seed_seq, "seed_tm": "", "timeout": 120,
                    })
                    seed_seq += 1
    return jobs


def build_wave2_jobs(cores: dict, wiki: dict, raw_wiki: dict, floors: dict, seeds: List[dict]) -> List[dict]:
    """Target gaps, ties, monotonicity conflicts, and lifting winners into empty/blocked neighbors."""
    by_cell = load_hits(max_n=25)
    sel = select_monotone(by_cell, raw_wiki, n_max=25, m_max=9)
    jobs = []
    seed_seq = 50001

    ext_seeds = []
    for (hn, hm), lst in by_cell.items():
        for rec in lst[:3]:
            ext_seeds.append({"src": f"hit_{rec['core']}_{hn}x{hm}", "n": hn, "m": hm, "tm": rec["tm"], "rank": rec["rank"]})
    ext_seeds.extend(seeds)

    for n in range(3, 26):
        for m in range(3, 10):
            if (n, m) in sel:
                continue  # already cleanly winning in monotone grid!
            fl = floors.get((n, m))
            compat = []
            seen_cores = set()

            # 1) Prioritize any core that won/hit cleanly in (n-1,m), (n,m-1), or (n,m) itself!
            for pn, pm in [(n, m), (n - 1, m), (n, m - 1)]:
                for rec in (by_cell.get((pn, pm), [])[:2]):
                    cn = rec["core"]
                    if cn in seen_cores or not is_usable_core(cn) or cn not in cores:
                        continue
                    ce = cores[cn]
                    if ce["nfixed"] <= n and ce["nsym"] <= m:
                        pk = core_peak_expr(cn)
                        if pk is not None and (fl is None or strictly_beats(pk, fl)):
                            seen_cores.add(cn)
                            compat.append((rank_core_tuple(cn, ce), cn, ce))

            # 2) Plus top compatible cores from bbcores_ultimate
            all_compat = []
            for cname, ce in cores.items():
                if cname in seen_cores or not is_usable_core(cname):
                    continue
                if ce["nfixed"] > n or ce["nsym"] > m:
                    continue
                pk = core_peak_expr(cname)
                if pk is not None and (fl is None or strictly_beats(pk, fl)):
                    all_compat.append((rank_core_tuple(cname, ce), cname, ce))
            all_compat.sort(reverse=True)
            chosen = compat[:2] + all_compat[:2]
            if not chosen:
                chosen = all_compat[:2]

            for _, cname, ce in chosen[:3]:
                mode = "hydra" if is_hydra_core(cname) else "bbsearch"
                matching = find_matching_seeds(ce, n, m, ext_seeds)
                if mode == "bbsearch":
                    cap = 20000
                    budget = 120000000
                    sim_cap = 25000
                elif cname in ("fe01_5", "fe0_5_16", "fe01_6_17"):
                    cap = 35000
                    budget = 250000000
                    sim_cap = 40000
                else:
                    cap = 8000
                    budget = 200000000
                    sim_cap = 15000

                # Best distinct seed (if any) + 1 cold start (or second seed if hydra)
                if matching:
                    jobs.append({
                        "mode": mode, "core": cname, "n": n, "m": m,
                        "cap": cap, "budget": budget, "sim_cap": sim_cap,
                        "seed": seed_seq, "seed_tm": matching[0]["tm"], "timeout": 240,
                    })
                    seed_seq += 1
                    if len(matching) > 1 and mode == "hydra":
                        jobs.append({
                            "mode": mode, "core": cname, "n": n, "m": m,
                            "cap": cap, "budget": budget, "sim_cap": sim_cap,
                            "seed": seed_seq, "seed_tm": matching[1]["tm"], "timeout": 240,
                        })
                        seed_seq += 1
                else:
                    jobs.append({
                        "mode": mode, "core": cname, "n": n, "m": m,
                        "cap": cap, "budget": budget, "sim_cap": sim_cap,
                        "seed": seed_seq, "seed_tm": "", "timeout": 240,
                    })
                    seed_seq += 1
    return jobs


def build_wave3_jobs(cores: dict, raw_wiki: dict, seeds: List[dict], include_bonus: bool = True) -> List[dict]:
    """Focused 15-core push on epsilon_2 crown jewels (fe2_8 at 25x8, fe2_9 at 24x9 & 25x9)
    plus optional bonus n=26..30 tier!
    """
    by_cell = load_hits(max_n=35)
    ext_seeds = list(seeds)
    for (n, m), lst in by_cell.items():
        if lst:
            ext_seeds.append({"src": f"hit_{n}x{m}", "n": n, "m": m, "tm": lst[0]["tm"]})

    jobs = []
    seed_seq = 90001

    # Crown jewels: 15-seed attack on (25,8) fe2_8, (24,9) fe2_9, (25,9) fe2_9
    targets = [(25, 8, "fe2_8", 400000000, 2500), (24, 9, "fe2_9", 300000000, 2500), (25, 9, "fe2_9", 300000000, 2500)]
    for n, m, cname, budget, cap in targets:
        ce = cores[cname]
        matching = find_matching_seeds(ce, n, m, ext_seeds)
        for i in range(6):
            sd_tm = matching[i % len(matching)]["tm"] if (matching and i < 3) else ""
            jobs.append({
                "mode": "hydra", "core": cname, "n": n, "m": m,
                "cap": cap, "budget": budget, "sim_cap": 10000,
                "seed": seed_seq, "seed_tm": sd_tm, "timeout": 240,
            })
            seed_seq += 1

    # Also strengthen 23..25 x 7 (fe11_7) and 21..25 x 8 (fe11_8) and 20..25 x 9 (fe11_9) if weak
    for n, m, cname in [
        (23, 7, "fe11_7"), (24, 7, "fe11_7"), (25, 7, "fe11_7"),
        (21, 8, "fe11_8"), (22, 8, "fe11_8"), (23, 8, "fe11_8"), (24, 8, "fe11_8"),
    ]:
        ce = cores[cname]
        matching = find_matching_seeds(ce, n, m, ext_seeds)
        for i in range(3):
            sd_tm = matching[i % len(matching)]["tm"] if (matching and i == 0) else ""
            jobs.append({
                "mode": "hydra", "core": cname, "n": n, "m": m,
                "cap": 2500, "budget": 200000000, "sim_cap": 10000,
                "seed": seed_seq, "seed_tm": sd_tm, "timeout": 180,
            })
            seed_seq += 1

    if include_bonus:
        bonus_specs = [
            (26, 3, "fwp22_3"), (27, 3, "fwp22_3"), (28, 3, "fwp22_3"),
            (26, 4, "fwp2_10_4"), (27, 4, "fwp2_10_4"), (28, 4, "fwp2_10_4"),
            (26, 5, "fe01_5"), (27, 5, "fe01_5"), (28, 5, "fe01_5"),
            (26, 6, "fe1_6"), (27, 6, "fe1_6"), (28, 6, "fe1_6"),
            (26, 7, "fe11_7"), (27, 7, "fe11_7"), (28, 7, "fe11_7"),
            (26, 8, "fe2_8"), (27, 8, "fe2_8"), (28, 8, "fe2_8"),
            (26, 9, "fe2_9"), (27, 9, "fe2_9"), (28, 9, "fe2_9"),
        ]
        for n, m, cname in bonus_specs:
            ce = cores[cname]
            mode = "hydra" if is_hydra_core(cname) else "bbsearch"
            matching = find_matching_seeds(ce, n, m, ext_seeds)
            cap = 20000 if mode == "bbsearch" else (10000 if cname == "fe01_5" else 2500)
            budget = 100000000 if mode == "bbsearch" else 150000000
            for sd in matching[:1]:
                jobs.append({
                    "mode": mode, "core": cname, "n": n, "m": m,
                    "cap": cap, "budget": budget, "sim_cap": max(10000, cap),
                    "seed": seed_seq, "seed_tm": sd["tm"], "timeout": 180,
                })
                seed_seq += 1
            jobs.append({
                "mode": mode, "core": cname, "n": n, "m": m,
                "cap": cap, "budget": budget, "sim_cap": max(10000, cap),
                "seed": seed_seq, "seed_tm": "", "timeout": 180,
            })
            seed_seq += 1
    return jobs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wave", type=int, choices=[1, 2, 3], required=True)
    ap.add_argument("--workers", type=int, default=15)
    ap.add_argument("--no-bonus", action="store_true")
    args = ap.parse_args()

    cores = load_cores_full(CORES_PATH)
    wiki, raw_wiki, floors, _ = load_wiki(WIKI_PATH)
    seeds = load_seed_bank(cores, wiki)
    print(f"Loaded {len(cores)} cores, {len(seeds)} seeds.")

    if args.wave == 1:
        jobs = build_wave1_jobs(cores, wiki, raw_wiki, floors, seeds)
        run_jobs(jobs, workers=args.workers, label="Wave 1 (Broad Sweep)")
    elif args.wave == 2:
        jobs = build_wave2_jobs(cores, wiki, raw_wiki, floors, seeds)
        run_jobs(jobs, workers=args.workers, label="Wave 2 (Seeded LNS Gap Rescue)")
    elif args.wave == 3:
        jobs = build_wave3_jobs(cores, raw_wiki, seeds, include_bonus=not args.no_bonus)
        run_jobs(jobs, workers=args.workers, label="Wave 3 (Epsilon-2 Crown Jewels + Bonus)")


if __name__ == "__main__":
    main()
