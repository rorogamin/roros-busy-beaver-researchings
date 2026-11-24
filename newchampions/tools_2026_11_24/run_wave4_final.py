"""Wave 4 Final Sweep:
Stage 4A: n <= 25 surgical monotonicity lifts + fe2_8 crown jewel + fe01 215+ breakthrough
Stage 4B: Row-by-row ascending n=26..35 extended champion tier across cols 3, 5, 6, 7, 8, 9
"""
import argparse
import os
import time
from audit_grid import load_hits, load_wiki
from fgh_order import fmt_expr
from orchestrate import find_matching_seeds, is_hydra_core, load_seed_bank, CORES_PATH, WIKI_PATH
from run_wave2b_and_3 import best_tm, dispatch
from validator import load_cores_full

HERE = os.path.dirname(os.path.abspath(__file__))

FE2_8_SEED_N4 = (
    "6LE1LN0RK0RM4LN0RQ0RX7LN_1RZ1RB2LI7LN1RB5LI6LI6LT_0LI5RC2RC3RC2RC5RC6RC6RC_"
    "1LE1RD2RD3RD7LY5RD6RD---_3LO1LE2LE3LE---5LE6LE---_0LG1RF2RF3RF1LR5RF6RF---_"
    "0RI0LH---3RI4RI------7RI_2LO1LH2LH3LH5LO5LH6LH6LO_3RP4RC0LO0LI---2LS5LV---_"
    "2RA0RF2LJ3LJ0RF5LJ6LJ0RD_2LU1RK2RK3RK4RK5RK6RK7RK_3RA1LL2LL3LL4LL5LL6LL7LL_"
    "3LL1RM2RM3RM4RM5RM6RM7RM_1RB1LN2LN3LN1LO5LN6LN---_1RB4RP0RF0RD1LN4RF7RF---_"
    "4LJ1RP2RP3RP0RP5RP6RP7RP_5LR1RQ2RQ3RQ4RQ5RQ6RQ7RQ_5RA1LR2LR3LR4LR5LR6LR7LR_"
    "1RB4RT2LS3LS4LS5LS6LS---_2LS6LW2RT3RT4RT5RT6RT---_2RA1LU2LU3LU4LU5LU6LU7LU_"
    "1RB4RW2LV3LV4LV5LV6LV---_5LV6RS2RW3RW4RW5RW6RW---_6LY1RX2RX3RX4RX5RX6RX7RX_"
    "6RA1LY2LY3LY4LY5LY6LY7LY"
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=15)
    ap.add_argument("--skip-4a", action="store_true")
    args = ap.parse_args()

    cores = load_cores_full(CORES_PATH)
    wiki, raw_wiki, floors, _ = load_wiki(WIKI_PATH)
    seeds = load_seed_bank(cores, wiki)

    if not args.skip_4a:
        by_cell = load_hits(max_n=25)
        jobs = []
        sq = 110001

        def add(n, m, cn, cap, budget, stm="", sim_cap=None):
            nonlocal sq
            cap = min(cap, 64500)
            jobs.append({
                "mode": "hydra" if is_hydra_core(cn) else "bbsearch",
                "core": cn, "n": n, "m": m,
                "cap": cap, "budget": budget,
                "sim_cap": sim_cap or (cap + 10000),
                "seed": sq, "seed_tm": stm, "timeout": 300,
            })
            sq += 1

        # 1. fe01_5 (23..25, 5) seeded from (22,5)=231 (and 21,5=227 fallback)
        s_22_5 = best_tm(by_cell, 22, 5, "fe01_5") or best_tm(by_cell, 21, 5, "fe01_5")
        for idx, n in enumerate([23, 24, 25]):
            for r in range(3):
                add(n, 5, "fe01_5", 50000 + idx * 4500 + r * 1500, 250000000, s_22_5, 68000)

        # 2. (24,6) fe1_6 from (23,6)=87, (23,7) fe11_7 from (24,7)=39 / cold, (25,6) lift
        s_23_6 = best_tm(by_cell, 23, 6, "fe1_6")
        for r in range(3):
            add(24, 6, "fe1_6", 14000 + r * 2000, 150000000, s_23_6, 22000)
        s_24_7 = best_tm(by_cell, 24, 7, "fe11_7")
        for r in range(4):
            add(23, 7, "fe11_7", 6000 + r * 1000, 250000000, "" if r < 2 else s_24_7[:0], 15000)

        # 3. (18..20, 6) fe01_6_17 from 20x6=209 & 18x6=204 & (18..20,5) to break 215
        s_20_6 = best_tm(by_cell, 20, 6, "fe01_6_17")
        s_18_6 = best_tm(by_cell, 18, 6, "fe01_6_17")
        for n in [18, 19, 20]:
            for r in range(3):
                stm = s_18_6 if (n == 18 and r < 2) else (s_20_6 if (n == 20 and r < 2) else s_18_6)
                add(n, 6, "fe01_6_17", 64000, 400000000, stm if r < 2 else "", 72000)
            s_18_5 = best_tm(by_cell, 18, 5, "fe01_5")
            for r in range(2):
                add(n, 5, "fe01_5", 64000, 400000000, s_18_5 if r == 0 else "", 72000)

        # 4. (25,8) fe2_8 crown jewel (10 parallel seeds mixing cold + n=4 seed)
        for r in range(10):
            add(25, 8, "fe2_8", 4000 + (r % 3) * 1500, 400000000, FE2_8_SEED_N4 if r < 5 else "", 15000)

        # 5. Monotonicity lifts with fixed bbsearch_ultimate.exe
        s_15_6 = best_tm(by_cell, 15, 6, "fwpw3_5")
        for r in range(2):
            add(15, 7, "fwpw3_5", 25000, 150000000, s_15_6, 30000)
        s_9_8 = best_tm(by_cell, 9, 8, "fwpw1_8")
        for r in range(2):
            add(9, 9, "fwpw1_8", 25000, 150000000, s_9_8, 30000)
        s_22_3 = best_tm(by_cell, 22, 3, "fwp21_3")
        for n in [23, 24, 25]:
            for r in range(2):
                add(n, 3, "fwp21_3", 20000, 150000000, s_22_3 if r == 0 else best_tm(by_cell, n, 3, "fwp21_3"), 25000)
        add(25, 3, "fwp22_3", 20000, 150000000, "", 25000)

        # 6. Extra 1-step wiki pushes
        for (n, m, cn) in [(8, 7, "fwp22_7"), (9, 4, "fwp2_4"), (11, 3, "fwm21_3"), (11, 5, "fwp22_5_sw"), (13, 7, "fwpw2_6"), (15, 4, "fwp25_4"), (20, 4, "fwp27_4")]:
            stm = best_tm(by_cell, n, m, cn)
            if not stm:
                ms = find_matching_seeds(cores[cn], n, m, seeds)
                stm = ms[0]["tm"] if ms else ""
            add(n, m, cn, 20000, 150000000, stm, 25000)

        dispatch(jobs, "Wave 4A (n<=25 Final Breakthrough & Monotonicity Lifts)", workers=args.workers)

    # Stage 4B: Row-by-row n = 26..35 Extended Tier
    print("\n=== Starting Wave 4B: Row-by-row n=26..35 Extended Tier ===")
    for n in range(26, 36):
        by_cell = load_hits(max_n=36)
        row_jobs = []
        sq = 120000 + n * 100

        def best_prev_col(col, cn):
            # Look from n-1 down to 20 for best verified hit of core cn in col (or FE2_8_SEED_N4 fallback for col 8)
            for sn in range(n - 1, 18, -1):
                t = best_tm(by_cell, sn, col, cn)
                if t:
                    return t
            if cn == "fe2_8":
                return FE2_8_SEED_N4
            return ""

        specs = [
            (5, "fe01_5", min(64000, 55000 + (n - 25) * 900), 160000000),
            (6, "fe1_6", 12000 + (n - 25) * 1500, 140000000),
            (7, "fe11_7", 8000 + (n - 25) * 1500, 140000000),
            (8, "fe2_8", 5000 + (n - 25) * 1000, 180000000),
            (9, "fe2_9", 8000 + (n - 25) * 1500, 180000000),
        ]
        if n <= 32:
            specs.append((3, "fwp21_3", 20000, 100000000))

        for col, cn, cap, bud in specs:
            stm = best_prev_col(col, cn)
            cur_own = best_tm(by_cell, n, col, cn)
            for r in range(3):
                use_stm = stm if r < 2 else (cur_own if cur_own else "")
                row_jobs.append({
                    "mode": "hydra" if is_hydra_core(cn) else "bbsearch",
                    "core": cn, "n": n, "m": col,
                    "cap": min(cap + r * 500, 64500), "budget": bud,
                    "sim_cap": min(cap + 12000, 75000),
                    "seed": sq, "seed_tm": use_stm, "timeout": 240,
                })
                sq += 1
        dispatch(row_jobs, f"Wave 4B Row n={n} (Extended Tier)", workers=args.workers)


if __name__ == "__main__":
    main()
