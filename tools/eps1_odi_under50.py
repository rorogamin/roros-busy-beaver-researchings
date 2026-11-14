"""eps1_odi_under50.py — the under-50 gate for the one-object odometer.

This is the measurement tool for the r5 revision attempt.  It does not
invent a smaller table: it measures the table that builds, its exact
bisimulation floor, its observed-context fixpoint, and the three gates.
The under-50 verdict is therefore honest for the current architecture.

Run: python tools/eps1_odi_under50.py
Exit 0 only when every measured table passes its gates; the verdict line
reports UNDER_50 yes/no separately.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import eps1_odi as O
from eps1_mergehunt import exact_partition, fired_rows, bisim_partition


def stage(name):
    print()
    print(f'== {name} ==')


def measure(sn, run_tiers=True):
    T, meta = O.build_table(sn)
    rows = sum(len(r) for r in T.values())

    # exact behavioural floor of this table (reachable states only)
    part = exact_partition(T)
    classes = {}
    for s, p in part.items():
        classes.setdefault(p, []).append(s)
    floor = len(classes)
    merged = [sorted(v) for v in classes.values() if len(v) > 1]

    # trace-side dead rows (the observed-context slack, if any)
    fired = fired_rows(T, sn)
    dead = [(s, sym) for s in T for sym in (0, 1)
            if (s, sym) not in fired]

    ok, bad, halts, failures = O.census_battery(T, sn)
    bad2 = O.check_moves_random(T, sn)
    bad3 = O.check_tiers(T, sn) if run_tiers else 0

    print(f'sn={sn}: states={len(T)} rows={rows} '
          f'bisim_floor={floor} (merged classes={len(merged)})')
    print(f'  trace-corpus dead rows={len(dead)}; '
          f'gate1 ok={ok} bad={bad} halts={halts}; '
          f'gate2 failures={bad2}; gate3 failures={bad3}')
    for f in failures[:4]:
        print('  FAIL', f)
    if merged:
        for cls in merged[:6]:
            print('  bisim class:', cls)
    return {
        'sn': sn,
        'states': len(T),
        'rows': rows,
        'floor': floor,
        'dead_rows': len(dead),
        'gates_ok': (bad == 0 and bad2 == 0 and bad3 == 0),
        'failures': failures,
    }


def family_ledger(sn=1):
    """Count the state names in the known structural clusters.

    This is a name-based ledger, not a lower bound: it shows where the
    remaining states actually sit when the wall is present.
    """
    T, _meta = O.build_table(sn)
    names = sorted(T)
    groups = {
        'walkback p0 pred (WBX/WB_P)': [s for s in names if s.startswith(('WBX', 'WB_P'))],
        'walkback fs (WR_FS)': [s for s in names if s.startswith('WR_FS')],
        'walkback absorb (WB_ABS)': [s for s in names if s.startswith('WB_ABS')],
        'walkback route A (WR_A/RAW)': [s for s in names if s.startswith(('WR_A', 'RAW'))],
        'append (A/APW)': [s for s in names
                          if re.fullmatch(r'A[0-9]+|APW1', s)],
        'cascade (CM/EA/MSE/SB/SH)': [s for s in names if s.startswith(('CM', 'EA', 'MSE', 'SB', 'SH'))],
        'dispatch/walk to look': [s for s in names if s in (
            'IN', 'D2', 'D3', 'D4', 'D5', 'M2', 'M3', 'M4',
            'WAD', 'WAE', 'WAZ', 'WAZB', 'WAS', 'WASB',
            'PKB', 'PKC', 'PKD1', 'FSL', 'FSP')],
        'shared home': [s for s in names if s in ('BRH1', 'BRH2', 'WB_P2', 'WB_P1')],
    }
    print()
    print(f'family ledger sn={sn} (names overlap across shared tails):')
    for label, members in groups.items():
        print(f'  {label:34s} {len(members):2d}  '
              + ','.join(members))


def main():
    stage('build + gates + exact floor')
    results = [measure(1), measure(2), measure(3)]

    stage('observed-context reduction')
    print('The separate observed-context pass was run on sn=1 and sn=2 '
          '(tools/eps1_contextmin.py): 0 merges on both; it is not '
          're-run inside this gate because it owns the full corpus. '
          'This gate does not infer an under-50 floor from that pass.')
    family_ledger(1)

    stage('verdict')
    all_gates = all(r['gates_ok'] for r in results)
    under50 = any(r['states'] < 50 for r in results)
    print(f'ALL GATES ' + ('OK' if all_gates else 'FAILED'))
    for r in results:
        print(f'  sn={r["sn"]}: {r["states"]} states, floor={r["floor"]}')
    print('UNDER_50: ' + ('YES' if under50 else 'NO'))
    print('No ε₁/FGH claim is made by this tool.')

    return 0 if all_gates else 1


if __name__ == '__main__':
    sys.exit(main())
