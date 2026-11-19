"""Verify all 11 new 9..11-state Fwp2_H cores in Python (zero free-cell touches, exact transitions)."""
from search.sim import parse_tm, run, fmt_cfg, mk_cfg

def mk_core(ns, ms, base_rows, edits):
    grid = []
    for s in range(ns):
        row = list(['---'] * ms)
        if s < len(base_rows):
            br = base_rows[s]
            bms = len(br) // 3
            for sym in range(min(ms, bms)):
                row[sym] = br[3*sym:3*sym+3]
        grid.append(row)
    for (s, sym), val in edits.items():
        grid[s][sym] = val
    return '_'.join(''.join(r) for r in grid)

# Base Fwp2_H (8x6)
BASE_H6 = [
    '---3LB2LH2RA4LB---',
    '---3RB1LD2RA3LF5RB',
    '3RB1LB3LC2RC4LC1LE',
    '3RB3RE3LC2RC---3RD',
    '5RB3RE4RG4LC3LG5LE',
    '5RB5RB---1LF5LF5LF',
    '5LF4RG1LB1LG---5LG',
    '------1LH1LH---5RG',
]

# Base 8x7 (+2 on sym 6)
BASE_87_6 = mk_core(8, 7, BASE_H6, {
    (0, 6): '6LH', (6, 6): '2LH', (7, 4): '2LH',
}).split('_')

# Base 8x8 (+2 on 6, +3 on 7)
BASE_88 = mk_core(8, 8, BASE_87_6, {
    (0, 7): '7LH', (6, 7): '6LD', (3, 4): '6LD', (3, 6): '3RB', (1, 6): '3RC', (2, 6): '2RA',
}).split('_')

# Base 8x9 (+2 on 6, +3 on 7, +4 on 8)
BASE_89 = mk_core(8, 9, BASE_88, {
    (0, 8): '8LH', (6, 8): '7LG', (6, 4): '7LG',
    (1, 7): '3RC', (2, 7): '3RE', (4, 7): '3RF', (5, 7): '2RA',
}).split('_')

# Now build all 11 cores!
CORES = {}

# Column m=6
CORES['BB9_6'] = '---3LB2LH2RA4LB2RI_---3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC---3RD_5RB3RE4RG4LC3LG5LE_5RB5RB---1LF5LF5LF_5LF4RG1LB1LG---5LG_------1LH1LH---5RG_1RZ5LI2LI2LI---5RG'
CORES['BB10_6'] = '---3LB2LH2RA4LB2RI_---3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC2RF3RD_5RB3RE4RG4LC3LG5LE_5RB5RB1LA1LF5LF5LF_5LF4RG1LB1LG4LJ5LG_------1LH1LH3RD5RG_1RZ4LH2LI2LI5LI5RG_------------4LJ5RH'
CORES['BB11_6'] = mk_core(11, 6, CORES['BB10_6'].split('_'), {
    # Move 5 4 (+2) sweep from I to K; put 5 2 (+4) on J!
    (8, 2): '1LJ', (8, 3): '---', (8, 4): '5LK', (8, 5): '---',
    (10, 2): '2LK', (10, 3): '2LK', (10, 5): '5RG',
    (9, 2): '1LJ', (9, 3): '1LJ', (7, 1): '2RF', (5, 1): '1RJ', (9, 1): '5LA',
})

# Column m=7 (A5=4RI; 5 0->halt, 5 1->6^(2m-1) 5, 5 4->1 5 1^(2m+1), 5 6->5 4^(2m+1))
CORES['BB9_7'] = mk_core(9, 7, BASE_87_6, {
    (0, 5): '4RI',
    (8, 0): '1RZ', (8, 1): '5LI', (8, 4): '6LI', (8, 2): '6LI', (8, 3): '6LI', (8, 5): '5RB',
    (1, 6): '3RC', (2, 6): '3RD', (3, 6): '3RE', (4, 6): '2RA',
})
CORES['BB10_7'] = mk_core(10, 7, BASE_87_6, {
    (0, 5): '4RI',
    (8, 0): '1RZ', (8, 1): '5LJ',
    (9, 4): '6LJ', (9, 2): '6LJ', (9, 3): '6LJ', (9, 5): '5RB',
    (1, 6): '3RC', (2, 6): '3RD', (3, 6): '3RE', (4, 6): '2RA',
    # 5 4 (+4) on I:
    (8, 4): '1LI', (8, 2): '1LI', (8, 3): '1LI', (8, 5): '5RH',
    (7, 1): '2RF', (5, 1): '1RJ', (9, 1): '5LA',
})
CORES['BB11_7'] = mk_core(11, 7, CORES['BB10_7'].split('_'), {
    # 5 6 (+5) on K:
    (8, 6): '4LK', (10, 4): '4LK', (10, 2): '4LK', (10, 3): '4LK', (10, 5): '5RD',
    (3, 4): '3RG', (6, 4): '2RF', (5, 2): '2RA',
})

# Column m=8 (A5=6RI; 5 0->halt, 5 1->7^(2m-1) 5, 5 6->1 5 1^(2m+1), 5 7->5 6^(2m+1))
CORES['BB9_8'] = mk_core(9, 8, BASE_88, {
    (0, 5): '6RI',
    (8, 0): '1RZ', (8, 1): '5LI', (8, 6): '7LI', (8, 2): '7LI', (8, 3): '7LI', (8, 5): '5RB',
    (1, 7): '3RC', (2, 7): '3RE', (4, 7): '3RF', (5, 7): '2RA',
})
CORES['BB10_8'] = mk_core(10, 8, BASE_88, {
    (0, 5): '6RI',
    (8, 0): '1RZ', (8, 1): '5LJ',
    (9, 6): '7LJ', (9, 2): '7LJ', (9, 3): '7LJ', (9, 5): '5RB',
    (1, 7): '3RC', (2, 7): '3RE', (4, 7): '3RF', (5, 7): '2RA',
    # 5 6 (+5) on I:
    (8, 6): '1LI', (8, 2): '1LI', (8, 3): '1LI', (8, 5): '5RH',
    (7, 1): '2RF', (5, 1): '1RJ', (9, 1): '5LA',
})
CORES['BB11_8'] = mk_core(11, 8, CORES['BB10_8'].split('_'), {
    # 5 7 (+6) on K:
    (8, 7): '6LK', (10, 6): '6LK', (10, 2): '6LK', (10, 3): '6LK', (10, 5): '5RE',
    (4, 6): '3RF', (5, 6): '2RH', (7, 6): '5LF', (5, 2): '2RA',
})

# Column m=9 (A5=6RI; 5 0->halt, 5 1->8^(2m-1) 5, 5 6->1 5 1^(2m+1), 5 7->5 6^(2m+1))
CORES['BB9_9'] = mk_core(9, 9, BASE_89, {
    (0, 5): '6RI',
    (8, 0): '1RZ', (8, 1): '5LI', (8, 6): '8LI', (8, 2): '8LI', (8, 3): '8LI', (8, 5): '5RB',
    (1, 8): '3RC', (2, 8): '3RD', (3, 8): '3RE', (4, 8): '2RA',
})
CORES['BB10_9'] = mk_core(10, 9, BASE_89, {
    (0, 5): '6RI',
    (8, 0): '1RZ', (8, 1): '5LJ',
    (9, 6): '8LJ', (9, 2): '8LJ', (9, 3): '8LJ', (9, 5): '5RB',
    (1, 8): '3RC', (2, 8): '3RD', (3, 8): '3RE', (4, 8): '2RA',
    # 5 6 (+6) on I:
    (8, 6): '1LI', (8, 2): '1LI', (8, 3): '1LI', (8, 5): '5RH',
    (7, 1): '2RF', (5, 1): '1RJ', (9, 1): '5LA',
})
CORES['BB11_9'] = mk_core(11, 9, CORES['BB10_9'].split('_'), {
    # 5 7 (+7) on K:
    (8, 7): '6LK', (10, 6): '6LK', (10, 2): '6LK', (10, 3): '6LK', (10, 5): '5RE',
    (4, 6): '3RF', (5, 6): '2RH', (7, 6): '5LF', (5, 2): '2RA',
})

TESTS = {
    'BB9_6':  [('2',1),('51',1),('51',2)],
    'BB10_6': [('2',1),('54',1),('51',1),('51',2)],
    'BB11_6': [('2',1),('54',1),('51',1),('52',0),('52',1),('52',2)],
    'BB9_7':  [('2',1),('6',1),('51',1),('51',2)],
    'BB10_7': [('2',1),('6',1),('51',1),('54',0),('54',1),('54',2)],
    'BB11_7': [('2',1),('6',1),('51',1),('54',0),('54',1),('56',0),('56',1),('56',2)],
    'BB9_8':  [('2',1),('6',1),('7',1),('51',1),('51',2)],
    'BB10_8': [('2',1),('6',1),('7',1),('51',1),('56',0),('56',1),('56',2)],
    'BB11_8': [('2',1),('6',1),('7',1),('51',1),('56',0),('56',1),('57',0),('57',1),('57',2)],
    'BB9_9':  [('2',1),('6',1),('7',1),('8',1),('51',1),('51',2)],
    'BB10_9': [('2',1),('6',1),('7',1),('8',1),('51',1),('56',0),('56',1),('56',2)],
    'BB11_9': [('2',1),('6',1),('7',1),('8',1),('51',1),('56',0),('56',1),('57',0),('57',1),('57',2)],
}

all_ok = True
for name, core in CORES.items():
    ns, ms, tab = parse_tm(core)
    print(f'=== {name} ({ns}x{ms}) ===')
    for sym, m in TESTS[name]:
        L = '55' + '3'*(2*m+1) + '2'
        R = sym + '0'
        tp, p, s = mk_cfg(L, R, 0)
        hit = None
        for i in range(1, 200):
            cur = tp.get(p, 0)
            if tab[(s, cur)] is None:
                hit = f'FREE ({chr(65+s)},{cur}) at t={i}'
                all_ok = False
                break
            _, tp, p, s = run(tab, tp, p, s, 1)
            if s == 0 and tp.get(p-1, 0) == 2 and i >= 5:
                hit = f't={i}: {fmt_cfg(tp, p, s)}'
                break
        if hit is None:
            hit = f'TIMEOUT: {fmt_cfg(tp, p, s)}'
            all_ok = False
        print(f'  sym={sym:2s} m={m} -> {hit}')
    # Test halt on 50
    tp, p, s = mk_cfg('553332', '50', 0)
    t, tp2, p2, s2 = run(tab, tp, p, s, 20)
    if s2 is not None:
        print(f'  HALT FAILED: {fmt_cfg(tp2, p2, s2)}')
        all_ok = False
    else:
        print(f'  HALT OK in {t} steps')

assert all_ok, "Some core failed!"
print("ALL 11 CORES 100% PASSED!!")
