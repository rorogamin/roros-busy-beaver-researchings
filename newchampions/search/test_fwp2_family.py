from search.sim import parse_tm, run, fmt_cfg, mk_cfg

def test_core(name, core_str, tests, halt_seq):
    ns, ms, tab = parse_tm(core_str)
    print(f"=== {name} ({ns}x{ms}) ===")
    ok = True
    for sym, r, m in tests:
        L = '5'*r + '3'*(2*m+1) + '2'
        R = sym + halt_seq
        tp, p, s = mk_cfg(L, R, 0)
        hit = None
        for i in range(1, 200):
            sym_cur = tp.get(p, 0)
            if tab[(s, sym_cur)] is None:
                hit = f"TOUCHED FREE ({chr(65+s)},{sym_cur}) at t={i}"
                ok = False
                break
            _, tp, p, s = run(tab, tp, p, s, 1)
            if s == 0 and tp.get(p-1, 0) == 2 and tp.get(p, 0) != int(sym) and tp.get(p, 0) != 3:
                hit = f"t={i}: {fmt_cfg(tp, p, s)}"
                break
        if hit is None:
            hit = f"TIMEOUT: {fmt_cfg(tp, p, s)}"
            ok = False
        print(f"  sym={sym} r={r} m={m} -> {hit}")
    tp, p, s = mk_cfg('553332', halt_seq, 0)
    t, tp2, p2, s2 = run(tab, tp, p, s, 20)
    if s2 is not None:
        print(f"  HALT FAILED: {fmt_cfg(tp2, p2, s2)}")
        ok = False
    else:
        print(f"  HALT OK in {t} steps")
    return ok

fwp21_7 = '---3LB6LA2RA4LB5RC5LA_1RZ3RB1LD2RA3LF5RB6LD_3RB1LB3LC2RC4LC1LE5RB_3RB3RE3LC2RC---3RD1LA_5RB3RE---4LC3LG5LE---_5RB5RB---1LF---5LF---_5LF------1LG---5LG---'

fwp22_8 = (
    '---3LB6LA2RA4LB5RC5LA2LG_'
    '1RZ3RB1LD2RA3LF5RB6LD---_'
    '3RB1LB3LC2RC4LC1LE5RB3RF_'
    '3RB3RE3LC2RC---3RD1LA---_'
    '5RB3RE---4LC3LG5LE------_'
    '5RB5RB2RA1LF---5LF------_'
    '5LF---7LA1LG---5LG------'
)

fwp23_9 = (
    '---3LB6LA2RA4LB5RC5LA2LG7LE_'
    '1RZ3RB1LD2RA3LF5RB6LD------_'
    '3RB1LB3LC2RC4LC1LE5RB3RF3RD_'
    '3RB3RE3LC2RC---3RD1LA2RA---_'
    '5RB3RE8LA4LC3LG5LE---------_'
    '5RB5RB2RA1LF---5LF---------_'
    '5LF---7LA1LG---5LG---------'
)

fwp22_7 = (
    '---3LB2LH2RA4LB6LH1RZ_'
    '---3RB1LD2RA3LF5RB---_'
    '3RB1LB3LC2RC4LC1LE---_'
    '3RB3RE3LC2RC---3RD---_'
    '5RB3RE4RG4LC3LG5LE---_'
    '5RB5RB---1LF5LF5LF---_'
    '5LF4RG1LB1LG---5LG2LH_'
    '------1LH1LH2LH5RG---'
)

fwp23_8 = (
    '---3LB2LH2RA4LB1RZ6LH7LH_'
    '---3RB1LD2RA3LF5RB------_'
    '3RB1LB3LC2RC4LC1LE------_'
    '3RB3RE3LC2RC6LD3RD2RA---_'
    '5RB3RE4RG4LC3LG5LE------_'
    '5RB5RB---1LF5LF5LF------_'
    '5LF4RG1LB1LG---5LG2LH6LD_'
    '------1LH1LH2LH5RG------'
)

fwp24_9 = (
    '---3LB2LH2RA4LB1RZ6LH7LH8LH_'
    '---3RB1LD2RA3LF5RB---3RC---_'
    '3RB1LB3LC2RC4LC1LE---2RA---_'
    '3RB3RE3LC2RC6LD3RD2RA------_'
    '5RB3RE4RG4LC3LG5LE---------_'
    '5RB5RB---1LF5LF5LF---------_'
    '5LF4RG1LB1LG7LG5LG2LH6LD7LG_'
    '------1LH1LH2LH5RG---------'
)

assert test_core('BB(7,7) fwp21_7', fwp21_7, [('2',1,1),('2',2,2)], '50')
assert test_core('BB(7,8) fwp22_8', fwp22_8, [('2',1,1),('2',2,2),('7',1,1),('7',2,2)], '50')
assert test_core('BB(7,9) fwp23_9', fwp23_9, [('2',1,1),('7',2,2),('8',1,1),('8',2,2)], '50')
assert test_core('BB(8,7) fwp22_7', fwp22_7, [('2',1,1),('5',1,1),('5',2,2)], '6')
assert test_core('BB(8,8) fwp23_8', fwp23_8, [('2',1,1),('6',2,2),('7',2,1),('7',2,2)], '5')
assert test_core('BB(8,9) fwp24_9', fwp24_9, [('2',1,1),('6',2,2),('7',2,2),('8',1,1),('8',2,2)], '5')
print("ALL 6 CORES 100% PASSED!!")
