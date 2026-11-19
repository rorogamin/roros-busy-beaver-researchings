import sys

def parse_tm(s):
    rows = s.split('_')
    ns, ms = len(rows), len(rows[0]) // 3
    tab = {}
    for st, row in enumerate(rows):
        assert len(row) == 3 * ms, f"Bad row len {len(row)} vs {3*ms}"
        for sym in range(ms):
            c = row[3*sym:3*sym+3]
            if c == '---':
                tab[(st, sym)] = None
            else:
                w = int(c[0])
                d = -1 if c[1] == 'L' else 1
                nx = None if c[2] == 'Z' else ord(c[2]) - ord('A')
                tab[(st, sym)] = (w, d, nx)
    return ns, ms, tab

def run(tab, tape_dict, pos, st, max_steps=100000):
    tape = dict(tape_dict)
    for t in range(max_steps):
        if st is None:
            return t, tape, pos, st
        sym = tape.get(pos, 0)
        act = tab[(st, sym)]
        if act is None:
            return t, tape, pos, None
        w, d, nx = act
        if w == 0:
            tape.pop(pos, None)
        else:
            tape[pos] = w
        pos += d
        st = nx
    return max_steps, tape, pos, st

def fmt_cfg(tape, pos, st):
    s = 'Z' if st is None else chr(65 + st)
    if not tape:
        return f'{s}>'
    lo = min(min(tape.keys()), pos)
    hi = max(max(tape.keys()), pos)
    L = ''.join(str(tape.get(i, 0)) for i in range(lo, pos))
    R = ''.join(str(tape.get(i, 0)) for i in range(pos, hi + 1))
    return f'{L} {s}> {R}'

def mk_cfg(L_str, R_str, st=0):
    tape = {}
    for i, ch in enumerate(L_str):
        if ch != '0':
            tape[i - len(L_str)] = int(ch)
    for i, ch in enumerate(R_str):
        if ch != '0':
            tape[i] = int(ch)
    return tape, 0, st

if __name__ == '__main__':
    tms = {
        'BB6_7': ('6RD3LB6LF2RA4LB1RZ6LA_6LC3RB1LD2RA3LF4RE6LB_3RB1LB3LC2RC4LC0LE5LA_3RB2RD3LC2RC1LA3RE1LE_5RC3RE2RA4LC2LE2LE5RB_5RB3RD1LF1LF6LE5RF5LB', 46),
        'BB6_8': ('5RE3LB7LF2RA4LB6LF1RZ5RF_5LE3RB1LD2RA3LF7RC3LB3RA_3RB1LB3LC2RC4LC0LE6LE5LF_3RB6RD3LC2RC5LA3RE2LE1LB_5RC3RE2RA4LC6RA5LA2LE3RE_5RB7RD1LF1LF5RA5RF5LE0RD', 210),
        'BB6_9': ('8LE3LB7LF2RA4LB6LF1RZ1LC8LF_6LE3RB1LD2RA3LF2RA3LB3RA8RD_3RB1LB3LC2RC4LC0LE5LC3RB6RE_3RB6RD3LC2RC5LC3RE2LE1LB5LC_5RC3RE2RA4LC8LE8RE2LE3RE1RB_5RB7RD1LF1LF8LE5RF8RE1RZ8RB', 304),
    }

    for name, (tm_s, boot_t) in tms.items():
        ns, ms, tab = parse_tm(tm_s)
        t, tape, pos, st = run(tab, {}, 0, 0, boot_t)
        print(f'=== {name} ({ns}x{ms}) boot@{boot_t}: {fmt_cfg(tape, pos, st)} ===')
        halt_sym = '5' if name == 'BB6_7' else '6'
        # Test Fwm2 level 0: 5 3^(2m+1) 2 A> 1 R -> 5 3^(2M'+1) 2 A> R (exact!)
        for m in [0, 1, 2]:
            L = '5' + '3'*(2*m+1) + '2'
            R = '1' + halt_sym
            tp, p, s = mk_cfg(L, R, 0)
            tt, tp2, p2, s2 = run(tab, tp, p, s, 50000)
            print(f'  Fwm2 k=0 m={m}: {L} A> {R} --[{tt}]--> {fmt_cfg(tp2, p2, s2)}')
        # Test Fwm2 level k>=1 bounce (1 step + sweep + bounce):
        for k in [1, 2]:
            for m in [0, 1]:
                L = '5' + '3'*(2*m+1) + '2'*(k+1)
                R = '1' + halt_sym
                tp, p, s = mk_cfg(L, R, 0)
                # stop when we hit A> with 2^k on left!
                for step_i in range(1, 500):
                    _, tp, p, s = run(tab, tp, p, s, 1)
                    if s == 0 and tp.get(p, 0) == 1 and tp.get(p-1, 0) == 2 and tp.get(p-k-1, 0) == 3:
                        print(f'  Fwm2_K2 k={k} m={m}: {L} A> 1 --[{step_i}]--> {fmt_cfg(tp, p, s)}')
                        break
        # Test reload transitions
        for sym in (['2'] if name=='BB6_7' else ['2','5'] if name=='BB6_8' else ['2','5','8']):
            for k in [1, 2, 3]:
                for m in [0, 1, 2]:
                    L = '5' + '3'*(2*m+1) + '2'*k
                    R = sym + halt_sym
                    tp, p, s = mk_cfg(L, R, 0)
                    for step_i in range(1, 500):
                        _, tp, p, s = run(tab, tp, p, s, 1)
                        if s == 0 and tp.get(p-1, 0) == 2 and tp.get(p, 0) != int(sym) and tp.get(p, 0) != 3:
                            print(f'  Reload sym={sym} k={k} m={m}: {L} A> {sym} --[{step_i}]--> {fmt_cfg(tp, p, s)}')
                            break
