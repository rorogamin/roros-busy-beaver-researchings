"""Check that the Rocq table in Fe0Boot.v is exactly the .txt machine.

The Rocq file's [deltaF] must agree, cell by cell, with
machines/found_fe0_5_17s.txt.  This is the link that keeps the proof from
drifting away from the simulated machine: it parses both, compares all 17*5
cells, and exits non-zero on any difference.

usage:  python tools/check_boot_table.py [machine.txt] [Fe0Boot.v]
"""

import re
import sys

MACHINE = 'machines/found_fe0_5_17s.txt'
ROCQ = 'rocq/Fe0Boot.v'
STATES = 'ABCDEFGHIJKLMNOPQ'
NSTATES = len(STATES)
NSYMS = 5


def load_txt(path):
    """(state, symbol) -> (write, 'L'/'R', next index or None for halt)."""
    tab = {}
    for line in open(path):
        s = line.strip()
        if not s or s.startswith('#'):
            continue
        f = s.split()
        if len(f) != 5 or not f[0].isdigit():
            continue
        st, sy, w, d, nxt = f
        tab[(int(st), int(sy))] = (int(w), d, None if nxt == 'H' else int(nxt))
    return tab


def load_rocq(path):
    """Parse the `match s with ... end` block of [deltaF]."""
    src = open(path).read()
    m = re.search(r'Definition deltaF\b.*?match s with(.*?)\n\s*end\) None\.',
                  src, re.S)
    if not m:
        raise SystemExit(f'could not find the deltaF table in {path}')
    body = m.group(1)
    rows = {}
    # a row's cell list may wrap over several source lines, so match across
    # newlines up to the closing bracket (cells contain no bracket)
    for mm in re.finditer(r'\|\s*([A-Q])\s*=>\s*\[(.*?)\]', body, re.S):
        state = STATES.index(mm.group(1))
        cells = [' '.join(c.split()) for c in mm.group(2).split(';')]
        if len(cells) != NSYMS:
            raise SystemExit(f'state {mm.group(1)}: {len(cells)} cells, expected {NSYMS}')
        parsed = []
        for c in cells:
            if c == 'None':
                parsed.append(None)
                continue
            mc = re.match(r'Some \(S(\d), (true|false), (HALT|[A-Q])\)$', c)
            if not mc:
                raise SystemExit(f'cannot parse cell {c!r} in state {mm.group(1)}')
            parsed.append((int(mc.group(1)), 'R' if mc.group(2) == 'true' else 'L',
                           None if mc.group(3) == 'HALT' else STATES.index(mc.group(3))))
        rows[state] = parsed
    return rows


def main():
    machine = sys.argv[1] if len(sys.argv) > 1 else MACHINE
    rocq = sys.argv[2] if len(sys.argv) > 2 else ROCQ
    txt = load_txt(machine)
    tab = load_rocq(rocq)

    bad = []
    for st in range(NSTATES):
        if st not in tab:
            bad.append(f'state {STATES[st]}: missing from {rocq}')
            continue
        for sy in range(NSYMS):
            a = txt.get((st, sy))
            b = tab[st][sy]
            if a != b:
                bad.append(f'{STATES[st]}/{sy}: txt={a} rocq={b}')
    extra = sorted(k for k in txt if k[0] >= NSTATES or k[1] >= NSYMS)
    for k in extra:
        bad.append(f'{k}: in the .txt but outside the 17x5 table')

    checked = NSTATES * NSYMS
    if bad:
        print(f'TABLE MISMATCH ({len(bad)} of {checked} cells):')
        for b in bad:
            print('  ', b)
        return 1
    halts = [f'{STATES[s]}/{y}' for s in range(NSTATES) for y in range(NSYMS)
             if txt.get((s, y)) and txt[(s, y)][2] is None]
    print(f'{rocq} matches {machine}: {checked}/{checked} cells identical')
    print(f'halt cells: {", ".join(halts) or "none"}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
