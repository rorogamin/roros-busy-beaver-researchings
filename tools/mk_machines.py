"""Build machine tables and emit them as (a) 5-tuple text files and (b) Rocq tables.

Core states (relative numbering, as in rocq/Core.v):
  A=0 T=1 F0=2 F1=3 F2=4 G1=5 R1=6 R2=7 R3=8 R4=9 R5=10 A2=11 T2=12 N0=13 N1=14

The core is placed at absolute states [CORE_BASE, CORE_BASE+14] so that state 0
can be the machine's boot entry state.
"""

CORE_BASE = 0

CORE_REL = {
    'A': 0, 'T': 1, 'F0': 2, 'F1': 3, 'F2': 4, 'G1': 5,
    'R1': 6, 'R2': 7, 'R3': 8, 'R4': 9, 'R5': 10,
    'A2': 11, 'T2': 12, 'N0': 13, 'N1': 14,
}

# core transitions in relative numbering: (state, read) -> (write, dir, next)
CORE_REL_TBL = {
    (0, 1): (0, 'R', 1),
    (1, 1): (1, 'R', 3),
    (1, 0): (0, 'R', 2),
    (2, 0): (0, 'R', 2),
    (2, 1): (1, 'R', 4),
    (3, 1): (1, 'R', 3),
    (3, 0): (0, 'R', 4),
    (4, 1): (1, 'R', 4),
    (4, 0): (1, 'R', 5),
    (5, 0): (1, 'L', 6),
    (6, 1): (1, 'L', 6),
    (6, 0): (0, 'L', 7),
    (7, 1): (1, 'L', 8),
    (7, 0): (0, 'L', 9),
    (8, 1): (1, 'L', 8),
    (8, 0): (0, 'R', 0),
    (9, 0): (0, 'L', 9),
    (9, 1): (1, 'L', 10),
    (10, 1): (1, 'L', 10),
    (10, 0): (0, 'R', 11),
    (11, 1): (0, 'R', 12),
    (12, 1): (1, 'R', 13),
    # (12, 0) undefined: halt
    (13, 1): (1, 'R', 13),
    (13, 0): (0, 'R', 14),
    (14, 0): (0, 'R', 14),
    (14, 1): (0, 'R', 1),
}


def core_table():
    """Core transitions with absolute state numbers."""
    return {((s + CORE_BASE), r): (w, d, None if n is None else n + CORE_BASE)
            for (s, r), (w, d, n) in CORE_REL_TBL.items()}


def abs_state(name):
    return CORE_REL[name] + CORE_BASE


def boot_table(c, u, w):
    """Boot: state 0 on a blank jumps to state 15; states 15.. write
    1^c 0 1^u 0 1^w starting at cell 1; then a 6-state walk back to C's
    leftmost cell, entering the core's N0.  State 0 on `on` is the core's A,
    so the boot jump (state 0 on `bl`) never collides with it.
    """
    pat = 'O' * c + 'Z' + 'O' * u + 'Z' + 'O' * w
    n = len(pat)
    tbl = {(0, 0): (0, 'R', 15)}
    write_states = [15 + i for i in range(n)]
    for i, ch in enumerate(pat):
        st = write_states[i]
        nxt = write_states[i + 1] if i + 1 < n else 15 + n
        tbl[(st, 0)] = (1 if ch == 'O' else 0, 'R', nxt)
    b = 15 + n
    p1, p2, p3, p4, p5 = b + 1, b + 2, b + 3, b + 4, b + 5
    tbl[(b, 0)] = (0, 'L', p1)
    tbl[(p1, 1)] = (1, 'L', p1)
    tbl[(p1, 0)] = (0, 'L', p2)
    tbl[(p2, 0)] = (0, 'L', p2)
    tbl[(p2, 1)] = (1, 'L', p3)
    tbl[(p3, 1)] = (1, 'L', p3)
    tbl[(p3, 0)] = (0, 'L', p4)
    tbl[(p4, 0)] = (0, 'L', p4)
    tbl[(p4, 1)] = (1, 'L', p5)
    tbl[(p5, 1)] = (1, 'L', p5)
    tbl[(p5, 0)] = (0, 'R', 13)          # N0, at C's leftmost cell
    return tbl, b + 6


def machine1(c=8, u=2, w=1):
    bt, nxt = boot_table(c, u, w)
    t = dict(bt)
    t.update(core_table())
    return t, max(nxt, 15)


def to_text(tbl, nstates, order=None):
    """Render a table as 5-tuple lines, sorted by (state, symbol)."""
    lines = []
    for (s, r), (w, d, n) in sorted(tbl.items()):
        ns = 'H' if n is None else str(n)
        lines.append(f'{s} {r} {w} {d} {ns}')
    return '\n'.join(lines) + '\n'


def to_rocq(name, tbl):
    """Render a table as a Rocq match on (state, symbol)."""
    out = [f'Definition {name} : table := fun s b =>',
           '  match s, b with']
    for (s, r), (w, d, n) in sorted(tbl.items()):
        ws = 'on' if w else 'bl'
        ds = 'true' if d == 'R' else 'false'
        ns = 'None' if n is None else f'Some ({ws}, {ds}, {n})'
        out.append(f'  | {s}, {"on" if r else "bl"} => {ns}')
    out.append('  | _, _ => None')
    out.append('  end.')
    return '\n'.join(out) + '\n'
