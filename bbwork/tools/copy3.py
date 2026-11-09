"""Copy primitive on three symbols (0 blank, 1 mark, 2 marker).

Two symbols cannot carry the marker: erasing the carried cell creates a third
blank beside the doubled separator, so the return leg cannot tell separator
from marker (see tools/copy.py, which measures that failure).  A third symbol
is the cheap fix -- the handbook says so itself in section 10.5, "67 is a state
bound, not a symbol bound, and symbols are the cheap currency" -- and it makes
the copy eight states instead of nine.

Layout:  [source 1^k] 0 0 [destination]     (source at cells 0..k-1)

    S0  on the source's leftmost uncopied mark:
        1 -> 2,R,S1          mark the cell being carried
        0 -> halt            source exhausted
    S1  walk right over the source:    1 -> 1,R,S1
    S2  first separator:               0 -> 0,R,S2   (falls through to S3)
    S3  walk right over the destination:
        1 -> 1,R,S3 ; 0 -> 1,L,S4        append the copy at its right end
    S4  walk back over the destination: 1 -> 1,L,S4
    S5  second separator:              0 -> 0,L,S5
    S6  walk left over the source to the marker:
        1 -> 1,L,S6 ; 2 -> 1,R,S7        restore the marker
    S7  on the next source cell:
        1 -> 2,R,S1                     mark it and copy it too
        0 -> halt                       done

S1 crosses the source, S2 crosses the first separator, S3 crosses the second
and then walks the destination, S4 walks back, S5 re-crosses the first
separator, S6 walks back over the source to the marker and restores it.
"""
import tm

BL, ON, MK = 0, 1, 2
HALT = None

# state numbers
S0, S1, S2, S3, S4, S5, S6, S7 = range(8)


def copy_table():
    t = {}
    # S0: mark the cell under the head; a blank means the source is finished
    t[(S0, ON)] = (MK, 'R', S1)
    t[(S0, BL)] = (BL, 'R', HALT)
    t[(S0, MK)] = (MK, 'R', S1)
    # S1: cross the rest of the source
    t[(S1, ON)] = (ON, 'R', S1)
    t[(S1, MK)] = (MK, 'R', S1)
    t[(S1, BL)] = (BL, 'R', S2)
    # S2: first separator -> second separator
    t[(S2, BL)] = (BL, 'R', S3)
    # S3: cross the destination, then append the copy
    t[(S3, ON)] = (ON, 'R', S3)
    t[(S3, BL)] = (ON, 'L', S4)
    # S4: walk back across the destination
    t[(S4, ON)] = (ON, 'L', S4)
    t[(S4, BL)] = (BL, 'L', S5)
    # S5: second separator -> first separator
    t[(S5, BL)] = (BL, 'L', S6)
    # S6: back over the source to the marker
    t[(S6, ON)] = (ON, 'L', S6)
    t[(S6, MK)] = (ON, 'R', S7)
    # S7: is there another source cell to copy?  If so, mark it here and
    # continue in S1 (S0 is only for the very first cell).
    t[(S7, ON)] = (MK, 'R', S1)
    t[(S7, BL)] = (BL, 'R', HALT)
    return t


def run(k, gap=2, table=None, max_steps=10000):
    table = table or copy_table()
    m = tm.TM(8, table)
    tape = {i: ON for i in range(k)}
    steps, tp, head, state, halted = m.run(head=0, state=S0, tape=tape,
                                           max_steps=max_steps)
    kept = all(tp.get(i, 0) == ON for i in range(k))
    dest = sorted(i for i in range(k + gap, k + gap + 3 * k + 6)
                  if tp.get(i, 0) == ON)
    return dict(steps=steps, halted=halted, state=state, head=head,
                src_intact=kept, dest=dest, score=m.score(tp), tape=tp)


if __name__ == '__main__':
    ok = 0
    for k in range(1, 7):
        r = run(k)
        good = r['halted'] and r['src_intact'] and len(r['dest']) == k
        ok += good
        print(f'k={k}: steps={r["steps"]:3d} halted={r["halted"]} '
              f'src_intact={r["src_intact"]} dest={r["dest"]} '
              f'score={r["score"]} {"OK" if good else "WRONG"}')
    print('copies correct:', ok, 'of 6')
