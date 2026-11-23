"""Classify each landmark machine against the bbchallenge Champions table.

A machine is a *confirmed* champion only when the wiki states a bound for its
cell and the machine's bound is in a strictly higher family (epsilon1 > epsilon0
> omega^omega+k > omega^2+k > omega*2+k > omega+k > fixed numbers), because a
higher family dominates any fixed argument or finite iteration of a lower one.
Cells the wiki hides behind "..." are reported as unknown, never as champion.
"""
import json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_champions as G

ROOT = r'C:\Users\Rowan\Documents\findthatmachine'
OUT = os.path.join(ROOT, 'work', 'out_landmarks')

# (n,m) -> wiki bound text, transcribed from the live raw wikitext (2026-11-23).
WIKI = {
    (2, 3): '38', (3, 3): '10^17', (4, 3): '10^^4 4', (5, 3): 'f_omega(2^^7 7)',
    (6, 3): 'f_omega^2(10^^^6)', (7, 3): None,
    (8, 3): 'f_{omega+1}^4(f_omega^3(14))',
    (9, 3): 'f_{omega+2}^3(f_{omega+1}^2(f_omega(14)))',
    (10, 3): 'f_{omega*2}(11)', (11, 3): 'f_{omega*2}(46)',
    (12, 3): 'f_{omega*2}(f_{omega+2}^2(4))',
    (13, 3): 'f_{omega*2}^3(f_{omega+1}(f_omega^2(5)))',
    (2, 4): '3932964', (3, 4): '2^^15 5', (4, 4): 'f_omega(2^^5 3)',
    (5, 4): 'f_{omega+1}(65536)', (6, 4): 'f_{omega+1}^4(65536)',
    (7, 4): 'f_{omega+3}(21)', (8, 4): 'f_{omega+8}^2(4)',
    (9, 4): 'f_{omega^2}(18)', (10, 4): 'f_{omega^2}^3(3)',
    (11, 4): 'f_{omega^2+1}(f_{omega^2}(f_{omega+3}^2(4)))',
    (12, 4): 'f_{omega^2+2}(15)', (13, 4): 'f_{omega^2+3}(15)',
    (2, 5): '10^10^10^3314360',
    (3, 5): 'f_omega(2^^15 5) > f_omega^2(15)',
    (4, 5): 'f_{omega+1}(27041)', (5, 5): 'f_{omega+1}(f_omega^4(6))',
    (6, 5): 'f_{omega+3}(11)', (7, 5): 'f_{omega+3}^2(10)',
    (8, 5): 'f_{omega^2}(13)', (9, 5): 'f_{omega^2+1}(6)',
    (10, 5): 'f_{omega^2+2}(4)', (12, 5): 'f_{omega^omega}^6(14)',
    (14, 5): 'f_{omega^omega+1}(51)', (17, 5): 'f_epsilon0(20)',
    (2, 6): '10^^10^^10^10^115', (3, 6): 'f_omega^3(15)',
    (4, 6): 'f_{omega+2}(29)', (5, 6): 'f_{omega+3}(31)',
    (6, 6): 'f_{omega*2}(89)', (7, 6): 'f_{omega^2}(110)',
    (8, 6): 'f_{omega^2+1}(f_omega(31))', (12, 6): 'f_{omega^omega+1}(330)',
    (2, 7): '10^^10^^10^^155', (3, 7): 'f_{omega+1}(117)',
    (4, 7): 'f_{omega+3}(34)', (18, 7): 'f_epsilon0(1.7e352)',
    (2, 8): '10^^10^^10^^10^^155', (17, 8): 'f_epsilon0(1.7e352)',
    (2, 9): '10^^10^^10^^10^^10^^155',
}


def _offset_after(t, i):
    """Read a '+k' offset starting at t[i], or 0."""
    if i < len(t) and t[i] == '+':
        j = i + 1
        k = j
        while k < len(t) and t[k].isdigit():
            k += 1
        if k > j:
            return int(t[j:k])
    return 0


def wiki_rank(text):
    """(family, offset) of the *strongest* term mentioned."""
    if text is None:
        return None
    t = text.replace(' ', '')
    best = (0, 0)
    if 'epsilon1' in t:
        best = max(best, (6, 0))
    if 'epsilon0' in t:
        best = max(best, (5, 0))
    for key, fam in (('omega^omega', 4), ('omega^2', 3), ('omega*2', 2)):
        i = t.find(key)
        while i >= 0:
            best = max(best, (fam, _offset_after(t, i + len(key))))
            i = t.find(key, i + 1)
    i = t.find('omega')
    while i >= 0:
        nxt = t[i + 5:i + 6]
        if nxt in ('+', '('):
            best = max(best, (1, _offset_after(t, i + 5)))
        i = t.find('omega', i + 1)
    return best


def main():
    data = json.load(open(os.path.join(OUT, 'landmarks_2026_11_23.json'), encoding='utf-8'))
    confirmed, unknown, beaten, upgraded = [], [], [], []
    for e in data:
        cell = (e['states'], e['symbols'])
        w = WIKI.get(cell, 'HIDDEN')
        mine = G.family_rank(e['core'])
        if w == 'HIDDEN':
            e['wiki_status'] = 'unknown (row hidden on wiki)'
            unknown.append(e)
            continue
        if w is None:
            e['wiki_status'] = 'WIKI CELL BLANK -> champion'
            confirmed.append(e)
            continue
        wr = wiki_rank(w)
        e['wiki_bound'] = w
        if mine[0] > wr[0] or (mine[0] == wr[0] and mine[1] > wr[1]):
            e['wiki_status'] = f'WINS: {mine} > wiki {wr}'
            confirmed.append(e)
        elif mine[0] == wr[0] and mine[1] == wr[1]:
            e['wiki_status'] = f'same family as wiki {wr}; argument not comparable'
            upgraded.append(e)
        else:
            e['wiki_status'] = f'weaker than wiki {wr}'
            beaten.append(e)
    json.dump(data, open(os.path.join(OUT, 'landmarks_2026_11_23.json'), 'w', encoding='utf-8'),
              indent=1, ensure_ascii=False)
    json.dump(confirmed, open(os.path.join(OUT, 'champions_confirmed_2026_11_23.json'), 'w',
                              encoding='utf-8'), indent=1, ensure_ascii=False)
    print(f'confirmed champions: {len(confirmed)}')
    for e in confirmed:
        print(f"  {e['states']}x{e['symbols']} {e['core']:<12} {e['wiki_status']}")
    print(f'\nsame-family (unresolved): {len(upgraded)}   weaker than wiki: {len(beaten)}   '
          f'unknown/hidden: {len(unknown)}')


if __name__ == '__main__':
    main()
