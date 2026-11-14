#!/usr/bin/env python3
"""Extra finite checks of the paid-reset bridge and matched-tree inequality."""
from itertools import product
import json
from pathlib import Path
import sys
from verify_prefix_safety import adjusted, decode, good, reset_paid, transpose_word, value
sys.path.insert(0, str(Path(__file__).parent/'reference_tools'))
import blocksim as ref


def dyck_words(n, height=0, word=''):
    if n == 0:
        if height == 0: yield word
        return
    if n > height: yield from dyck_words(n-1, height+1, word+'Y')
    if height:
        yield from dyck_words(n-1, height-1, word+'X')
        yield from dyck_words(n-1, height-1, word+'V')


def main():
    reset_count = 0
    for n in range(9):
        for letters in product('YVX', repeat=n):
            word = ''.join(letters)
            if adjusted(word) < 0: continue
            expected = reset_paid(word)
            assert decode(expected) == transpose_word(word)
            lt, st, rt = ['L'], 'L', list(word)+['R']
            for i in range(2000):
                if st == 'B':
                    assert rt == ['Y', 'R1']
                    assert tuple(reversed(lt[:-1])) == expected, (word, expected, lt)
                    break
                d = ref.stride(lt) if st == 'L' else None
                if d is not None: lt, _ = d; st = 'R'
                else: lt, st, rt, _ = ref.bstep('3RA', lt, st, rt)
            else: raise AssertionError(('reset limit', word))
            reset_count += 1
    group_count = 0
    for n in range(1, 7):
        for word in dyck_words(2*n):
            for a in (-100, -3, -1, 0, 1, 2, 7, 100):
                q = transpose_word(word, a)
                for b in (0, 1, 3, 100):
                    assert adjusted(q, b) >= 4*b + 2, (word, a, b, q)
                    group_count += 1
    result = {'status':'all finite component checks passed',
              'clean_reset_words_through_length_8':reset_count,
              'matched_group_tests_through_6_pairs':group_count,
              'not_a_Lean_certificate':True}
    Path(__file__).with_name('component_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
