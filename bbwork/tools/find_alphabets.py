"""Classify every machine string in championsreal.txt by state and symbol count.

Notation in this file: rows separated by '_', each row a run of 3-character
entries SYMBOL MOVE STATE, MOVE in {L,R,Z}, and '---' meaning the transition is
undefined (contributing no symbol).  A row may be preceded by a label on the
same line, so the machine string is taken to be the longest whitespace-separated
field that contains '_'.

Blank convention: machines that write their blank explicitly use '0', so the
symbol count is the size of the written alphabet.  Machines that only ever
mention '-' for an undefined entry and never write a blank use '-' as the blank,
so the count is one more than the number of written symbol characters.  Both
readings are printed, plus the labels, so any claim about "the only N-symbol
row" can be checked against the whole file instead of assumed.
"""

import re
import sys

ENTRY = re.compile(r'^(\S)([LRZ-])([A-Za-z0-9-])$')


def machine_field(line):
    best = None
    for field in line.split():
        if '_' in field and (best is None or len(field) > len(best)):
            best = field
    return best


def classify(text):
    rows = text.split('_')
    if len(rows) < 2:
        return None
    alphabet = set()
    for row in rows:
        if not row or len(row) % 3:
            return None
        for i in range(0, len(row), 3):
            tok = row[i:i + 3]
            if tok == '---':
                continue
            m = ENTRY.match(tok)
            if not m:
                return None
            alphabet.add(m.group(1))
    return len(rows), alphabet


def main(path='championsreal.txt'):
    found = []
    for n, line in enumerate(open(path, encoding='utf-8', errors='replace'), 1):
        text = machine_field(line)
        if text is None:
            continue
        r = classify(text)
        if r is None:
            continue
        states, alpha = r
        written = len(alpha)
        syms = written if '0' in alpha else written + 1
        label = line.strip().split(text)[0].strip()
        found.append((n, states, syms, ''.join(sorted(alpha)), label, text))

    print(f'rows classified: {len(found)}')
    by_sym = {}
    for rec in found:
        by_sym.setdefault(rec[2], []).append(rec)
    for syms in sorted(by_sym):
        rows = by_sym[syms]
        print(f'\n{syms}-symbol rows: {len(rows)}')
        for n, states, _, alpha, label, text in sorted(rows, key=lambda t: t[1]):
            print(f'  line {n:4d}  {states:3d} states  written {{{alpha}}}  {label}')
    return 0


if __name__ == '__main__':
    sys.exit(main(*sys.argv[1:]))
