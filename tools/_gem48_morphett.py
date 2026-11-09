"""Generate morphett.info format for the gemini 48-state 2-symbol eps1 machine.

Source of truth: rocq/gemini_epsilon1_tm_48s_v2_fix.v (the audited, compiling
copy; machine table identical to the shipped epsilon1_tm.v).

Morphett syntax (morphett.info/turing):
  '<current state> <current symbol> <new symbol> <direction> <new state>'
  halting states start with 'halt'.

Mapping used:
  file state S01..S48  -> morphett states '0'..'47'  (S01 = start state -> 0)
  file Halt            -> morphett 'halt'
  symbol B0            -> '_'  (the blank / zero bit: blank tape = all '_')
  symbol B1            -> '1'

Semantics note (checked against the .v): a transition INTO Halt still writes
and moves its symbol/direction, then halts -- morphett does the same, so the
halt lines carry the write symbol and direction.
"""
import re
import sys

V_PATH = 'rocq/gemini_epsilon1_tm_48s_v2_fix.v'
OUT    = 'gem48_morphett.txt'

src = open(V_PATH, encoding='utf-8').read()
m = re.search(r'Definition trans.*?\bend\.', src, re.S)
tab = m.group(0)

# states in first-appearance order: S01..S48
states = []
for q in re.finditer(r'\| (S\d{2}), (B[01]) => \(B([01]), ([LR]), (?:(St (S\d{2}))|Halt)\)', tab):
    pass

rows = re.findall(
    r'\| (S\d{2}), (B[01]) => \(B([01]), ([LR]), (?:St (S\d{2})|Halt)\)', tab)
if len(rows) != 96:
    print(f'ERROR: expected 96 transition rows, found {len(rows)}'); sys.exit(1)

qs = sorted({r[0] for r in rows})
if len(qs) != 48:
    print(f'ERROR: expected 48 states, found {len(qs)}'); sys.exit(1)

def qname(q):
    return str(int(q[1:]) - 1)      # S01 -> '0', S02 -> '1', ... S48 -> '47'

def bit(b):        # regex captures the digit after B: '0' or '1'
    return '1' if b in ('B1', '1') else '_'

lines = []
lines.append('; gem48  48 states, 2 symbols  (state,2)-machine, eps1 claim')
lines.append('; Source: rocq/gemini_epsilon1_tm_48s_v2_fix.v table (audit 2026-11-04);')
lines.append('; morphett S01->0 .. S48->47, halt-rows carry their write+move (as in the .v).')
lines.append('; Start state 0 (morphett default), blank tape, head at 0.')
for q, br, w, d, nq in rows:
    lines.append(f"{qname(q)} {bit(br)} {bit(w)} {d.lower()} {qname(nq) if nq else 'halt'}")

open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines) + '\n')
print(f'wrote {OUT}: 96 data rows, {len(qs)} states')
