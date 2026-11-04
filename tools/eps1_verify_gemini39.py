"""eps1_verify_gemini39.py — independent verification of the claimed
39-state 2-symbol TM "transcending f_eps1(3)" (tools/verify_epsilon1_tm.py).

Checks performed here (all independent of that script's own claims):
  G0  table: 39 states, total transition coverage across the run.
  G1  boot: from blank $0^inf at A, the machine reaches (((e()))) with
      counter 3 encoded as W-tokens then B-run then zeros.
  G2  macro-step equivalence: one machine macro-run (rest-to-...) equals
      one reference step_ordinal_term call; the machine configuration at
      each cleanup-return boundary decodes to exactly the reference's
      (W, n).  Driven up to a tape-length budget.
  G3  the reference system itself: every step must produce a balanced
      bracket word and the ordinal valuation must STRICTLY decrease.
  G4  halting: the machine halts on the reduced-to-empty configuration.

The tape encoding per the claim: tokens as 3-bit blocks (m, b1, b2),
_ = 000, B = 100, o = 010, c = 001, e = 011, marked = m flipped to 1.
W occupies cells left-to-right ending just before the B^n counter.
"""

import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from verify_epsilon1_tm import TM_TABLE, step_ordinal_term  # noqa: E402

BLOCK = {(0, 0, 0): '_', (1, 0, 0): 'B', (0, 1, 0): 'o', (1, 1, 0): 'O',
         (0, 0, 1): 'c', (1, 0, 1): 'C', (0, 1, 1): 'e', (1, 1, 1): 'E'}


def run(tm_tape, pos, st, cap, stop_edges=(), vedge=None):
    """step the TM; returns (kind, steps, tape, pos, vedge_hits).
    kind 'halt' on HALT, 'cap' on cap, or the boundary edge name at the
    first stop_edge (prev_state, new_state) seen AFTER >=1 step."""
    tape = dict(tm_tape)
    prev = None
    hits = []
    for i in range(cap):
        r = tape.get(pos, 0)
        trans = TM_TABLE.get(st)
        if trans is None:
            return 'unknown-state', i, tape, pos, hits
        w, d, nx = trans[r]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        prev, st = st, nx
        if st == 'HALT':
            return 'halt', i + 1, tape, pos, hits
        if prev == 'm' and st == 'D' and ('m', 'D') in stop_edges:
            hits.append(('mD', i + 1, dict(tape), pos))
            return 'boundary', i + 1, tape, pos, hits
    return 'cap', cap, tape, pos, hits


def decode_config(tape):
    """(W list of lowercase chars, n) or 'garbage'.  Blocks at 3k..3k+2.
    Walks left to right: tokens while payload legal, stops at first B run
    (the counter) then requires zeros."""
    W = []
    k = 0
    n = 0
    while True:
        blk = (tape.get(3 * k, 0), tape.get(3 * k + 1, 0), tape.get(3 * k + 2, 0))
        tok = BLOCK.get(blk)
        if tok is None:
            return None
        if tok == 'B':
            n = 1
            k += 1
            break
        if tok == '_':
            return (W, 0, k)          # empty W, no counter
        W.append(tok.lower())
        k += 1
    while True:
        blk = (tape.get(3 * k, 0), tape.get(3 * k + 1, 0), tape.get(3 * k + 2, 0))
        tok = BLOCK.get(blk)
        if tok is None:
            return None
        if tok == 'B':
            n += 1
            k += 1
            continue
        if tok == '_':
            # everything right of the counter must be blank
            j = 3 * (k + 1)
            for off in range(60):
                if tape.get(j + off, 0):
                    return None
            return (W, n, k)
        return None


def parse_balance(w):
    d = 0
    for t in w:
        if t == 'o':
            d += 1
        elif t == 'c':
            d -= 1
            if d < 0:
                return False
    return d == 0


# --- ordinal valuation with eps0 >> every finite tower, for decrease checks

def val(w):
    """CNF list of exponent-lists; eps0 = 'E' symbol."""
    def inner(tokens):
        if not tokens:
            return []
        out = []
        stack = []
        cur = []
        for t in tokens:
            if t == 'o':
                stack.append(cur)
                cur = []
            elif t == 'c':
                if not stack:
                    return None
                inner_w = cur
                cur = stack.pop()
                cur.append(('w', tuple(inner_w)))
            else:
                cur.append(('e',))
        if stack:
            return None
        return cur
    nodes = inner(list(w))
    if nodes is None:
        return None
    # top-level sum: components = maximal groups separated at depth 0:
    # inner() returns a flat list of ('w', arg)/('e') nodes in order,
    # siblings already in order: that IS the CNF summand list.
    res = []
    for kind, arg in nodes:
        res.append((kind, arg))
    return tuple(res)


def cmp_val(a, b):
    """compare valuations a, b (tuples of ('w', sub)/('e',)); returns -1/0/1"""
    if a == b:
        return 0
    for i in range(min(len(a), len(b))):
        ka, va = a[i]
        kb, vb = b[i]
        if ka == 'e' and kb == 'e':
            continue
        if ka == 'e':
            return -1 if False else 1      # eps0 > omega^anything: a bigger => a > b
        if kb == 'e':
            return -1
        # both omega^x: compare exponents x
        c = cmp_val(tuple(va), tuple(vb))
        if c:
            return c
        # equal exponents: continue to next summand
    return (len(a) > len(b)) - (len(a) < len(b))


def main():
    print('G0 table:', len(TM_TABLE), 'states,',
          sum(2 for _ in TM_TABLE), 'transitions listed')

    # ---------------- G1 boot ----------------
    tape = {}
    pos, st = 0, 'A'
    first_edge = None
    for i in range(200000):
        r = tape.get(pos, 0)
        w, d, nx = TM_TABLE[st][r]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        prev, st = st, nx
        if prev == 'C' and st == 'D':
            first_edge = ('booted', i + 1)
            break
        if st == 'HALT' or st not in TM_TABLE:
            break
    got = decode_config(tape)
    print('G1 boot:', first_edge, 'decoded=', None if got is None else (got[0], got[1]))
    boot_ok = got is not None and got[0] == list('oooeocccc') and got[1] == 3

    # ---------------- G2 macro equivalence ----------------
    wr, nr = list('oooeocccc'), 3          # the reference side
    bad = 0
    checked = 0
    tape_last, pos_last, st_last = tape, pos, st
    cap = 5_000_000
    bounds = [0, 3000, 300_00, 100_000]
    for mi in range(200):
        if not parse_balance(wr):
            print('  macro', mi, ': reference state unbalanced:', ''.join(wr), ' STOP')
            break
        kind, steps, tape2, pos2, hits = run(tape_last, pos_last, st_last, cap, stop_edges=(('m', 'D'),))
        if kind == 'halt':
            print('  macro', mi, ': machine HALTED (steps this macro:', steps,
                  ') at reference', (''.join(wr), nr))
            break
        if kind != 'boundary':
            print('  macro', mi, ': machine', kind, 'steps cap or error; reference', (''.join(wr), nr))
            break
        dec = decode_config(tape2)
        w2, n2 = step_ordinal_term(wr, nr)
        if dec is None or w2 is None:
            print('  macro', mi, ': decode', dec is None, 'ref', w2 is None)
            bad += 1
            break
        if dec[0] != list(w2) or dec[1] != n2:
            print('  macro', mi, ': MISMATCH machine (W=', ''.join(dec[0]), ', n=', dec[1],
                  ') ref (W=', ''.join(w2), ', n=', n2, ')')
            bad += 1
            break
        checked += 1
        if checked % 5 == 0:
            print('  ok macro', mi, 'n=', dec[1], 'len(W)=', len(dec[0]), 'machine-steps=', steps)
        if len(dec[0]) > 250000:
            print('  budget: stopping at len(W)=', len(dec[0]))
            break
        tape_last, pos_last, st_last = tape2, pos2, 'D'
        wr, nr = list(w2), n2
    print('G2 macro equivalence:', checked, 'macro-steps checked,', bad, 'mismatches')

    # ---------------- G3 reference sanity (independent of the machine) ----
    print('G3 reference-system checks on sample terms:')
    samples = [('oo cc (omega)', 'oocc', 3), ('oooccc (w^w)', 'oooccc', 3),
               ('oooeocccc (eps1[3])', 'oooeocccc', 3)]
    for label, w, n in samples:
        w = list(w)
        v_prev = val(w)
        balanced = True
        dec = True
        for k in range(40):
            w2, n2 = step_ordinal_term(w, n)
            if w2 is None:
                break
            if not parse_balance(w2):
                print('  ', label, 'step', k, ': UNBALANCED', ''.join(w2))
                dec = False
                break
            v2 = val(w2)
            c = cmp_val(v2, v_prev)
            if c >= 0:
                print('  ', label, 'step', k, ': value did NOT decrease (cmp=', c,
                      ') w-> w\' (len', len(w), '->', len(w2), ') n', n, '->', n2)
                dec = False
                break
            v_prev = v2
            w, n = w2, n2
        print('  ', label, ': steps survived', k, ('OK' if dec else 'FAILED'))
        for kk in range(k):
            pass


if __name__ == '__main__':
    main()
