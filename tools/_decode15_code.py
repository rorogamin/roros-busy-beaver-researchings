"""Trace every entry into the 15-state candidate's H (state 7) code.

Run: python tools/_decode15_code.py [cap] [window]
"""

import sys

sys.path.insert(0, 'tools')

import tm


def window(tape, head, back=30, fwd=80):
    lo, hi = head - back, head + fwd
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    k = head - lo
    return s[:k] + '<' + s[k] + '>' + s[k + 1:]


def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
    w = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    m = tm.load('machines/candidate_15_omega2.txt')
    tape, head, state = {}, 0, 0
    visits = []
    logs = []
    log_until = -1
    for i in range(1, cap + 1):
        read = tape.get(head, 0)
        if state == 7:
            visits.append((i, head, read))
            if len(visits) <= 2:
                log_until = i + w
                logs.append([f'--- H entry {len(visits)} at step {i} head {head} '
                             f'read {read} tape {window(tape, head)}'])
        if i <= log_until:
            nxt = m.t.get((state, read))
            act = 'HALT' if nxt is None else f'w{nxt[0]} {nxt[1]} {nxt[2]}'
            logs[-1].append(f'  t={i} s={state} h={head} r={read} -> {act}')
        r = m.step(tape, head, state)
        if r is None:
            print(f'HALT at {i}')
            break
        head, state = r
    print(f'cap={cap:,} H entries={len(visits)}')
    print('H entry steps: ' + ', '.join(str(v[0]) for v in visits[:40]))
    for block in logs:
        print('\n'.join(block))
        print()
    print('final tape around head: ' + window(tape, head, 20, 100))


if __name__ == '__main__':
    main()
