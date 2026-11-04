"""SUPER local-rewrite layer: the eps_1 fixed-seed moves as ONE 2-symbol TM.

Layout v2 (unary entries, fixed-width frames; blank pad on the left):

    ...0  1^p  F  F+1 F+2 F+3  1^{c0} 0 ... 1^{cm} 0  0 0...

  p-run right-anchored at F-1 (the I1 trick of the record: the p == 0 test,
  the spend, and the p-bump are single-cell operations); frame '000'/'100'/
  '110'; entries are unary runs each followed by one separating 0; after the
  top run's separator, pad zeros forever (the chain end is '1..10 0').

Cycle: rest at F (state IN) -> read the sign at F-1 -> scan right over the
frame and body (sign-coloured states) -> dispatch on the top run's length
class / frame kind / sign (U-chain, FL, FA) -> execute near the chain end ->
walk left home (the WA/WB chains), executing the move's p-op at F-1 on
landing -> step right into the next cycle at F.

Reachability contract (checked by running, never by hand-derivation): flags
only appear on singleton bottoms; no middle-1 entries; plain-frame bodies are
non-empty at rest.  Guard rows point to a row-free state so a broken
invariant halts loudly in the checks instead of corrupting silently.

Measured here, honestly (printed, not asserted): the state budget per phase
against the ledger hypotheses in EPS1_SUPER.md, and the blank-tape writer's
step cost.  No 40-state cap claim and no f_{eps_1}(n) claim come out of this
module; the fixed-vs-bumping fork is recorded in EPS1_SUPER.md.

Run: python tools/eps1_super_local.py    (expect ALL OK)
"""

import sys
import random

sys.path.insert(0, 'tools')

import tm as TM
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1, chain_of
import eps1_descent as D

GU = 'GU'          # the loud guard: no rows anywhere


def build(s, tower_n=3):
    T = {}
    ph = {}

    def st(name, phase):
        T[name] = {}
        ph[name] = phase

    def row(name, sym, w, d, nx):
        T[name][sym] = (w, d, nx)

    def both(name, w, d, nx):
        row(name, 0, w, d, nx)
        row(name, 1, w, d, nx)

    st(GU, 'guard')

    # ------------------------------------------------------------------ writer
    # blank -> the seed tape (p = tower_n marks, frame 110, body empty), then
    # walk back to F and enter the cycle.
    for i in range(tower_n):
        st('W%d' % i, 'writer')
        nxt = 'W%d' % (i + 1) if i < tower_n - 1 else 'Wp'
        both('W%d' % i, 1, 'R', nxt)
    st('Wp', 'writer')                    # at F: the separator
    both('Wp', 0, 'R', 'Wf0')
    st('Wf0', 'writer')                   # at F+1
    both('Wf0', 1, 'R', 'Wf1')
    st('Wf1', 'writer')                   # at F+2
    both('Wf1', 1, 'R', 'Wf2')
    st('Wf2', 'writer')                   # at F+3
    both('Wf2', 0, 'L', 'Wb1')
    st('Wb1', 'writer')                   # at F+2 ('1')
    both('Wb1', 1, 'L', 'Wb2')
    st('Wb2', 'writer')                   # at F+1 ('1')
    both('Wb2', 1, 'L', 'IN')

    st('IN', 'reader')                    # at F
    row('IN', 0, 0, 'L', 'SA')

    # ------------------------------------------------------ sign + body scan
    st('SA', 'reader')                    # at F-1
    row('SA', 0, 0, 'R', 'IA0')
    row('SA', 1, 0, 'R', 'IA1')
    for x in ('0', '1'):
        st('IA' + x, 'reader')            # at F
        row('IA' + x, 0, 0, 'R', 'GF' + x)
        st('GF' + x, 'reader')            # at F+1
        row('GF' + x, 0, 0, 'R', 'GB' + x)
        row('GF' + x, 1, 1, 'R', 'FA' + x)
        st('GB' + x, 'reader')            # at F+2 (plain frame: 0)
        row('GB' + x, 0, 0, 'R', 'GC' + x)
        st('GC' + x, 'reader')            # at F+3
        row('GC' + x, 0, 0, 'R', 'EB' + x)
        st('EB' + x, 'reader')            # at F+4
        row('EB' + x, 1, 0, 'R', 'WB1' + x)
        st('WB1' + x, 'reader')           # mid-run
        row('WB1' + x, 1, 0, 'R', 'WB1' + x)
        row('WB1' + x, 0, 0, 'R', 'WSP' + x)
        st('WSP' + x, 'reader')           # at a 0 that followed a mark
        row('WSP' + x, 0, 0, 'R', 'WPK' + x)
        row('WSP' + x, 1, 1, 'R', 'WPK' + x)   # mid-walk: next run's mark
        st('WPK' + x, 'reader')           # at the cell right of that 0
        row('WPK' + x, 1, 0, 'R', 'WB1' + x)
        row('WPK' + x, 0, 0, 'R', 'WP3' + x)
        st('WP3' + x, 'reader')           # the terminator confirmed at E+1
        row('WP3' + x, 0, 0, 'L', 'WP4' + x)
        st('WP4' + x, 'reader')           # at E+1: walk back to E-1
        row('WP4' + x, 0, 0, 'L', 'WQ1' + x)
        st('WQ1' + x, 'reader')           # at E+1
        row('WQ1' + x, 0, 0, 'L', 'WQ2' + x)
        st('WQ2' + x, 'reader')           # at E
        row('WQ2' + x, 0, 0, 'L', 'U1' + x)
        st('U1' + x, 'reader')            # at E-1 (the run's last mark)
        row('U1' + x, 1, 1, 'L', 'U2' + x)   # keep: the C-routes erase here
        st('U2' + x, 'reader')            # at E-2
        row('U2' + x, 0, 0, 'L', 'PC1' + x)     # c == 1
        row('U2' + x, 1, 0, 'L', 'U3' + x)
        st('U3' + x, 'reader')            # at E-3
        row('U3' + x, 1, 1, 'R', 'C3' + x)      # c >= 3
        row('U3' + x, 0, 0, 'R', 'AB0')         # c == 2: the absorb arm

    # --------------------------------------------------- flagged dispatches
    st('FA0', 'reader')                   # at F+2 (p == 0): the flagged fork
    row('FA0', 0, 0, 'R', 'FB')
    row('FA0', 1, 1, 'R', 'PD0')
    st('FA1', 'reader')                   # at F+2 (p >= 1): the flagged fork
    row('FA1', 0, 0, 'R', 'FB1')
    row('FA1', 1, 1, 'R', 'PDs0')
    st('FB', 'reader')                    # at F+3 (atom): step onto F+4
    row('FB', 0, 0, 'R', 'FB20')
    row('FB', 1, 1, 'R', 'FB21')
    st('FB1', 'reader')                   # at F+3 (p >= 1 arm): same step, sign kept
    row('FB1', 0, 0, 'R', 'FB21')
    row('FB1', 1, 1, 'R', 'FB21')
    st('FB20', 'reader')                  # at F+4 (p == 0)
    row('FB20', 0, 0, 'R', 'FLb')         # the empty body: the fs-limit
    row('FB20', 1, 1, 'R', 'WB10')        # entries exist: the shorten scan
    st('FB21', 'reader')                  # at F+4 (p >= 1)
    row('FB21', 0, 0, 'R', 'FLb')
    row('FB21', 1, 1, 'R', 'WB11')

    # the '01' bare fork: f1 = 0 with f2 = 1 (the frame keeps decodable flag 1)
    row('GB0', 1, 0, 'L', 'WH0')          # p == 0: erase f2; the '00' empty landing
    row('GB1', 1, 1, 'R', 'PDq0')         # p >= 1: the '01'-bare spend walk

    # ----------------------------------------------------- exec: the fs-limit
    # [ATOM] -> [NUM(1)] at F+4, frame '100' -> '000', p += s, then home.
    st('FLb', 'fs_limit')                 # at F+5 ('0'): walk the frame left, no writes yet
    row('FLb', 0, 0, 'L', 'FLc')
    row('FLb', 1, 1, 'L', 'GU')
    st('FLc', 'fs_limit')                 # at F+4 ('0')
    row('FLc', 0, 0, 'L', 'FLd')
    row('FLc', 1, 1, 'L', 'GU')
    st('FLd', 'fs_limit')                 # at F+3 ('0')
    row('FLd', 0, 0, 'L', 'FLe')
    row('FLd', 1, 1, 'L', 'GU')
    st('FLe', 'fs_limit')                 # at F+2: flags 10 -> 11 (the atom becomes NUM(1))
    row('FLe', 0, 1, 'L', 'FLf')
    row('FLe', 1, 1, 'L', 'GU')
    st('FLf', 'fs_limit')                 # at F+1 ('1'): f1 -> 0 (the '01' frame)
    row('FLf', 1, 0, 'L', 'FLg')
    row('FLf', 0, 0, 'L', 'GU')
    st('FLg', 'fs_limit')                 # at F ('0')
    row('FLg', 0, 0, 'L', 'FLh')
    row('FLg', 1, 1, 'L', 'GU')
    st('FLh', 'fs_limit')                 # at F-1: the p += s extend
    row('FLh', 0, 1, 'L', 'FLw1' if s > 1 else 'FLr0')  # p == 0: first write
    row('FLh', 1, 1, 'L', 'FLm')          # p >= 1: walk to the run's left end
    st('FLm', 'fs_limit')                 # walking left inside the p-run
    row('FLm', 1, 1, 'L', 'FLm')
    row('FLm', 0, 1, 'L', 'FLw1' if s > 1 else 'FLr0')
    # s extend-writes, each stepping further left; s - 1 extra loop states
    for i in range(1, s):
        st('FLw%d' % i, 'fs_limit')
        both('FLw%d' % i, 1, 'L', 'FLw%d' % (i + 1) if i < s - 1 else 'FLr0')
    st('FLr0', 'fs_limit')                # one past the last written mark
    both('FLr0', 0, 'R', 'FLr0b') if False else None
    row('FLr0', 0, 0, 'R', 'FLr0b')
    row('FLr0', 1, 1, 'R', 'FLr0b')
    st('FLr0b', 'fs_limit')
    row('FLr0b', 1, 1, 'R', 'FLr0b')      # over the extended run's marks
    row('FLr0b', 0, 0, 'R', 'FLr2')       # at F
    st('FLr2', 'fs_limit')                # at F+1 ('1', flags 11 now)
    row('FLr2', 1, 1, 'R', 'FLr3')
    row('FLr2', 0, 0, 'R', 'FLr3')
    st('FLr3', 'fs_limit')                # at F+2 ('1' now) or straight to F+3 when 0
    row('FLr3', 1, 1, 'R', 'FLr4')
    row('FLr3', 0, 0, 'R', 'FLr4')
    st('FLr4', 'fs_limit')                # at F+3 ('0')
    row('FLr4', 0, 0, 'R', 'FLr5')
    row('FLr4', 1, 1, 'R', 'GU')
    st('FLr5', 'fs_limit')                # at F+4 ('0')
    row('FLr5', 0, 0, 'R', 'FLr6')
    row('FLr5', 1, 1, 'R', 'GU')
    st('FLr6', 'fs_limit')                # at F+5 ('0'): walk the frame back left
    row('FLr6', 0, 0, 'L', 'FLr7')
    row('FLr6', 1, 1, 'L', 'GU')
    st('FLr7', 'fs_limit')                # at F+4 ('0')
    row('FLr7', 0, 0, 'L', 'FLr8')
    row('FLr7', 1, 1, 'L', 'GU')
    st('FLr8', 'fs_limit')                # at F+3 ('0')
    row('FLr8', 0, 0, 'L', 'FLr9')
    row('FLr8', 1, 1, 'L', 'GU')
    st('FLr9', 'fs_limit')                # at F+2 ('1')
    row('FLr9', 1, 1, 'L', 'FLr10')
    row('FLr9', 0, 0, 'L', 'GU')
    st('FLr10', 'fs_limit')               # at F+1 ('1')
    row('FLr10', 1, 1, 'L', 'FLr11')
    row('FLr10', 0, 0, 'L', 'FLr11')
    st('FLr11', 'fs_limit')               # at F ('0')
    row('FLr11', 0, 0, 'L', 'FLrm')
    row('FLr11', 1, 1, 'L', 'GU')
    st('FLrm', 'fs_limit')                # at F-1 ('1'): the extension wrote there
    row('FLrm', 1, 1, 'R', 'IN')
    row('FLrm', 0, 0, 'R', 'GU')

    # --------------------------- exec: the atom+1 fs-succ (p >= 1) chain
    # frame 110 -> 100, spawn [n+1] = s+1 marks at F+4, spend at F-1.
    st('PDs0', 'pred')                    # at F+3: the bare-b fork by the body
    row('PDs0', 0, 0, 'L', 'PDs1')        # empty body (F+4 = 0): the bare spend
    row('PDs0', 1, 1, 'R', 'PDs2')        # F+4 = 1 cannot happen at F+3; unused
    st('PDs1', 'pred')                    # at F+2 ('1'): erase (the rewrite)
    row('PDs1', 1, 0, 'R', 'PDs2')
    row('PDs1', 0, 0, 'L', 'GU')
    st('PDs2', 'pred')                    # at F+3: body check for the bare case
    row('PDs2', 0, 0, 'R', 'SW0')         # F+4 = 0: the empty pad: the spawn writer
    row('PDs2', 1, 1, 'L', 'GU')
    st('PDq0', 'pred')                    # at F+3: write the sep k-bit, then pass
    row('PDq0', 0, 1 if s > 1 else 0, 'L', 'PDq1')
    row('PDq0', 1, 1, 'L', 'PDq1')
    st('PDq1', 'pred')                    # at F+2 ('1', f2 keep)
    row('PDq1', 1, 1, 'L', 'PDq2')
    row('PDq1', 0, 0, 'L', 'GU')
    st('PDq2', 'pred')                    # at F+1 ('0'): f1 -> 1 ('01' -> '11')
    row('PDq2', 1, 1, 'L', 'PDq3')
    row('PDq2', 0, 1, 'L', 'PDq3')
    st('PDq3', 'pred')                    # at F ('0')
    row('PDq3', 0, 0, 'L', 'PDq4')
    row('PDq3', 1, 1, 'L', 'GU')
    st('PDq4', 'pred')                    # at F-1 ('1'): the spend walk begins
    row('PDq4', 1, 1, 'L', 'PDq5')
    row('PDq4', 0, 0, 'R', 'GU')
    st('PDq5', 'pred')                    # walking left inside the p-run
    row('PDq5', 1, 1, 'L', 'PDq5')
    row('PDq5', 0, 0, 'R', 'PDq6')
    st('PDq6', 'pred')                    # on the leftmost mark: ERASE it
    row('PDq6', 1, 0, 'R', 'PDq7')
    row('PDq6', 0, 0, 'R', 'GU')
    st('PDq7', 'pred')                    # walking right back over the run
    row('PDq7', 1, 1, 'R', 'PDq7')
    row('PDq7', 0, 0, 'R', 'PDq8')
    st('PDq8', 'pred')                    # at F+1: step left back onto F, into IN
    row('PDq8', 1, 1, 'L', 'IN')
    row('PDq8', 0, 0, 'L', 'IN')

    # the 'b01'-bare p == 0 succ-none arm: land the plain zero state (0, [], 0)
    st('WH0', 'walk')                     # at F+1 ('0': the '01' f1): pass
    row('WH0', 0, 0, 'L', 'WH1')
    row('WH0', 1, 1, 'L', 'GU')
    st('WH1', 'walk')                     # at F ('0')
    row('WH1', 0, 0, 'L', 'WH2')
    row('WH1', 1, 1, 'L', 'GU')
    st('WH2', 'walk')                     # at F-1 ('0' = p == 0): dance right into IN
    row('WH2', 0, 0, 'R', 'IN')
    row('WH2', 1, 1, 'R', 'GU')

    # --------------------------------------------------- exec: the atom+1 pred
    # frame 110 -> 100 (bottom eps_0+2 -> eps_0+1).  No p-op, tiny walk.
    st('PD0', 'pred')                     # at F+3 ('0'): step back to F+2
    row('PD0', 0, 0, 'L', 'PDh')
    row('PD0', 1, 1, 'L', 'PDh')
    st('PDh', 'pred')                     # at F+2 ('1'): erase the atom+1 mark
    row('PDh', 1, 0, 'R', 'PD1')
    row('PDh', 0, 0, 'L', 'GU')
    st('PD1', 'pred')                     # at F+3
    row('PD1', 0, 0, 'L', 'PD2')
    st('PD2', 'pred')                     # at F+2 (0 post-write)
    row('PD2', 0, 0, 'L', 'PD3')
    st('PD3', 'pred')                     # at F+1 ('1', the atom mark)
    row('PD3', 1, 1, 'L', 'PD4')
    row('PD3', 0, 0, 'L', 'GU')
    st('PD4', 'pred')                     # at F
    row('PD4', 0, 0, 'L', 'PD5')
    row('PD4', 1, 1, 'L', 'PD5')
    st('PD5', 'pred')                     # at F-1: dance right back into IN
    row('PD5', 0, 0, 'R', 'IN')
    row('PD5', 1, 1, 'R', 'IN')

    # exec: the c == 2 absorb (shared): erase both marks, walk home with +1
    st('AB0', 'pred')                     # at E-2 ('1'): erase, right
    row('AB0', 1, 0, 'R', 'AB1')
    row('AB0', 0, 0, 'R', 'GU')
    st('AB1', 'pred')                     # at E-1 ('1'): erase, left
    row('AB1', 1, 0, 'L', 'AB2')
    row('AB1', 0, 0, 'R', 'GU')
    st('AB2', 'pred')                     # at E-2 post-erase ('0'): into the walk-home
    row('AB2', 0, 0, 'L', 'WB0p')
    row('AB2', 1, 1, 'L', 'WB0p')

    # =========================================== exec: c == 1 (bottom [NUM(1)])
    # p == 0: halt at the dispatch (PC10, no rows: the model's final move).
    # p >= 1: the head-empty arm (an fs-succ): spend, erase, write run s+1.
    st('PC10', 'halt')                    # no rows: the machine stops here
    st('PC11', 'pred')
    row('PC11', 0, 0, 'L', 'HC0')
    row('HC0', 0, 0, 'L', 'HC1') if False else None
    for a, b in (('HC0', 'HC1'), ('HC1', 'HC2'), ('HC2', 'HC3')):
        st(a, 'pred')
        row(a, 0, 0, 'L', b)
        row(a, 1, 1, 'L', b)
    st('HC3', 'pred')                     # at F-1 ('1'): walk to the left end
    row('HC3', 1, 1, 'L', 'HLa')
    row('HC3', 0, 0, 'R', 'GU')
    st('HLa', 'pred')                     # walking left inside the p-run
    row('HLa', 1, 1, 'L', 'HLa')
    row('HLa', 0, 0, 'R', 'HLb')
    st('HLb', 'pred')                     # on the pad: step right onto the mark
    row('HLb', 0, 0, 'R', 'HLc')
    st('HLc', 'pred')                     # on the leftmost mark: ERASE it
    row('HLc', 1, 0, 'R', 'HLd')
    row('HLc', 0, 0, 'R', 'GU')
    st('HLd', 'pred')                     # walking right over the rest of the run
    row('HLd', 1, 1, 'R', 'HLd')
    row('HLd', 0, 0, 'R', 'HLe')
    st('HLe', 'pred')                     # at F: right to F+4
    row('HLe', 0, 0, 'R', 'HC5')
    st('HC5', 'pred')
    for a, b in (('HC5', 'HC6'), ('HC6', 'HC7'), ('HC7', 'HC8'), ('HC8', 'HC9')):
        if a != 'HC5':
            st(a, 'pred')
        row(a, 0, 0, 'R', b)
    st('HC9', 'pred')                     # at F+5: step left onto F+4
    row('HC9', 0, 0, 'L', 'SW0')          # the head lands in SW0: write here
    row('HC9', 1, 1, 'L', 'GU')

    # ---------------------------------------------- the spawn writer (s+1 marks)
    for i in range(s + 1):
        st('SW%d' % i, 'spawn')
        nxt = 'SW%d' % (i + 1) if i < s else 'SWz'
        both('SW%d' % i, 1, 'R', nxt)
    st('SWz', 'spawn')                    # on the pad after the run: home
    row('SWz', 0, 0, 'R', 'INx') if False else None
    row('SWz', 0, 0, 'L', 'WB1p')         # left onto the run's last mark
    row('SWz', 1, 1, 'R', GU)

    # ================================================ execs for c >= 2 (sign)
    # c >= 3: erase E-1; p == 0: shorten in place; p >= 1: spawn then the walk.
    for x in ('0', '1'):
        st('C3' + x, x == '0' and 'pred' or 'fs_succ')
        row('C3' + x, 1, 1, 'R', 'C3a' + x)
        row('C3' + x, 0, 0, 'R', GU)
        st('C3a' + x, x == '0' and 'pred' or 'fs_succ')     # at E-1: erase it
        row('C3a' + x, 1, 0, 'L', 'C3b' + x)
        row('C3a' + x, 0, 0, 'L', GU)
        st('C3b' + x, x == '0' and 'pred' or 'fs_succ')     # at E-2 post-erase (mark)
        if x == '0':
            row('C3b' + x, 1, 1, 'L', 'WA1')     # shorten: home, no p-op
            row('C3b' + x, 0, 0, 'R', GU)
        else:
            row('C3b' + x, 1, 1, 'R', 'C3d')     # fs-succ: right to E, spawn
            row('C3b' + x, 0, 0, 'L', GU)
        st('C3d', 'fs_succ')
        row('C3d', 0, 0, 'R', 'SW0')
        row('C3d', 1, 1, 'R', GU)

    # ---------------------------------------------------------- c == 2 (sign)
    for x in ('0', '1'):
        st('C2T' + x, x == '0' and 'pred' or 'fs_succ')
        if x == '0':
            row('C2T' + x, 0, 0, 'R', 'C2B')     # bottom: shorten (c -> 1)
            row('C2T' + x, 1, 1, 'R', 'C2A')     # non-bottom: the absorb
        else:
            row('C2T' + x, 0, 0, 'R', 'F2E')     # fs-succ (no test needed)
            row('C2T' + x, 1, 1, 'R', 'F2E')
    st('C2B', 'pred')
    row('C2B', 0, 0, 'R', 'C2Ba')                # at E-3
    row('C2B', 1, 1, 'R', GU)
    st('C2Ba', 'pred')                           # at E-2
    row('C2Ba', 1, 1, 'R', 'C2Bb')
    st('C2Bb', 'pred')                           # at E-1: erase it
    row('C2Bb', 1, 0, 'L', 'C2Bc')
    row('C2Bb', 0, 0, 'R', GU)
    st('C2Bc', 'pred')                           # at E-2: fold = erase it
    row('C2Bc', 1, 0, 'L', 'C2P')
    st('C2P', 'pred')                            # at E-3 (sep): hop left
    row('C2P', 0, 0, 'L', 'C2Q')
    row('C2P', 1, 1, 'L', 'C2Q')
    st('C2Q', 'pred')                            # at F+2 (f2, keep)
    row('C2Q', 0, 0, 'L', 'C2R')
    row('C2Q', 1, 1, 'L', 'C2R')
    st('C2R', 'pred')                            # at F+1 (f1, keep)
    row('C2R', 0, 0, 'L', 'C2S')
    row('C2R', 1, 1, 'L', 'C2S')
    st('C2S', 'pred');                           # at F
    row('C2S', 0, 0, 'L', 'WB6p')
    row('C2S', 1, 1, 'L', 'GU')
    st('C2A', 'pred')                            # at E-3 ('0'): step to E-2
    row('C2A', 0, 0, 'R', 'C2Aa')
    row('C2A', 1, 1, 'R', GU)
    st('C2Aa', 'pred')                           # at E-2 ('1'): step to E-1
    row('C2Aa', 1, 1, 'R', 'C2Ab')
    row('C2Aa', 0, 0, 'R', GU)
    st('C2Ab', 'pred')                           # at E-1: erase it
    row('C2Ab', 1, 0, 'R', 'C2Ac')
    st('C2Ac', 'pred')                           # at E-2 post-erase2 ('1')
    row('C2Ac', 1, 0, 'L', 'C2Ad')
    row('C2Ac', 0, 0, 'L', GU)
    st('C2Ad', 'pred')                           # at E-3 ('0')
    row('C2Ad', 0, 0, 'L', 'C2Ae')
    row('C2Ad', 1, 1, 'L', GU)
    st('C2Ae', 'pred')                           # at E-3
    row('C2Ae', 0, 0, 'L', 'C2Af')
    st('C2Af', 'pred')                           # at E-4 (the below's mark)
    row('C2Af', 1, 1, 'L', 'WB1p')               # home with the p-op tail
    st('F2E', 'fs_succ')                         # at E-3 ('0'): step to E-2
    row('F2E', 0, 0, 'R', 'F2Ea')
    row('F2E', 1, 1, 'R', GU)
    st('F2Ea', 'fs_succ')                        # at E-2 ('1'): step to E-1
    row('F2Ea', 1, 1, 'R', 'F2Eb')
    row('F2Ea', 0, 0, 'R', GU)
    st('F2Eb', 'fs_succ')                        # at E-1: erase it
    row('F2Eb', 1, 0, 'L', 'F2Ec')
    row('F2Eb', 0, 0, 'R', GU)
    st('F2Ec', 'fs_succ')                        # at E-2 ('1'): step right, spawn
    row('F2Ec', 1, 1, 'R', 'F2Ed')
    row('F2Ec', 0, 0, 'R', GU)
    st('F2Ed', 'fs_succ')                        # at E-1 (0' post-erase): to E
    row('F2Ed', 0, 0, 'R', 'SW0')
    row('F2Ed', 1, 1, 'R', GU)

    # =================================================== the walk-home chains
    # no-op chain (shorten paths and the fs-limit's return): F-1 left as-is.
    st('WA1', 'walk')                     # at a mark, walking left
    row('WA1', 1, 1, 'L', 'WA1')
    row('WA1', 0, 0, 'L', 'WA2')
    st('WA2', 'walk')                     # at a 0 crossed from a mark
    row('WA2', 1, 1, 'L', 'WA1')
    row('WA2', 0, 0, 'L', 'WA3')          # the frame zone entered at F+3
    st('WA3', 'walk')                     # at F+1 (0 plain / 1 atom: keep)
    row('WA3', 0, 0, 'L', 'WA4')
    row('WA3', 1, 1, 'L', 'WA4')
    st('WA4', 'walk')                     # at F ('0'): hop to F-1
    row('WA4', 0, 0, 'L', 'WA6')
    row('WA4', 1, 1, 'L', 'WA6')
    st('WA5', 'walk')                     # at F ('0')
    row('WA5', 0, 0, 'L', 'WA6')
    row('WA5', 1, 1, 'L', GU)
    st('WA6', 'walk')                     # at F-1: no p-op (both signs)
    row('WA6', 0, 0, 'R', 'IN')
    row('WA6', 1, 1, 'R', 'IN')
    # p-op chain (absorb: p += 1; fs-succ: p -= 1): the landing writes.
    st('WB1p', 'walk')
    row('WB1p', 1, 1, 'L', 'WB1p')
    row('WB1p', 0, 0, 'L', 'WB2p')
    st('WB2p', 'walk')
    row('WB2p', 1, 1, 'L', 'WB1p')
    row('WB2p', 0, 0, 'L', 'WB3p')
    st('WB3p', 'walk')                    # at F+1 ('0' plain / '1' atom)
    row('WB3p', 0, 0, 'L', 'WB4p')
    row('WB3p', 1, 1, 'L', 'WB4q')
    st('WB4p', 'walk')                    # at F ('0')
    row('WB4p', 0, 0, 'L', 'WB6p')
    row('WB4p', 1, 1, 'L', GU)
    st('WB4q', 'walk')                    # at F (the atom path)
    row('WB4q', 0, 0, 'L', 'WB6p')
    row('WB4q', 1, 1, 'L', GU)
    st('WB6p', 'walk')                    # at F-1: 0 -> +1, 1 -> leftmost erase
    row('WB6p', 0, 1, 'R', 'IN')
    row('WB6p', 1, 1, 'L', 'WL0')
    st('WL0', 'walk')                     # walking left inside the p-run
    row('WL0', 1, 1, 'L', 'WL0')
    row('WL0', 0, 0, 'R', 'WL2')
    st('WL2', 'walk')                     # on the leftmost mark: ERASE it
    row('WL2', 1, 0, 'R', 'WL3')
    row('WL2', 0, 0, 'R', 'GU')
    st('WL3', 'walk')                     # walking right over the rest of the run
    row('WL3', 1, 1, 'R', 'WL3')
    row('WL3', 0, 0, 'L', 'WL4')
    st('WL4', 'walk')                     # at F-1: dance right into the cycle
    row('WL4', 0, 0, 'R', 'IN')
    row('WL4', 1, 1, 'R', 'IN')
    # entry used when the walk starts on a pad 0 (after the spawn) with the
    # p-op tail: land on the run's mark, then the p-op chain.
    st('WB0p', 'walk')
    row('WB0p', 0, 0, 'L', 'WB1p')
    row('WB0p', 1, 1, 'L', GU)

    # decide-rows only branch; their write must equal the read symbol
    for name in ('SA', 'FA0', 'FA1'):
        d, nx = T[name][1][1], T[name][1][2]
        row(name, 1, 1, d, nx)            # the decide row keeps the bit it read
    for x in ('0', '1'):
        row('GF' + x, 1, 1, 'R', T['GF' + x][1][2])   # the flag bit must survive
        row('EB' + x, 1, 1, 'R', T['EB' + x][1][2])   # the body mark must survive
        row('WB1' + x, 1, 1, 'R', T['WB1' + x][1][1:] and T['WB1' + x][1][2])
        row('WB1' + x, 0, 0, 'R', T['WB1' + x][0][2])
        row('WPK' + x, 1, 1, 'R', T['WPK' + x][1][2])
        for base in ('U1', 'U2', 'U3', 'C3'):
            nm = base + x
            d, nx = T[nm][1][1], T[nm][1][2]
            row(nm, 1, 1, d, nx)
    # ================================================ flatten into a TM table
    order = list(T.keys())
    id_of = {n: i for i, n in enumerate(order)}
    lines = []
    for n in order:
        for sym in (0, 1):
            r = T[n].get(sym)
            if r is None:
                continue
            w, d, nx = r
            if nx == GU:
                lines.append('%d %d %d %s H' % (id_of[n], sym, w, d))
            else:
                lines.append('%d %d %d %s %d' % (id_of[n], sym, w, d, id_of[nx]))
    return lines, T, ph, id_of


def encode(p, chain):
    chain = list(chain)
    while len(chain) > 1 and isinstance(chain[-1], int) and chain[-1] == 1:
        chain.pop()
        p += 1
    fr = '000'
    entries = []
    if chain:
        if isinstance(chain[0], D.Ord):
            entries = list(chain[1:])
            fr = '100' if chain[0].is_atom() else '110'
        else:
            entries = list(chain)
    body = ''.join('1' * c + '0' for c in entries)
    return '1' * p + '0' + fr + body + '0'


def decode(tape, head=0):
    at = lambda k: tape.get(k, 0)
    p, k = 0, head - 1
    while at(k) == 1:
        p += 1
        k -= 1
    f1, f2 = at(head + 1), at(head + 2)
    chain = []
    j = head + 4
    while True:
        if at(j) == 0 and at(j + 1) == 0:
            return (p, chain, f1 * 10 + f2)
        c = 0
        while at(j) == 1:
            c += 1
            j += 1
        if c == 0 or at(j) != 0:
            return None
        chain.append(c)
        j += 1


def shape(chain, flag=0):
    """The frame + entries as a hashable shape, across NUM/Ord spellings."""
    if flag == 10:
        return ('a', tuple(int(b) for b in chain))
    if flag == 1:
        return ('b', tuple(int(b) for b in chain))
    if flag == 11:
        return ('b', tuple(int(b) for b in chain))
    ents = list(chain)
    bottom = None
    if ents and isinstance(ents[0], D.Ord):
        bottom = 'a' if ents[0].is_atom() else 'b'
        ents = ents[1:]
    return (bottom, tuple(int(b) for b in ents))


def fixed_chain_run(p, chain, sn, cap=60000):
    """The fixed-parameter reference: C.step with the seed every move."""
    moves = 0
    chain = list(chain)
    while moves < cap:
        try:
            p, chain, _n, _k = C.step(p, chain, sn)
        except C.Halt:
            return moves
        moves += 1
    return None


def main():
    ok = True
    print('=' * 72)
    for s in (1, 2):
        lines, T, ph, id_of = build(s)
        mo = TM.parse_table('\n'.join(lines))
        print('machine s = %d' % s)
        cnt = {}
        for name, rows in T.items():
            if rows or name == GU:
                cnt.setdefault(ph.get(name, 'other'), set()).add(name)
        budgets = {'reader': 10, 'pred': 12, 'fs_limit': 12, 'writer': 6}
        for k in sorted(cnt):
            b = budgets.get(k)
            print('  %-10s %2d states%s' % (k, len(cnt[k]),
                                            ' (ledger hypothesis %d)' % b if b else ''))
        print('  TOTAL STATES: %d  (40-target: %s)' % (
            mo.n, 'met' if mo.n <= 40 else 'not met (measured, honestly)'))
        # the writer from blank
        tape = {}
        head, state, steps = 0, id_of['W0'], 0
        while state != id_of['IN'] and steps < 10000:
            r = mo.step(tape, head, state)
            head, state = r
            steps += 1
        got = decode(tape, head)
        ok_seed = got == (3, [], 11)
        print('  writer: %d steps from blank; decodes to %r : %s'
              % (steps, got, 'OK' if ok_seed else 'FAIL'))
        ok = ok and ok_seed
        # ------------- full runs: the machine from the seed vs the fixed model
        for t_n in (1, 2, 3):
            mp, mc = chain_of(D.tower(t_n))
            for sn in (s, ):                  # the build's own seed only
                tape0 = {i: int(ch) for i, ch in enumerate(encode(t_n, [ATOM1]))}
                head, state, steps, moves = t_n, id_of['IN'], 0, 0
                bad = 0
                halted = False
                while steps < 60000:
                    r = mo.step(tape0, head, state)
                    steps += 1
                    if r is None:
                        if state == id_of['PC10']:
                            moves += 1    # the halting dispatch = the final move
                        halted = True
                        break
                    head, state = r
                    if state == id_of['IN']:
                        g = decode(tape0, head)
                        try:
                            p1, c1, _n, kind = C.step(mp, list(mc), sn)
                        except C.Halt:
                            halted = True
                            break
                        want_p, want_c = C.normalise(p1, list(c1))
                        if g is None or g[0] != want_p or \
                                shape(g[1], g[2]) != shape(want_c):
                            bad += 1
                            if bad < 3:
                                print('    UNFAITHFUL move %d: tape %r vs model %r'
                                      % (moves, g, (want_p, want_c)))
                        else:
                            mp, mc = p1, list(c1)
                        moves += 1
                ref = fixed_chain_run(*chain_of(D.tower(t_n)), sn)
                same = ref == moves
                print('  eps_1[%d] seed %d: machine %d moves vs fixed model %d : %s%s'
                      % (t_n, sn, moves, ref,
                         'OK' if same else 'MISMATCH',
                         '  (halted: %d steps, decodes %r)' % (steps, decode(tape0, head)) if halted else ''))
                ok = ok and not bad and same
        print()
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
