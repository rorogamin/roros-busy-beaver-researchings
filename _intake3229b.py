import sys, io
sys.path.insert(0, 'tools')
from bbmulti import parse, run

MACHINES = [
 ('BB(8,4)', 'f_(w+2)(83)',
  '1LH3LB2RD2RA_2LC3RB1LC2RA_3RB1LB3LC2RC_0RF2LD1LD2LE_3RE3LB2RE2LE_0LG1RZ------_1LG2RD1LG3RG_0LB---0LH2RB'),
 ('BB(8,4)', 'f_(w+2)(f_w(f_w(f_w(f_w(12)))))',
  '1RC3LB2RD2RA_1RF3RB1LC2RA_3RB1LB3LC2RC_0RF2LD1LD2LE_3RE3LB2RE2LE_0LG0LH1RZ3RB_1LG2RD1LG3RG_0LH0LC0LH3RD'),
 ('BB(9,4)', 'f_(w+2)(f_(w+2)(f_w(f_w(f_w(f_w(12))))))',
  '0RB3LB2RD2RA_0LI3RB1LC2RA_3RB1LB3LC2RC_0RF2LD1LD2LE_3RE3LB2RE2LE_0LG0LH1RZ---_1LG2RD1LG3RG_0LH3LC0LH3RD_1LA------1RA'),
 ('BB(9,4)', 'f_(w+3)(10)',
  '0LB3LB2RD2RA_2LI3RB1LC2RA_3RB1LB3LC2RC_0RF2LD1LD2LE_3RE3LB2RE2LE_0LG0LH1RZ---_1LG2RD1LG3RG_0LH---0LH3RD_2RI3RF2RB1LI'),
 ('BB(9,4)', 'f_(w+3)(16)',
  '2LI3LB2RD2RA_2LC3RB1LC2RA_3RB1LB3LC2RC_0RF2LD1LD2LE_3RE3LB2RE2LE_0LG0LH1RZ---_1LG2RD1LG3RG_0LH---0LH3RD_2LB---1LI3RF'),
 ('BB(4,6)', 'f_(w+1)(2{15}5)',
  '1RB3LB5LD2RA4LB5LB_2LC3RB1LC2RA3LC1RZ_3RB1LB3LC2RC4LC5LC_3RC---4LD4LD------'),
 ('BB(5,5) [BBi(20) champion]', 'f_(w+1)(f_w(f_w(f_w(f_w(6)))))',
  '1LB3LB4LC2RA4LB_3LE3RB1LC2RA4RD_3RB1LB3LC2RC4LC_1RZ------4LD4LE_3RB------4LE3LC'),
 ('BB(6,5) [BBi(21)]', 'f_(w+2)(4)',
  '4RF3LB4LC2RA4LB_2LC3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---------4LD4LE_3RB------4LE3LC_3RC------------'),
 ('BB(6,5) [BBi(22)]', 'f_(w+2)(9)',
  '1RC3LB4LC2RA4LB_4RF3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---------4LD4LE_3RB------4LE3LC_2LE3RC---------'),
 ('BB(6,5)', 'f_(w+2)(126)',
  '0LB3LB4LC2RA4LB_1LF3RB1LC2RA4RD_3RB1LB3LC2RC4LC_1RZ------4LD4LE_3RB------4LE3LC_4RF3RE---0RA3LC'),
 ('BB(6,5)', 'f_(w+2)(176)',
  '0LF3LB4LC2RA4LB_4RF3RB1LC2RA4RD_3RB1LB3LC2RC4LC_1RZ------4LD4LE_3RB------4LE3LC_2LE2RB1LF1RB1LA'),
 ('BB(6,5) [BBi(26) champion]', 'f_(w+3)(11)',
  '2LE3LB4LC2RA4LB_4RA3RB1LC2RA4RD_3RB1LB3LC2RC4LC_1RZ3LF1LA4LD4LE_3RB---0RD4LE3LC_4LC------3LF3LF'),
 ('BB(7,5) [BBi(27)]', 'f_(w+3)(17)',
  '0LG3LB4LC2RA4LB_2LC3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---3LF---4LD4LE_3RB------4LE3LC_4LC------3LF3LF_1RB---1LG1LF---'),
 ('BB(7,5)', 'f_(w+3)(f_(w+3)(10))',
  '2LE3LB4LC2RA4LB_4RA3RB1LC2RA4RD_3RB1LB3LC2RC4LC_---3LF1LG4LD4LE_3RB---1LE4LE3LC_4LC------3LF3LF_3LF------1LG1LG'),
 ('BB(8,5) [BBi(28)]', 'f_(w*2)(17)',
  '1RG3LB---2RA---_------1LD2RA---_3RB1LB3LC2RC---_3RE---3LC2RC---_---3RE---4LH---_4RA3LG---2RF4LG_2LH3RG1LH2RF2RA_3RG1LG3LH2RH4LH'),
 ('BB(8,5)', 'f_(w*2)(32)',
  '0LB3LB1RZ2RA4RB_0LD1RB1LD2RA1LE_3RB1LB3LC2RC3LF_3RE2LF3LC2RC4LF_0LF3RE0LG4LH2LB_0LE3LG4LC2RF4LG_1LC3RG1LH2RF2RA_3RG1LG3LH2RH4LH'),
 ('BB(8,5) [BBi(36)]', 'f_(w*2+1)(93)',
  '2RG3LB4LC2RA4LB_1RZ---1LD2RA4LD_3RB1LB3LC2RC4LC_3RE---3LC2RC3LC_---3RE4LE4LH4RB_4LE3LG3LB2RF4LG_2LH3RG1LH2RF2RA_3RG1LG3LH2RH4LH'),
 ('BB(11,4)', 'f_(w*2)(21)',
  '1RG3LB1RZ2RA_2LD---1LD2RA_3RB1LB3LC2RC_3RE---3LC2RC_---3RE3LH2LF_3RF2RF2LE1LF_2LC3LH2LJ2RG_---3RH1LI2RG_3RH1LH3LI2RI_------3LJ3RK_------2RA3RK'),
 ('BB(11,4) [potential, "probably can reach"]', 'f_(w*2)(2{11}6)',
  '1RG3LB1RZ2RA_0LG0LE1LD2RA_3RB1LB3LC2RC_3RE---3LC2RC_0LC3RE3LH2LF_3RF2RF2LE1LF_2LC3LH2LJ2RG_3LG3RH1LI2RG_3RH1LH3LI2RI_0LH2LI3LJ3RK_------2RA3RK'),
 ('BB(11,4)', 'f_(w*2)(98)',
  '1RG3LB1RZ2RA_0LG---1LD2RA_3RB1LB3LC2RC_3RE0LA3LC2RC_1RI3RE3LH2LF_3RF2RF2LE1LF_2LC3LH2LJ2RG_0RG3RH1LI2RG_3RH1LH3LI2RI_------3LJ3RK_------2RA3RK'),
 ('BB(3,7)', 'f_(w+1)(117)',
  '6LC3LB6RA2RA4LB5LC5LA_1RZ3RB1LC2RA3RB4LC5RA_3RB1LB3LC2RC4LC1RA6LA'),
 ('BB(4,7)', 'f_(w+2)(124)',
  '6LD3LB5LD2RA4LB3LC5LA_1RZ3RB1LC2RA3RD---2RA_3RB1LB3LC2RC4LC3LC5LD_3RB---6LC4LD4LC4LD---'),
 ('BB(11,4) [new 2026-11-06]', 'f_(w*2)(2{11}6)',
  '1RK3LB1RZ2RA_0LG1LE1LD2RA_3RB1LB3LC2RC_3RE0LI3LC2RC_1RJ3RE3LH2LF_3RF2RF2LE1LF_3LC3LH2LJ2RG_0LE3RH1LI2RG_3RH1LH3LI2RI_0LB0LJ3LJ3RK_2LC0LD2RA3RK'),
 ('BB(8,6) [new 2026-11-06]', 'f_(w^2+1)(f_w(31))',
  '5LH3LB2LH2RA4LB1RZ_2RC3RB1LD2RA3LF5RB_3RB1LB3LC2RC4LC1LE_3RB3RE3LC2RC---3RD_5RB3RE1LE4LC3LG5LE_5RB5RB---1LF5LF5LF_5LF4RG1LB1LG2LG5LG_0LC---1LH1LH---5RG'),
]

# The 2026-11-06 BB(4,7) f_(w+3)(34) string is malformed as posted
# (state D has 8 actions for a 7-symbol machine); see championsReal.txt.
# It is deliberately not run here until the claimant supplies a correction.

BUDGET = 2_000_000
MARKS = (10, 100, 1000, 10_000, 100_000, 1_000_000)

out = io.StringIO()
allok = True
for tag, claim, text in MACHINES:
    try:
        table, nst, nsym = parse(text)
    except ValueError as e:
        print(f'PARSE FAIL {tag} {e}', flush=True)
        allok = False
        continue
    steps, halted, score, used_st, used_w, log = run(table, BUDGET, MARKS)
    missing = sum(1 for st in range(nst) for sym in range(nsym)
                  if (('ABCDEFGHIJKLMNOPQRSTUVWXY'[st], sym) not in table))
    line1 = (f'  {tag} {nst}x{nsym}, {len(table)} defined transitions, '
             f'undefined={missing}: blank tape {BUDGET:,} steps: '
             f'halted={halted} steps={steps:,} score={score:,}')
    line2 = ('  milestones: ' + (', '.join(f'{m:,}@{s:,}' for m, s in log) if log else 'none')
             + f'; states visited {len(used_st)}/{nst}; symbols written {sorted(used_w)}')
    print(line1, flush=True)
    print(line2, flush=True)
    if halted:
        allok = False
    out.write(line1 + '\n' + line2 + '\n')

open('_intake3229b_results.txt', 'w').write(out.getvalue())
print('ALL RUNS OK (no halt)' if allok else 'HALT OR PARSE FAIL: see above', flush=True)
