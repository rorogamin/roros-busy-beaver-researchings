"""Emit CHAMPIONS_2026_11_23.md from the verified champion JSON."""
import json, os, sys

ROOT = r'C:\Users\Rowan\Documents\findthatmachine'
OUT = os.path.join(ROOT, 'work', 'out')


def main():
    d = json.load(open(os.path.join(OUT, 'champions_2026_11_23.json'), encoding='utf-8'))
    L = []
    A = L.append
    A('# Busy Beaver Champions — 2026-11-23 batch')
    A('')
    A(f'{len(d)} machines, each one an exact blank-tape bootstrap into a proven '
      'Busy Beaver core, with a kernel-checked Lean 4 certificate.')
    A('')
    A('## Method')
    A('')
    A('1. Every core in `search/bbcores_plus.txt` (96 cores, up to `fe1_8` = '
      'f_{ε₁}) was run against every reachable `(states, symbols)` cell with '
      '`bbsearch_mc`, 4 strongest-fitting cores per cell, 1.2e8-step budget, '
      '20,000-cell tape cap.')
    A('2. A hit is kept only if the exact Python mirror of `BB/TM.lean` reproduces '
      'the landed landmark, every state and every symbol occurs in the run '
      '(irreducibility), and the machine survives 5,000 steps past the landmark.')
    A('3. A cell is claimed only if it is empty in the 51-machine Nov 21 batch and '
      'the Rocq `BB<n>_<m>.v` corpus, or if the new bound is strictly higher in the '
      'ordinal hierarchy.')
    A('')
    A('## Champions')
    A('')
    A('| cell | bound | core | landmark step |')
    A('|---|---|---|---|')
    for e in sorted(d, key=lambda x: (x['symbols'], x['states'])):
        A(f"| **BB({e['states']},{e['symbols']})** | `{e['bound']}` | "
          f"`{e['core']}` | {e['halted_at']} |")
    A('')
    A('## Certificates')
    A('')
    A('Each machine has, in `lean/BB/Champions2026_11_23_S<m>.lean`:')
    A('')
    A('- `tm_<n>_<m> : TM` — the exact transition table;')
    A('- `valid_<n>_<m> : ValidTM <n> <m> tm_<n>_<m>` — every write and target state '
      'is in range and everything outside the domain is `none`;')
    A('- `landmark_<n>_<m> : Config` and '
      '`reaches_landmark_<n>_<m> : steps tm <n>_<m> K initConfig = some landmark_<n>_<m>` '
      '— exact `K`-step execution from the blank tape, proved by 35-step `rfl` '
      'chunks glued with `steps_add`, the same structure as the Nov 21 batch.')
    A('')
    A('The reach theorem is what turns the machine into a champion: the landmark is '
      'the input configuration of the core, so the core\'s halting theorem '
      '(`Fe1_6_halts`, `Fe1_7_halts`, `Fe1_8_halts`, `Fwpw_*`, `Fwp2_*`, …) applies '
      'and gives `HaltsIn tm ... t` with `t` above the stated ordinal bound. The '
      'bound column is that core bound evaluated at the landmark counters.')
    A('')
    A('## Verification')
    A('')
    A('- `verify_champions_2026_11_23.py` re-simulates every machine from '
      '`0^inf A> 0^inf`, checks the exact landmark, 5,000 post-landmark steps, '
      'irreducibility, and cell disjointness against the Nov 21 batch.')
    A('- Every Lean module compiles with `lean -j 1 -M 4096`, and every theorem is '
      '`#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` only — '
      'no `sorry`, no `native_decide`).')
    A('')
    A('## Caveat')
    A('')
    A('The Lean certificate proves the machine is a valid n×m machine and reaches '
      'the core landmark in exactly K steps. The *halting* and the ordinal lower '
      'bound follow from the core theorem, whose formal proof lives in the Rocq '
      '`Fe1.v` / `Fwpw_*.v` / `Fwp2_*.v` files; those theorems are parameterized by '
      'a core-containment predicate, so a machine whose landmark carries extra '
      'non-blank tape beyond the matched prefix needs the core predicate checked '
      'for that exact tape before the composition is formal end-to-end.')
    p = os.path.join(OUT, 'CHAMPIONS_2026_11_23.md')
    open(p, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
    print('wrote', p, len(d), 'champions')


if __name__ == '__main__':
    main()
