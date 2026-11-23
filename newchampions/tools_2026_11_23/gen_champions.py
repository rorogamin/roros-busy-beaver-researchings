"""Turn sweep hits into verified champions + Lean 4 kernel certificates."""
import json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tm as T

ROOT = r'C:\Users\Rowan\Documents\findthatmachine'
HITS = os.path.join(ROOT, 'work', 'hits.jsonl')
OUT = os.path.join(ROOT, 'work', 'out')
NC = os.path.join(ROOT, 'repos', 'roros-busy-beaver-researchings', 'newchampions')
os.makedirs(OUT, exist_ok=True)


def core_base(core):
    """Strip trailing symbol-count / variant tokens from a core name."""
    b = core
    for suf in ('_blank', '_sw', '_opt', '_i', 'i'):
        if b.endswith(suf) and not b.endswith('_blank'):
            b = b[:-len(suf)]
            break
    if b.endswith('_blank'):
        b = b[:-6]
    parts = b.split('_')
    while len(parts) > 1 and parts[-1].isdigit():
        parts.pop()
    return '_'.join(parts)


def family_rank(core):
    """(family, offset) with family 6=epsilon1 .. 1=omega."""
    b = core_base(core)
    if b.startswith('fe1'):  return (6, 0)
    if b.startswith('fe0'):  return (5, 0)
    for pre, fam in (('fwpw', 4), ('fwp2', 3), ('fwm2', 2), ('fw', 1)):
        if b.startswith(pre):
            rest = b[len(pre):]
            m = re.match(r'(1[0-9]|[1-9])', rest)
            # for fwp2/fwm2 the trailing digit is the offset; for fwpw too
            return (fam, int(m.group(1)) if m else 0)
    return (0, 0)


def bound_str(core, landmark):
    nums = re.findall(r'(\d+)\^(\d+)', landmark or '')
    arg = int(nums[-1][1]) if nums else 0
    r, k = family_rank(core)
    if r == 6: return f'> f_{{ε₁}}({arg - 3})'
    if r == 5: return f'> f_{{ε₀}}({arg})'
    if r == 4: return f'> f_{{ω^ω+{k}}}({arg})' if k else f'> f_{{ω^ω}}({arg})'
    if r == 3: return f'> f_{{ω^2+{k}}}({arg})' if k else f'> f_{{ω^2}}({arg})'
    if r == 2: return f'> f_{{ω×2+{k}}}({arg})' if k else f'> f_{{ω×2}}({arg})'
    if r == 1: return f'> f_{{ω+{k}}}({arg})' if k else f'> f_{{ω}}({arg})'
    return f'> f_{{ω}}({arg})'


def keep(rec):
    if not rec.get('hit') or not rec.get('tnf'):
        return False
    if rec.get('states_used', -1) != rec['n']:
        return False
    try:
        n, m, tab = T.parse_tnf(rec['tnf'])
    except Exception:
        return False
    if (n, m) != (rec['n'], rec['m']):
        return False
    cfg = T.run(tab, T.INIT, rec['step'])
    if cfg is None or cfg[0] is None:
        return False
    if rec.get('landmark'):
        if not T.landmark_match(cfg, rec['landmark']):
            rec['landmark_mismatch'] = [str(cfg), rec['landmark']]
            return False
        rec['clean'] = T.landmark_clean(cfg, rec['landmark'])
    # irreducibility: every state and every symbol live
    seen, syms, c = set(), set(), T.INIT
    for _ in range(rec['step'] + 5000):
        if c[0] is None:
            break
        seen.add(c[0]); syms.add(c[2])
        c = T.step(tab, c)
        if c is None:
            return False
    if len(seen) != n or not set(range(m)) <= syms:
        return False
    # post-landmark must stay alive
    if T.run(tab, cfg, 5000) is None:
        return False
    rec['cfg'] = list(cfg)
    return True


def lean_tm(n, m, tab, name):
    out = [f'def {name} : TM']
    for s in range(n):
        for c in range(m):
            a = tab.get((s, c))
            if a is None:
                out.append(f'  | {s}, {c} => none')
            else:
                w, d, nx = a
                nxs = 'none' if nx is None else f'some {nx}'
                out.append(f'  | {s}, {c} => some ⟨{w}, Dir.{d}, {nxs}⟩')
    out.append('  | _, _ => none')
    return '\n'.join(out)


def lean_valid(n, m, tab, tmname):
    L = [f'theorem valid_{n}_{m} : ValidTM {n} {m} {tmname} := by', '  constructor']
    L.append('  · intro s sym hs hsym')
    L.append('    match s with')
    for s in range(n):
        defs = [c for c in range(m) if (s, c) in tab]
        und = [c for c in range(m) if (s, c) not in tab]
        L.append(f'    | {s} =>')
        L.append('      match sym with')
        if defs:
            for c in defs:
                w, d, nx = tab[(s, c)]
                second = 'trivial' if nx is None else 'by decide'
                L.append(f'      | {c} => exact ⟨by decide, {second}⟩')
        if und:
            pat = ' | '.join(str(c) for c in und)
            L.append(f'      | {pat} => trivial')
        L.append(f'      | _ + {m} => omega')
    L.append(f'    | _ + {n} => omega')
    L.append('  · intro s sym h')
    L.append('    match s with')
    for s in range(n):
        L.append(f'    | {s} =>')
        L.append('      match sym with')
        L.append('      | ' + ' | '.join(str(c) for c in range(m)) + ' => omega')
        L.append(f'      | _ + {m} => rfl')
    L.append(f'    | _ + {n} => rfl')
    return '\n'.join(L)


def lean_cfg(c):
    st, left, cur, right = c
    sts = 'none' if st is None else f'some {st}'
    return ('{ st := %s, left := [%s], cur := %s, right := [%s] }'
            % (sts, ', '.join(map(str, left)), cur, ', '.join(map(str, right))))


def lean_reaches(name, K, cfg, chunks, lm=None):
    lm = lm or (name[3:] if name.startswith('tm_') else name)
    L = [f'theorem reaches_landmark_{lm} : steps {name} {K} initConfig = some landmark_{lm} := by']
    prev = 'initConfig'
    prev_t = 0
    for i, (t, c) in enumerate(chunks):
        if i == 0:
            L.append(f'  have h0 : steps {name} {t} initConfig = some {lean_cfg(c)} := rfl')
            prev, prev_t = 'h0', t
        else:
            L.append(f'  have hstep{i} : steps {name} {t} {lean_cfg(chunks[i-1][1])} = some {lean_cfg(c)} := rfl')
            tot = prev_t + t
            L.append(f'  have h{i} : steps {name} {tot} initConfig = some {lean_cfg(c)} := '
                     f'steps_add {name} {prev_t} {t} initConfig _ _ {prev} hstep{i}')
            prev, prev_t = f'h{i}', tot
    L.append(f'  exact {prev}')
    return '\n'.join(L)


def emit_lean(entries):
    bys = {}
    for e in entries:
        bys.setdefault(e['m'], []).append(e)
    files = []
    for m in sorted(bys):
        L = ['/-', f'  BB/Champions2026_11_23_S{m}.lean',
             f'  Kernel-verified Lean 4 ValidTM + exact blank-tape landmark proofs for '
             f'{len(bys[m])} {m}-symbol champions.', '-/', 'import BB.TM', '',
             f'namespace BB.Champions2026_11_23.S{m}', 'open BB', '']
        for e in sorted(bys[m], key=lambda x: (x['n'], x['core'])):
            name = f"tm_{e['n']}_{m}"
            L.append(f"/-! ### BB({e['n']},{m}) — {e['bound']} (`{e['core']}` @ step {e['step']}) -/")
            L.append(lean_tm(e['n'], m, e['tab'], name))
            L.append('')
            L.append(lean_valid(e['n'], m, e['tab'], name))
            L.append('')
            L.append(f"def landmark_{e['n']}_{m} : Config := {lean_cfg(tuple(e['cfg']))}")
            if len(e['chunks']) > 90:
                L.append('set_option maxHeartbeats 800000 in')
            L.append(lean_reaches(name, e['step'], e['cfg'], e['chunks'], f"{e['n']}_{m}"))
            L.append('')
        L.append(f'end BB.Champions2026_11_23.S{m}')
        path = os.path.join(OUT, f'Champions2026_11_23_S{m}.lean')
        open(path, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
        files.append(path)
    root = ['import BB.TM'] + [f'import BB.Champions2026_11_23_S{m}' for m in sorted(bys)]
    open(os.path.join(OUT, 'Champions2026_11_23.lean'), 'w', encoding='utf-8').write('\n'.join(root) + '\n')
    return files


def rank_from_text(t):
    """Best ordinal rank mentioned in a proof header."""
    t = '\n'.join(l for l in t.splitlines() if not l.startswith('From '))
    best = (0, 0)

    def upd(r):
        nonlocal best
        if r > best:
            best = r

    if 'epsilon1' in t or 'ε₁' in t:
        upd((6, 0))
    if 'epsilon0' in t or 'ε₀' in t:
        upd((5, 0))
    m = re.search(r'Fwpw_(\d+)', t)
    if 'omega_pow_omega' in t or 'Fwpw' in t:
        upd((4, int(m.group(1)) if m else 0))
    m = re.search(r'Fwp2_(\d+)', t)
    if 'omega_pow' in t or 'Fwp2' in t:
        upd((3, int(m.group(1)) if m else 0))
    if 'omega_mul2' in t or 'Fwm2' in t:
        upd((2, 0))
    for m in re.finditer(r'f_omega_plus\s+(\d+)', t):
        upd((1, int(m.group(1))))
    if 'f_omega' in t or 'FGH' in t:
        upd((1, 0))
    return best


def load_prev():
    p = os.path.join(NC, 'champions_2026_11_21.json')
    prev = {}
    for x in json.load(open(p, encoding='utf-8')):
        core = x['core'].split()[0]
        prev[(x['states'], x['symbols'])] = {'core': core, 'rank': family_rank(core),
                                             'bound': x['bound'], 'step': x.get('step')}
    # the Rocq corpus already proves one champion per BB<n>_<m>.v cell
    rd = os.path.join(NC, 'rocq')
    for fn in os.listdir(rd):
        m = re.fullmatch(r'BB(\d+)_(\d+)\.v', fn)
        if not m:
            continue
        n, sym = int(m.group(1)), int(m.group(2))
        head = open(os.path.join(rd, fn), encoding='utf-8', errors='replace').read(6000)
        cm = re.search(r'Core:\s*(\w+)\s*@', head)
        rk = max(family_rank(cm.group(1)) if cm else (0, 0), rank_from_text(head))
        old = prev.get((n, sym))
        if old is None or rk > old['rank']:
            prev[(n, sym)] = {'core': f'rocq/{fn}', 'rank': rk,
                              'bound': old['bound'] if old else 'formal', 'step': None}
    return prev


def main():
    prev = load_prev()
    recs = []
    seen = set()
    for line in open(HITS, encoding='utf-8'):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        if not keep(r):
            continue
        if r['tnf'] in seen:
            continue
        seen.add(r['tnf'])
        n, m, tab = T.parse_tnf(r['tnf'])
        r['tab'] = tab
        r['bound'] = bound_str(r['core'], r.get('landmark'))
        r['chunks'] = T.chunk_configs(tab, r['step'])
        recs.append(r)

    # best per cell
    best = {}
    for r in recs:
        k = (r['n'], r['m'])
        if k not in best or family_rank(r['core']) > family_rank(best[k]['core']):
            best[k] = r
    alternates = []
    for k in list(best):
        r = best[k]
        if k in prev and prev[k]['rank'] >= family_rank(r['core']):
            alternates.append((r, prev[k]))
            del best[k]
    entries = [best[k] for k in sorted(best)]
    print(f'valid hits: {len(recs)}, new/upgraded cells: {len(entries)}, ')
    print(f'skipped (incumbent at least as strong): {len(alternates)}')
    for e in entries:
        print(f"  BB({e['n']:>2},{e['m']}) {e['core']:<14} step={e['step']:<6} {e['bound']}")

    out_json = []
    for e in entries:
        out_json.append({
            'states': e['n'], 'symbols': e['m'], 'core': e['core'],
            'bound': e['bound'], 'halted_at': e['step'],
            'landmark': T.fmt_landmark(tuple(e['cfg'])),
            'tnf': e['tnf'],
        })
    json.dump(out_json, open(os.path.join(OUT, 'champions_2026_11_23.json'), 'w', encoding='utf-8'),
              indent=1, ensure_ascii=False)
    files = emit_lean(entries)
    print('lean files:', [os.path.basename(f) for f in files])
    if alternates:
        json.dump([{'n': r['n'], 'm': r['m'], 'core': r['core'], 'step': r['step'],
                    'incumbent': p['core'], 'incumbent_bound': p['bound']}
                   for r, p in alternates],
                  open(os.path.join(OUT, 'alternates_2026_11_23.json'), 'w', encoding='utf-8'), indent=1)


if __name__ == '__main__':
    main()
