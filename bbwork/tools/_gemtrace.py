import sys
sys.path.insert(0, '.')
import sys; sys.path.insert(0, "tools")
from verify_epsilon1_tm import step_ordinal_term

def val(w):
    # O(w) per their section 5: eps_0 = e, (X) = omega^O(X), concat = sum
    def p(tokens):
        if not tokens: return 0
        t, rest = tokens[0], tokens[1:]
        if t == 'e': return 1 << 20  # eps0 as a huge symbolic value marker
        if t == 'o':
            depth = 0; j = 0
            for j, u in enumerate(rest):
                if u == 'o': depth += 1
                elif u == 'c':
                    if depth == 0: return None
                    depth -= 1
                    if depth == 0:
                        inner = p(rest[:j+1])
                        if inner is None: return None
                        return (inner * (1 << 20 if False else 1)) if False else None or None
        return None
    # proper parser: return list of top-level components
    def parse(tokens):
        out = []; stack = []; cur = []
        for t in tokens:
            if t == 'o':
                stack.append(cur); cur = []
            elif t == 'c':
                if not stack: return None
                inner = cur; cur = stack.pop()
                cur.append(('w', inner))
            else:
                cur.append(('e',))
        if stack: return None
        return cur
    def ev(nodes):
        tot = []
        for nm, arg in nodes:
            if nm == 'e': tot.append(1)          # eps0 -> symbolic 1 (not comparable numerically)
            else: tot.append(('exp', ev(arg)))
        return tot
    p2 = parse(w)
    if p2 is None: return None
    return ev(p2)

def show(v):
    # render exponent tower chain: exp(x) renders as w^(...)
    if isinstance(v, list):
        return "+".join(show(x) for x in v)
    nm, arg = v
    if nm == 'e': return "e"
    return "w^(" + show(arg) + ")"

cases = [
    ("oo cc (omega)", "oocc", 3),
    ("o o c", "oocc", 3),
    ("((())) = w^w", "oooccc", 3),
    ("w^4-ish 'o oc oc oc oc c'", "ooococochoc".replace("m","o"), 3),
    ("'o'+oc*7", "o" + "oc"*7, 4),
    ("e", "e", 3),
    ("(e) = w^e0", "oec", 2),
    ("oooeocccc = eps1[3]", "oooeocccc", 3),
]
for label, w, n in cases:
    print("=== ", label, " n=", n)
    print("   value:", show(val(list(w))))
    for k in range(6):
        w2, n2 = step_ordinal_term(list(w), n)
        if w2 is None:
            print("   step", k, "-> None (halt-ish?) n->", n)
            break
        print("   step", k, "|n:", n, "->", n2, "| len:", len(w), "->", len(w2), "|", "".join(w2))
        print("        value: ", show(val(w2)))
        w, n = w2, n2
