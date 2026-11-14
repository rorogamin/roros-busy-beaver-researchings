"""Token parsing/printing helpers (importable; no side effects)."""

def parse(w):
    """Parse a tape word into tokens U(a,b) = 0 4^a 2^b and V(c) = 4 3 2^c."""
    i = 0; out = []
    while i < len(w):
        if w[i] == '0':
            j = i+1; a = 0
            while j < len(w) and w[j] == '4': a += 1; j += 1
            b = 0
            while j < len(w) and w[j] == '2': b += 1; j += 1
            out.append(('U', a, b)); i = j
        elif w[i:i+2] == '43':
            j = i+2; c = 0
            while j < len(w) and w[j] == '2': c += 1; j += 1
            out.append(('V', c)); i = j
        else:
            out.append(('?', w[i])); i += 1
    return out

def word(toks):
    s = ''
    for t in toks:
        if t[0] == 'U': s += '0' + '4'*t[1] + '2'*t[2]
        elif t[0] == 'V': s += '43' + '2'*t[1]
        else: s += t[1]
    return s

def name(t):
    if t[0] == 'U': return 'u' if t[1:] == (1, 1) else 'U%d,%d' % (t[1], t[2])
    if t[0] == 'V': return 'V%d' % t[1]
    return '?' + str(t[1])

def fmt(toks):
    s = [name(t) for t in toks]
    out = []; i = 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        out.append(s[i] if j-i == 1 else '%s^%d' % (s[i], j-i)); i = j
    return ' '.join(out)
