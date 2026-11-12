import math, re, os, functools

BASE = r"c:\Users\Rowan\Documents\st\bbwork\bb-variants\CET"

def carmichael_lambda(n):
    if n <= 1:
        return 1
    res = 1
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            pe = 1
            k = 0
            while temp % d == 0:
                temp //= d
                pe *= d
                k += 1
            if d == 2 and k >= 3:
                lam = pe // 4
            else:
                lam = (pe // d) * (d - 1)
            res = math.lcm(res, lam)
        d += 1
    if temp > 1:
        res = math.lcm(res, temp - 1)
    return res

def fit_formula(Ts, L0, bt):
    """
    Exact integer representation for T_s(L) at L >= L0:
    bt=1: base=2, period=1: Ts[i] = c0 * 2^(L-L0) + A*L + B (Wait: c0 = Ts[0] - A*L0 - B)
    bt=2: base=2, period=2: even/odd i separately with 4^k
    bt=3: base=3, period=1
    bt=4: base=3, period=2
    Returns dict {base, per, L0, branches: [(c0, A, B), ...]} or None
    """
    base = 2 if bt in (1, 2) else 3
    per = 1 if bt in (1, 3) else 2
    branches = []
    if per == 1:
        d = [Ts[i+1] - base * Ts[i] for i in range(4)]
        diff1 = d[1] - d[0]
        if any(d[i+1] - d[i] != diff1 for i in range(3)):
            return None
        if diff1 % (1 - base) != 0:
            return None
        A = diff1 // (1 - base)
        # d[0] = (1-base)*(A*L0 + B) + A  => (1-base)*B = d[0] - A - (1-base)*A*L0
        numB = d[0] - A - (1 - base) * A * L0
        if numB % (1 - base) != 0:
            return None
        B = numB // (1 - base)
        c0 = Ts[0] - A * L0 - B
        for i in range(6):
            val = c0 * (base ** i) + A * (L0 + i) + B
            if val != Ts[i]:
                return None
        branches.append((c0, A, B, L0))
    else:
        b2 = base * base
        for par in (0, 1):
            sub = [Ts[par], Ts[par+2], Ts[par+4]]
            Lp = L0 + par
            # sub[k] = c * (b2)^k + A*(Lp + 2k) + B
            d0 = sub[1] - b2 * sub[0]
            d1 = sub[2] - b2 * sub[1]
            diff = d1 - d0
            # diff = 2*(1-b2)*A
            if diff % (2 * (1 - b2)) != 0:
                return None
            A = diff // (2 * (1 - b2))
            # d0 = sub[1] - b2*sub[0] = 2*A + (1-b2)*(A*Lp + B)
            numB = d0 - 2 * A - (1 - b2) * A * Lp
            if numB % (1 - b2) != 0:
                return None
            B = numB // (1 - b2)
            c0 = sub[0] - A * Lp - B
            for k in range(3):
                val = c0 * (b2 ** k) + A * (Lp + 2 * k) + B
                if val != sub[k]:
                    return None
            branches.append((c0, A, B, Lp))
    return {"base": base, "per": per, "L0": L0, "branches": branches}

def eval_T_mod(formula, L_mod_Q, L_mod_phi, L_par, Q, base, is_big=True):
    """Return T_s(L) mod Q given exact residues of L."""
    per = formula["per"]
    br = formula["branches"][0] if per == 1 else formula["branches"][L_par]
    c0, A, B, Lp = br
    # c0 * base^(L - Lp) + A * L + B mod Q
    # Split Q = b_part * coprime_part
    b_part = 1
    cop = Q
    while cop % base == 0:
        cop //= base
        b_part *= base
    if is_big:
        # Since L >= 1000, base^(L - Lp) == 0 mod b_part!
        exp_cop = pow(base, (L_mod_phi - Lp) % carmichael_lambda(cop) if cop > 1 else 0, cop) if cop > 1 else 0
        if cop > 1 and b_part > 1:
            # CRT: 0 mod b_part, exp_cop mod cop
            inv = pow(b_part, -1, cop)
            exp_mod = (b_part * ((exp_cop * inv) % cop)) % Q
        elif cop > 1:
            exp_mod = exp_cop % Q
        else:
            exp_mod = 0
    else:
        # Exact small L_exact passed as L_mod_Q
        exp_mod = pow(base, L_mod_Q - Lp, Q)
    return (c0 * exp_mod + A * L_mod_Q + B) % Q

def parse_mech_line(line):
    parts = line.strip().split("\t")
    c_pair, e_spec = parts[0], parts[1]
    meta = {}
    events = {}
    r1_str = ""
    for p in parts[2:]:
        if p.startswith("|"):
            for tok in p.split("|"):
                if not tok:
                    continue
                if tok.startswith("H:"):
                    _, gs, stp = tok.split(":")
                    events[int(gs)] = ("H", int(stp))
                elif tok.startswith("B:"):
                    flds = tok.split(":")
                    g = int(flds[1])
                    kv = {}
                    for f in flds[2:]:
                        k, v = f.split("=")
                        kv[k] = v
                    Ts = [int(x) for x in kv["T"].split(",")]
                    form = fit_formula(Ts, int(kv["L0"]), int(kv["bt"]))
                    w3 = int(kv["w3"])
                    if form is None or w3 % 3 != 0:
                        return None
                    events[g] = ("B", {
                        "ts": int(kv["ts"]), "lp": int(kv["lp"]), "w": w3 // 3,
                        "L0": int(kv["L0"]), "xr": int(kv["xr"]), "gdx": int(kv["gdx"]),
                        "gs": int(kv["gs"]), "mna": int(kv["mna"]), "form": form
                    })
        elif p.startswith("R1="):
            r1_str = p
        elif "=" in p:
            k, v = p.split("=", 1)
            meta[k] = int(v)
    return {
        "pair": c_pair, "e_spec": e_spec,
        "P": meta["P"], "D": meta["D"], "M": meta["M"], "mg": meta["mg"],
        "bt": meta["bt"], "nH": meta["nH"], "nB": meta["nB"],
        "r1": r1_str, "events": events
    }

def trace_from_R1_COL1(m, max_rounds=16):
    # Parse R1=COL1:t=...:gap=...:x1=...:r2min=...:cz=1:...
    r1 = m["r1"]
    if not r1.startswith("R1=COL1:"):
        return None
    kv = {}
    for f in r1.split(":")[1:]:
        k, v = f.split("=")
        kv[k] = v
    if int(kv["cz"]) != 1:
        return None
    G1 = int(kv["gap"])
    if G1 not in m["events"]:
        return None
    ev1 = m["events"][G1]
    if ev1[0] == "H":
        return (1, [G1], float(kv["t"]), "R1 halt")
    b = ev1[1]
    # L_orig = (x1 - r2min) + mna
    L_orig_2 = int(kv["x1"]) - int(kv["r2min"]) + b["mna"]
    if L_orig_2 < b["L0"]:
        return None
    return trace_exact_from_collision(m, G1, L_orig_2, round_start=2, max_rounds=max_rounds)

def trace_exact_from_collision(m, G_start, L_orig_start, round_start=2, max_rounds=16):
    """
    Try halting depth R = round_start .. max_rounds by precomputing exact modulus chain!
    Wait: simpler! Compute backward modulus chain ONCE for depth K = max_rounds, then propagate L mod need_L[r] forward!
    """
    P, D, M, mg = m["P"], m["D"], m["M"], m["mg"]
    # Conservative modulus chain backwards from depth K:
    # Actually at each round we might pick ANY B event, so compute ONE unified backward chain assuming Q_K = P*M:
    # Let's check: does need_L[r] depend only on P, M, base?
    # Base can be 2 or 3; compute for max(carmichael) or simply propagate for depth K=12!
    # Wait: (P*M)^10 ~ 10^25 which can make carmichael_lambda slow to factor if big!
    # Instead: track exact BIG INT up to L <= 10^5, then track L mod (P^a * M^b) via lazy or exact step-by-step CRT?
    # NO! Think: for fixed K <= 8 rounds, Q grows by * (P*M); if P*M <= 500, Q_5 <= 500^5 = 3e13 (instant factoring!).
    # Wait: even simpler! To know round r+1 ONLY requires L_r mod M_eff, where we only factor P and M primes!!
    # Look! What primes can EVER appear in Q_0 = P * M and lambda(c_r)?
    # ONLY primes of P, M, and their totient ancestors!! Let's check factoring up to ~10^15 or using trial+Pollard?
    # Actually let's check rounds step-by-step for max_rounds = 10 starting with Q_final = P * M * 2 (fast!):
    # Wait: first run concretely if L_orig <= 5000 (Round 2): we can compute L_2 + T_2 as EXACT PYTHON INT!
    G = G_start
    ev = m["events"][G]
    if ev[0] == "H":
        return (round_start - 1, [G], 0, "halt")
    # Compute Round `round_start` (from collision G_start with exact L_orig_start <= 100000!) EXACTLY as Python int:
    b = ev[1]
    form = b["form"]
    base = form["base"]
    L_next = L_orig_start + b["xr"]
    if L_next < form["L0"]:
        return None
    if L_next > 300000:
        return None
    per = form["per"]
    br = form["branches"][0] if per == 1 else form["branches"][(L_next - form["L0"]) % 2]
    c0, A, B, Lp = br
    if per == 1:
        Ts_val = c0 * (base ** (L_next - Lp)) + A * L_next + B
    else:
        Ts_val = c0 * ((base * base) ** ((L_next - Lp) // 2)) + A * L_next + B
    T_round = b["ts"] + Ts_val + (L_orig_start + b["lp"] - 1) * b["w"]
    if T_round < b["gs"]:
        return None
    dt = T_round - b["gs"]
    q2 = dt % P
    N_rel = (G + b["gdx"] - b["xr"]) + (dt // P) * D + q2
    G_next = mg + ((N_rel - mg) % M)
    m_chase = (N_rel - G_next) // M
    if m_chase < 0:
        return None
    L_orig_3 = L_next + m_chase * P - q2
    if G_next not in m["events"]:
        return None
    if m["events"][G_next][0] == "H":
        return (round_start, [G, G_next], f"2^{L_next}", "HALT_R2")
    # Now L_orig_3 is STILL an EXACT Python int of <= ~100,000 bits (~30,000 digits, takes <1ms)!
    # Wait: from Round 3 -> 4 -> 5..., L_orig_3 has ~30,000 digits, so base ** L_orig_3 CANNOT be materialized,
    # BUT we CAN step modularly for ANY K target rounds!
    # Factor only primes of P, M up to K=7 cleanly using exact backward chain of length K (for K = 3..8):
    log10_approx = math.log10(base) * L_next if per == 1 else math.log10(base) * L_next
    # Trace exact up to K rounds by building backward modulus chain of length rem (fast: try K=8, 7, 6, ... or simply dynamic backward chain!):
    # Actually trace ONE exact chain of length rem=5 (up to Round 7!) FIRST — wait: why not factor via sympy? Check if sympy installed, else simple rho/sqrt!
    return (round_start, [G, G_next], L_next, L_orig_3)

def factor_small(n):
    res = {}
    d = 2
    while d * d <= n:
        if n % d == 0:
            c = 0
            while n % d == 0:
                n //= d; c += 1
            res[d] = c
        d += 1 if d == 2 else 2
    if n > 1:
        res[n] = 1
    return res

def trace_multiround_modular(m, G_start, L_orig_exact, round_idx, target_max_rounds=10):
    """Given exact integer L_orig_exact (for round `round_idx` after Round 2, so L_orig_exact ~ 10^10000),
       check rounds round_idx .. target_max_rounds cleanly using backward modulus table of length rem!"""
    P, D, M, mg = m["P"], m["D"], m["M"], m["mg"]
    # Wait: how large does need_L get? Suppose base in {2,3}, let's check modulus propagation on a 6-round horizon!
    # Actually we only need to compute ONE round further (`round_idx + 1`) cleanly?
    # No: to know Round r+1's G, we need N_rel mod M -> T mod (P*M) -> L_r mod lcm(P*M, lambda(P*M)).
    # To know Round r+2's G, we need L_{r+1} mod lcm(P*M, lam) -> T_r mod (P*M*lcm) -> ...
    # Factoring gets tricky past 10^14 UNLESS we use Pollard rho! Let's include 25-line Pollard rho in Python so factoring up to 10^30 takes < 1ms!
    pass

# Simple deterministic/Miller-Rabin + Pollard Rho for up to 128-bit integers:
import random
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17):
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1: break
        else: return False
    return True

def pollard_rho(n):
    if n % 2 == 0: return 2
    while True:
        c = random.randrange(1, n)
        x = random.randrange(2, n)
        y, d = x, 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n: return d

def factor_big(n, out=None):
    if out is None: out = {}
    if n <= 1: return out
    if n < 10**9:
        for k, v in factor_small(n).items():
            out[k] = out.get(k, 0) + v
        return out
    if is_prime(n):
        out[n] = out.get(n, 0) + 1
        return out
    d = pollard_rho(n)
    factor_big(d, out)
    factor_big(n // d, out)
    return out

@functools.lru_cache(maxsize=None)
def lambda_big(n):
    if n <= 1: return 1
    f = factor_big(n)
    res = 1
    for p, k in f.items():
        if p == 2 and k >= 3:
            lam = (p ** (k - 2))
        else:
            lam = (p ** (k - 1)) * (p - 1)
        res = math.lcm(res, lam)
    return res

@functools.lru_cache(maxsize=None)
def get_mod_chain(P, M, base, K):
    need_L = [1] * K
    mod_T = [0] * K
    mod_T[K - 1] = P * M
    for d in range(K - 1, -1, -1):
        mt = mod_T[d]
        cop = mt
        while cop % base == 0:
            cop //= base
        lam = lambda_big(cop) if cop > 1 else 1
        need_L[d] = math.lcm(mt, lam, 2)
        if d > 0:
            mod_T[d - 1] = P * M * need_L[d]
    return tuple(need_L), tuple(mod_T)

def exact_tower_rounds(m, G_start, L_orig_exact, round_start=3, max_depth=8):
    P, D, M, mg = m["P"], m["D"], m["M"], m["mg"]
    base = 2 if m["bt"] in (1, 2) else 3

    def run_for_K(K):
        need_L, mod_T = get_mod_chain(P, M, base, K)
        # Now trace forward using exact L_orig_exact mod need_L[0]!
        G = G_start
        L_mod = L_orig_exact % need_L[0]
        seq = [G]
        for d in range(K):
            ev = m["events"].get(G)
            if ev is None: return ("UNKNOWN", seq, d)
            if ev[0] == "H": return ("HALT", seq, d)
            b = ev[1]
            form = b["form"]
            xr = b["xr"]
            L_next_mod = (L_mod + xr) % need_L[d]
            L_par = (L_next_mod - form["L0"]) % 2
            mt = mod_T[d]
            # Evaluate Ts(L_next) mod mt
            br = form["branches"][0] if form["per"] == 1 else form["branches"][L_par]
            c0, A, B, Lp = br
            cop = mt; bp = 1
            while cop % base == 0: cop //= base; bp *= base
            lam_cop = lambda_big(cop) if cop > 1 else 1
            if cop > 1:
                exp_cop = pow(base, (L_next_mod - Lp) % lam_cop, cop)
                if bp > 1:
                    inv = pow(bp, -1, cop)
                    exp_mod = (bp * ((exp_cop * inv) % cop)) % mt
                else:
                    exp_mod = exp_cop % mt
            else:
                exp_mod = 0
            Ts_mod = (c0 * exp_mod + A * L_next_mod + B) % mt
            T_round_mod = (b["ts"] + Ts_mod + (L_mod + b["lp"] - 1) * b["w"]) % mt
            dt = (T_round_mod - b["gs"]) % mt
            q2 = dt % P
            # N_rel mod (mt // P) = mod_T[d] // P = M * need_L[d+1] (or M for d == K-1)
            m_div_P = mt // P
            N_rel_mod = (G + b["gdx"] - xr + (dt // P) * D + q2) % m_div_P
            G_next = mg + ((N_rel_mod - mg) % M)
            if d == K - 1:
                evn = m["events"].get(G_next)
                if evn and evn[0] == "H":
                    return ("HALT", seq + [G_next], d + 1)
                return ("ALIVE", seq + [G_next], d + 1)
            # Compute L_{d+1} mod need_L[d+1]!
            m_chase_mod = ((N_rel_mod - G_next) // M) % need_L[d + 1]
            L_next_for_next = (L_mod + xr) % need_L[d + 1]
            L_mod = (L_next_for_next + m_chase_mod * P - q2) % need_L[d + 1]
            G = G_next
            seq.append(G)
        return ("ALIVE", seq, K)

    res = run_for_K(max_depth)
    return res

def process_file(fname, label):
    path = os.path.join(BASE, fname)
    total = 0; r1_col1 = 0
    best = []
    alive_deep = []
    with open(path) as f:
        for line in f:
            total += 1
            m = parse_mech_line(line)
            if not m: continue
            r1 = m["r1"]
            if not r1.startswith("R1=COL1:"):
                continue
            r1_col1 += 1
            t2 = trace_from_R1_COL1(m)
            if t2 is None: continue
            if len(t2) == 4 and isinstance(t2[3], str): # HALT at R=1 or R=2
                r_end, seq, lnext, _ = t2
                if r_end >= 2:
                    best.append((r_end, str(lnext), seq, m))
                continue
            # r2 bounced into R=3 with exact L_orig_3!
            _, seq2, L_next_2, L_orig_3 = t2
            # Run exact modular up to K=6 first (Rounds 3..8!)
            status, seq3, depth = exact_tower_rounds(m, seq2[-1], L_orig_3, round_start=3, max_depth=6)
            if status == "HALT":
                total_R = 2 + depth
                best.append((total_R, f"{m['bt']}:L2={L_next_2}", seq2 + seq3[1:], m))
            elif status == "ALIVE":
                # Try K=10!
                status2, seq4, d2 = exact_tower_rounds(m, seq2[-1], L_orig_3, round_start=3, max_depth=10)
                if status2 == "HALT":
                    best.append((2 + d2, f"{m['bt']}:L2={L_next_2}", seq2 + seq4[1:], m))
                elif status2 == "ALIVE":
                    alive_deep.append((L_next_2, seq2 + seq4[1:], m))
    print(f"=== {label}: total_mechs={total}, R1=COL1={r1_col1}, halting(R>=2)={len(best)}, alive>=12R={len(alive_deep)} ===")
    best.sort(key=lambda x: (-x[0], -x[3]["M"]))
    for r_cnt, desc, seq, m in best[:15]:
        print(f"  ROUNDS={r_cnt} M={m['M']}(P={m['P']},D={m['D']}) bt={m['bt']} {desc} | gaps={seq} | {m['pair']} | {m['r1']}")
    for L2, seq, m in alive_deep[:5]:
        print(f"  [ALIVE >=12R] M={m['M']}(P={m['P']},D={m['D']}) bt={m['bt']} L2={L2} | gaps={seq} | {m['pair']}")

process_file("mechs_cet3.txt", "CET(3)")
process_file("mechs_cet23_t1.txt", "CET(2,3) t1")
process_file("mechs_cet23_t2.txt", "CET(2,3) t2")
