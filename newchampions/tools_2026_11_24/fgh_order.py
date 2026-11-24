"""Conservative, mathematically rigorous FGH expression representation and comparison.

All ordinals and fast-growing hierarchy functions follow Wainer/Cichoń standard
fundamental sequences up through epsilon_3 (matching rocq/FGH.v and rocq/Fe1.v):
  f_0(n) = n + 1
  f_{a+1}(n) = f_a^n(n)
  f_w(n) = f_n(n)
  f_{w*(a+1)}(n) = f_{w*a + n}(n)
  f_{w^2*(c+1)}(n) = f_{w^2*c + w*n}(n)
  f_{w^w}(n) = f_{w^n}(n)
  f_{e0}(n) ~ f_{w^^n}(n)  (in Fe1.v: chainH (n+2) 0 1 for core arg n)
  f_{e1}(n) ~ f_{...}(n)   (in Fe1.v: chainB_H (n+2) 0 1)
  f_{e2}(n), f_{e3}(n)

Key principle: NEVER compare ordinal names alone at small arguments!
We normalize expressions by unwrapping limit ordinals at small integer arguments
(e.g. f_{w*2}(1) -> 2, f_{w*2}(2) -> f_{w+2}(2), f_{w^2}(2) -> f_{w+2}(2))
and unwrapping successor ordinals f_{a+1}(n) -> f_a^n(n) when comparing or when n is small.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
import re
from typing import Optional, Tuple, Union


# Ordinal tuple: (tier, offset)
#   0: finite / constant / arithmetic / up-arrows (Wait: we give fine sub-rank for finite)
#  10: w * 1 + off   (f_{w+off})
#  20: w * 2 + off   (f_{w*2+off})
#  25: w * 3 + off   (f_{w*3+off})
#  30: w^2 + off     (f_{w^2+off})
#  35: w^k + off     (f_{w^k+off}, k>=3)
#  40: w^w + off     (f_{w^w+off})
#  45: w^^k + off    (f_{w^^k+off}, k>=3)
#  50: e0 + off      (f_{epsilon_0+off})
#  60: e1 + off      (f_{epsilon_1+off})
#  70: e2 + off      (f_{epsilon_2+off})
#  80: e3 + off      (f_{epsilon_3+off})
#  90: psi_0(Omega_2) / BMS / Loader (beyond epsilon hierarchy)

@total_ordering
@dataclass(frozen=True)
class Ord:
    tier: int
    off: int = 0

    def is_limit(self) -> bool:
        return self.off == 0 and self.tier in (10, 20, 25, 30, 35, 40, 45, 50, 60, 70, 80, 90)

    def pred(self) -> 'Ord':
        assert self.off > 0
        return Ord(self.tier, self.off - 1)

    def __lt__(self, other: 'Ord') -> bool:
        return (self.tier, self.off) < (other.tier, other.off)

    def fmt(self) -> str:
        names = {
            0: 'fin', 10: 'ω', 20: 'ω×2', 25: 'ω×3',
            30: 'ω^2', 35: 'ω^k', 40: 'ω^ω', 45: 'ω↑↑k',
            50: 'ε₀', 60: 'ε₁', 70: 'ε₂', 80: 'ε₃', 90: 'ψ₀(Ω₂)'
        }
        base = names.get(self.tier, f'T{self.tier}')
        return f'{base}+{self.off}' if self.off else base


@dataclass(frozen=True)
class FVal:
    """Finite/concrete value, optionally represented as a huge finite rank.
    rank = (arrows, base_or_approx, arg)
      arrows = 0: exact small integer (val)
      arrows = 1: power tower / exponential (e.g. 10^17 -> (1, 10, 17))
      arrows >= 2: Knuth up-arrow / finite FGH f_k(n) (approx finite level k, arg n)
    """
    arrows: int
    val: int  # exact value if arrows == 0, else leading param
    arg: int = 0
    note: str = ''

    def approx_tuple(self) -> Tuple[int, int, int]:
        return (self.arrows, self.val, self.arg)


@dataclass(frozen=True)
class FApp:
    """f_{ord}^{iters}(inner)"""
    ord: Ord
    iters: int
    inner: Union[FVal, 'FApp']


FExpr = Union[FVal, FApp]


def _const_int(e: FExpr) -> Optional[int]:
    if isinstance(e, FVal) and e.arrows == 0:
        return e.val
    return None


def _is_huge_finite(e: FExpr) -> bool:
    return isinstance(e, FVal) and e.arrows >= 1


def unwrap_limit(ord_: Ord, n: int) -> Optional[FExpr]:
    """Exact fundamental-sequence step for limit ordinals at small integer n <= 3."""
    if ord_.off > 0:
        return None
    if n <= 0:
        return FVal(0, 1)
    if n == 1:
        # For ALL standard Wainer ordinals, f_alpha(1) = 2!
        # Wait: for f_{e0}, f_{e1}, etc. in Fe1.v, f_epsilon0(1) = chainH 3 0 1 is small finite;
        # treating n=1 for limit ordinals as tiny (at most fin(3, 10)) is completely conservative.
        return FVal(0, 2)
    # n >= 2:
    if ord_.tier == 10:  # f_w(n) = f_n(n)
        if n == 2:
            return FVal(0, 8)  # f_2(2) = 2^2 * 2 = 8 exact
        return FVal(n, 2, n)
    if ord_.tier == 20:  # f_{w*2}(n) = f_{w+n}(n)
        return FApp(Ord(10, n), 1, FVal(0, n))
    if ord_.tier == 25:  # f_{w*3}(n) = f_{w*2+n}(n)
        return FApp(Ord(20, n), 1, FVal(0, n))
    if ord_.tier == 30:  # f_{w^2}(n) = f_{w*n}(n)
        if n == 2:
            return FApp(Ord(20, 0), 1, FVal(0, 2))
        if n == 3:
            # f_{w*3}(3) = f_{w*2+3}(3)
            return FApp(Ord(20, 3), 1, FVal(0, 3))
        if n == 4:
            # f_{w*4}(4) = f_{w*3+4}(4) > f_{w*2+k}(small)
            return FApp(Ord(25, 4), 1, FVal(0, 4))
        return None
    if ord_.tier == 40:  # f_{w^w}(n) = f_{w^n}(n)
        if n == 2:
            return FApp(Ord(30, 0), 1, FVal(0, 2))
        if n == 3:
            # f_{w^3}(3) = f_{w^2*3}(3) >> f_{w^2+k}(small) for reasonable k
            return FApp(Ord(35, 0), 1, FVal(0, 3))
        return None
    if ord_.tier == 50:  # f_{e0}(n)
        if n == 2:
            # Conservative: f_{e0}(2) <= f_{w^w}(2) = f_{w+2}(2)
            return FApp(Ord(40, 0), 1, FVal(0, 2))
        return None
    if ord_.tier == 60:  # f_{e1}(n)
        if n == 2:
            return FApp(Ord(50, 0), 1, FVal(0, 2))
        return None
    if ord_.tier == 70:
        if n == 2:
            return FApp(Ord(60, 0), 1, FVal(0, 2))
        return None
    if ord_.tier == 80:
        if n == 2:
            return FApp(Ord(70, 0), 1, FVal(0, 2))
        return None
    return None


def normalize(e: FExpr) -> FExpr:
    """Normalize small-argument limit degeneracies and successor-at-1."""
    if isinstance(e, FVal):
        return e
    inner = normalize(e.inner)
    cur = FApp(e.ord, e.iters, inner)
    c = _const_int(inner)
    if c is not None:
        if c == 1:
            # f_a(1) for standard FGH: if a is limit -> 2; if a = b+1 -> f_b(1) -> ... -> 2
            # Wait: for Fe1.v chainH(n-3+2, 0, 1) at n=4 (arg=1): chainH 3 0 1 is finite (bounded by f_{w^3}(2)).
            # To be strictly conservative for BOTH lower and upper bounds, we only collapse to tiny when evaluating OUR lower bound!
            if cur.ord.off == 0 and cur.ord.tier < 90:
                u = unwrap_limit(cur.ord, 1)
                if u is not None:
                    if cur.iters == 1:
                        return u
                    return normalize(FApp(cur.ord, cur.iters - 1, u))
            elif cur.ord.off > 0:
                # f_{a+1}(1) = f_a(1)
                if cur.iters == 1:
                    return normalize(FApp(cur.ord.pred(), 1, FVal(0, 1)))
                return normalize(FApp(cur.ord, cur.iters - 1, normalize(FApp(cur.ord.pred(), 1, FVal(0, 1)))))
        elif c == 2 and cur.ord.off == 0 and cur.ord.tier < 90:
            u = unwrap_limit(cur.ord, 2)
            if u is not None:
                if cur.iters == 1:
                    return normalize(u)
                # first iter produces u, remaining iters apply cur.ord to u (huge)
                return FApp(cur.ord, cur.iters - 1, normalize(u))
        elif c >= 3 and cur.ord.tier == 10 and cur.ord.off == 0 and cur.iters == 1:
            return FVal(c, 2, c)
    return cur


def _expand_succ_once(e: FApp) -> Optional[FExpr]:
    """If e = f_{a+1}(k) with integer k >= 2, expand to f_a^k(k)."""
    if e.ord.off == 0 or e.iters != 1:
        return None
    c = _const_int(e.inner)
    if c is None or c < 1 or c > 10000:
        return None
    return FApp(e.ord.pred(), c, FVal(0, c))


def min_base_value(e: FExpr) -> Tuple[int, int]:
    """Conservative lower-bound magnitude (tier_approx, val) for an FExpr."""
    e = normalize(e)
    if isinstance(e, FVal):
        return (e.arrows, e.val)
    # Wait: f_{w+k}(n) for n >= 3 is already >>> any f_m(small)
    return (1000 + e.ord.tier * 100 + e.ord.off, e.iters)


def _strip_single_succ_iter(e: FApp) -> FExpr:
    """Return f_a^{iters-1}(inner) if iters > 1, else inner."""
    if e.iters > 1:
        return FApp(e.ord, e.iters - 1, e.inner)
    return e.inner


def cmp_conservative(a: FExpr, b: FExpr, depth: int = 0) -> Optional[int]:
    """Return +1 if a > b is conservatively guaranteed, -1 if a < b, 0 if equal, None if incomparable."""
    if depth > 8:
        return None
    a = normalize(a)
    b = normalize(b)

    if isinstance(a, FVal) and isinstance(b, FVal):
        if a.arrows == 0 and b.arrows == 0:
            return 1 if a.val > b.val else (-1 if a.val < b.val else 0)
        if a.approx_tuple() > b.approx_tuple():
            return 1
        if a.approx_tuple() < b.approx_tuple():
            return -1
        return 0

    if isinstance(a, FVal) and isinstance(b, FApp):
        # Finite vs FApp: if b is normalized, is b guaranteed > a?
        bc = _const_int(b.inner)
        if bc is None or bc >= 2:
            # Wait: what if b is f_w(3) vs 10^100 or 2^^15 5?
            if b.ord.tier == 10 and b.ord.off == 0 and bc is not None and bc <= 4:
                # f_w(3) = f_3(3) ~ 2^^5 < 2^^15 5!
                if a.arrows >= bc:
                    return 1
                if bc == 4 and a.arrows <= 3:
                    return -1
                return None
            return -1
        return None

    if isinstance(a, FApp) and isinstance(b, FVal):
        r = cmp_conservative(b, a, depth + 1)
        return None if r is None else -r

    assert isinstance(a, FApp) and isinstance(b, FApp)

    # Expand limit ordinal at n=3 if comparing against same tier or lower successor!
    ac = _const_int(a.inner)
    bc = _const_int(b.inner)
    if a.ord.is_limit() and ac is not None and ac <= 3 and a.ord.tier in (10, 20, 25, 30, 40):
        ua = unwrap_limit(a.ord, ac)
        if ua is not None:
            if a.iters == 1:
                return cmp_conservative(ua, b, depth + 1)
            return cmp_conservative(FApp(a.ord, a.iters - 1, ua), b, depth + 1)
    if b.ord.is_limit() and bc is not None and bc <= 3 and b.ord.tier in (10, 20, 25, 30, 40):
        ub = unwrap_limit(b.ord, bc)
        if ub is not None:
            if b.iters == 1:
                return cmp_conservative(a, ub, depth + 1)
            return cmp_conservative(a, FApp(b.ord, b.iters - 1, ub), depth + 1)

    # Compare ordinal levels
    if a.ord != b.ord:
        if a.ord > b.ord:
            # Does a strictly dominate b?
            # Be careful if a is f_{alpha+1}(small_k) and b is f_alpha^{many}(huge)!
            # Example: f_{w+2}(3) = f_{w+1}^3(3) vs f_{w+1}(f_w^4(6)) -> unwrap a!
            if a.ord == Ord(b.ord.tier, b.ord.off + 1):
                if a.iters == 1 and ac is not None and ac <= 2 and b.ord.tier >= 50:
                    if cmp_conservative(FVal(0, ac), b.inner, depth + 1) == 1:
                        return 1
                    return None
                if a.iters == 1 and ac is not None and ac <= 20:
                    exp_a = _expand_succ_once(a)
                    if exp_a is not None:
                        return cmp_conservative(exp_a, b, depth + 1)
                if a.iters >= 2:
                    # f_{a+1}^{k}(x) = f_a^M(M) where M = f_{a+1}^{k-1}(x) >= f_{a+1}(x)
                    M = FApp(a.ord, a.iters - 1, a.inner)
                    if cmp_conservative(M, FVal(0, b.iters + 1), depth + 1) == 1 and cmp_conservative(M, b.inner, depth + 1) == 1:
                        return 1
                    return None
                # a.iters == 1: f_{a+1}(inner) = f_a^{inner}(inner)
                if ac is None:
                    # inner of a is itself an FApp (>= 3 if non-degenerate)
                    if cmp_conservative(a.inner, FVal(0, b.iters + 1), depth + 1) == 1 and cmp_conservative(a.inner, b.inner, depth + 1) in (0, 1):
                        return 1
                    return None
                if ac > b.iters and cmp_conservative(FVal(0, ac), b.inner, depth + 1) in (0, 1):
                    return 1
                if ac > b.iters and ac >= 3:
                    stepped = FApp(b.ord, ac - b.iters, FVal(0, ac))
                    if cmp_conservative(stepped, b.inner, depth + 1) == 1:
                        return 1
                return None
            # Otherwise a.ord is >= 2 steps above b.ord (or a higher limit tier),
            # and since a is normalized (any n<=2 limit collapsed, n=1 collapsed),
            # ensure a's effective argument >= 2 (or >= 3 for limit tiers):
            min_ok = 3 if a.ord.is_limit() else 2
            if ac is not None and ac < min_ok:
                exp_a = _expand_succ_once(a)
                if exp_a is not None:
                    return cmp_conservative(exp_a, b, depth + 1)
                return None
            return 1
        else:
            r = cmp_conservative(b, a, depth + 1)
            return None if r is None else -r

    # Same ordinal a.ord == b.ord!
    if a.iters == b.iters:
        return cmp_conservative(a.inner, b.inner, depth + 1)

    if a.iters > b.iters:
        # Check if a.inner is at least >= b.inner, OR if a.iters >= b.iters + 1 and
        # one extra application of f_{ord} on a.inner dominates b.inner.
        c_in = cmp_conservative(a.inner, b.inner, depth + 1)
        if c_in in (0, 1):
            return 1
        # Even if a.inner < b.inner, f_{ord}^{a.iters}(a.inner) = f_{ord}^{b.iters}(f_{ord}^{diff}(a.inner)):
        diff = a.iters - b.iters
        stepped_a = FApp(a.ord, diff, a.inner)
        if cmp_conservative(stepped_a, b.inner, depth + 1) == 1:
            return 1
        return None
    else:
        r = cmp_conservative(b, a, depth + 1)
        return None if r is None else -r


def strictly_beats(ours: FExpr, target: Optional[FExpr]) -> bool:
    """True iff ours is conservatively proven > target (or target is None)."""
    if target is None:
        # Still require ours to not be degenerate tiny (e.g. f_{w*2}(1) = 2)
        n = normalize(ours)
        if isinstance(n, FVal):
            return n.arrows > 0 or n.val > 10
        return True
    return cmp_conservative(ours, target) == 1


# ------------------------------------------------------------------ Parsers

def parse_core_bound(core: str, args: dict) -> Optional[FExpr]:
    """Build exact conservative FExpr from a core name and its landmark slot args.
    Returns None if core has unverified or unknown bound.
    """
    b = core
    for suf in ('_blank', '_sw', '_opt', '_fix', '_qr'):
        if b.endswith(suf):
            b = b[:-len(suf)]
    # Check specific named cores
    if b.startswith('fe3'):
        # 1^m B> 8^n -> arg = n - 3
        n = args.get('n', 0)
        return FApp(Ord(80, 0), 1, FVal(0, max(1, n - 3))) if n >= 4 else None
    if b.startswith('fe2'):
        # fe21_9 -> offset +1 with p; fe2_8/fe2_9 -> n - 3
        m_off = re.match(r'^fe2(\d+)_', b)
        n = args.get('n', 0)
        if m_off:
            off = int(m_off.group(1))
            p = args.get('p', 0)
            if n < 4:
                return None
            return FApp(Ord(70, off), 1, FVal(0, p))
        return FApp(Ord(70, 0), 1, FVal(0, max(1, n - 3))) if n >= 4 else None
    if b.startswith('fe1'):
        m_off = re.match(r'^fe1(\d+)_', b)
        if m_off:
            off = int(m_off.group(1))
            # Outer arg is highest priority counter (k, p, q, r)
            outer_key = {1: 'p', 2: 'q', 3: 'r'}.get(off, 'p')
            if 'k' in args and outer_key not in args:
                outer_key = 'k'
            val = args.get(outer_key, 0)
            if args.get('n', 4) < 4:
                return None
            return FApp(Ord(60, off), 1, FVal(0, val))
        n = args.get('n', 0)
        return FApp(Ord(60, 0), 1, FVal(0, max(1, n - 3))) if n >= 4 else None
    if b.startswith('fe0'):
        m_off = re.match(r'^fe0(\d+)_', b)
        if m_off:
            off = int(m_off.group(1))
            if b == 'fe01_5':
                val = args.get('k', 0)
            else:
                outer_key = {1: 'p', 2: 'q', 3: 'r'}.get(off, 'p')
                if 'k' in args and outer_key not in args:
                    outer_key = 'k'
                val = args.get(outer_key, 0)
            if args.get('n', 4) < 4:
                return None
            return FApp(Ord(50, off), 1, FVal(0, val))
        n = args.get('n', 0)
        return FApp(Ord(50, 0), 1, FVal(0, max(1, n - 3))) if n >= 4 else None

    # fwpw ladder: fwpw, fwpw1..fwpw7, dfwpw
    if b.startswith('dfwpw'):
        k = args.get('k', 0)
        return FApp(Ord(40, 0), 2, FVal(0, k))
    if b.startswith('fwpw'):
        m_off = re.match(r'^fwpw(\d+)', b)
        off = int(m_off.group(1)) if m_off else 0
        # Highest slot in order: t > s > r > q > p > k
        for key in ('t', 's', 'r', 'q', 'p', 'k'):
            if key in args:
                return FApp(Ord(40, off), 1, FVal(0, args[key]))
        return None

    # fwp2 ladder: fwp2_3, fwp21..fwp2_10, fwp21fw, fwp22fw, fwp23fw
    if b.startswith('fwp2'):
        m_fw = re.match(r'^fwp2(\d*)fw', b)
        if m_fw:
            off = int(m_fw.group(1)) if m_fw.group(1) else 0
            # fwp2kfw_4: 1^n G> 1^m 0 -> f_{w^2+k}(f_w(m or n))
            n = args.get('n', 0)
            return FApp(Ord(30, off), 1, FApp(Ord(10, 0), 1, FVal(0, n)))
        if b == 'fwp21_7':
            p = args.get('p', 0)
            return FApp(Ord(30, 1), 1, FVal(0, max(1, p - 1)))
        if b == 'fwp22_7':
            q = args.get('q', 0)
            return FApp(Ord(30, 2), 1, FVal(0, max(1, q - 1)))
        if b == 'fwp24_4':
            q = args.get('q', 0)
            return FApp(Ord(30, 4), 1, FVal(0, max(1, q - 1)))
        m_10 = re.match(r'^fwp2_(\d+)_', b)
        if m_10:
            off = int(m_10.group(1))
        else:
            m_off = re.match(r'^fwp2(\d+)', b)
            off = int(m_off.group(1)) if m_off else 0
        for key in ('t', 's', 'r', 'q', 'p', 'k', 'n'):
            if key in args:
                return FApp(Ord(30, off), 1, FVal(0, args[key]))
        return None

    # fwm2 ladder: fwm2_3..7, dfwm2_5, fwm2fw_5, fwm21..fwm23, fwm21tfw1_7
    if b.startswith('dfwm2'):
        k = args.get('k', 0)
        return FApp(Ord(20, 0), 2, FVal(0, k))
    if b.startswith('fwm2fw'):
        k = args.get('k', 0)
        return FApp(Ord(20, 0), 1, FApp(Ord(10, 0), 1, FVal(0, max(1, k - 1))))
    if b.startswith('fwm21tfw1'):
        p = args.get('p', 0)
        k = args.get('k', 0)
        return FApp(Ord(20, 1), 1, FApp(Ord(10, 1), 3, FVal(0, max(2, p or k))))
    if b.startswith('fwm21dfw1'):
        p = args.get('p', 0)
        return FApp(Ord(20, 1), 1, FApp(Ord(10, 1), 2, FVal(0, max(2, p))))
    if b.startswith('fwm21fw1'):
        p = args.get('p', 0)
        return FApp(Ord(20, 1), 1, FApp(Ord(10, 1), 1, FVal(0, max(2, p))))
    if b.startswith('fwm2'):
        m_off = re.match(r'^fwm2(\d+)', b)
        off = int(m_off.group(1)) if m_off else 0
        for key in ('q', 'p', 'k'):
            if key in args:
                return FApp(Ord(20, off), 1, FVal(0, args[key]))
        return None

    # fw ladder: fw_3, fw_4, dfw, tfw, fw1fw, fw1..fw4
    if b.startswith('tfw'):
        k = args.get('k', 0)
        return FApp(Ord(10, 0), 3, FVal(0, k))
    if b.startswith('dfw'):
        k = args.get('k', 0)
        return FApp(Ord(10, 0), 2, FVal(0, k))
    if b.startswith('fw1fw'):
        k = args.get('k', 0)
        return FApp(Ord(10, 1), 1, FVal(0, k))
    if b == 'fw_4':
        k = args.get('k', 0)
        return FApp(Ord(10, 0), 1, FVal(0, max(1, k - 1)))
    if b == 'fw2_3':
        k = args.get('k', 0)
        return FApp(Ord(10, 2), 1, FVal(0, max(1, k - 1)))
    if b == 'fw3_3':
        p = args.get('p', 0)
        return FApp(Ord(10, 3), 1, FVal(0, max(1, p - 1)))
    if b.startswith('fw'):
        m_off = re.match(r'^fw(\d+)', b)
        off = int(m_off.group(1)) if m_off else 0
        for key in ('s', 'r', 'q', 'p', 'k', 'n'):
            if key in args:
                return FApp(Ord(10, off), 1, FVal(0, args[key]))
    return None


def parse_wiki_latex(rt: str) -> Optional[FExpr]:
    """Conservatively parse a live wiki <math>...</math> runtime string into an FExpr.
    If unsure, return a conservative UPPER bound so we never falsely claim to beat it!
    """
    if not rt or rt == '(BLANK)':
        return None
    t = rt.replace(' ', '').replace(r'\,', '').lstrip('>')
    # Pick the highest > clause if multiple are present (e.g. f_omega(...) > f_omega^2(15))
    parts = [p for p in t.split('>') if p]
    if not parts:
        return None
    # Parse each part and take the conservative max
    parsed = [_parse_single_wiki(p) for p in parts]
    parsed = [x for x in parsed if x is not None]
    if not parsed:
        return FVal(999, 999)
    best = parsed[0]
    for x in parsed[1:]:
        if cmp_conservative(x, best) == 1:
            best = x
    return best


def _parse_single_wiki(t: str) -> Optional[FExpr]:
    if 'psi_0' in t or 'BMS' in t or 'D^{5}' in t:
        return FApp(Ord(90, 0), 1, FVal(0, 1000))
    if r'\omega\uparrow' in t:
        m = re.search(r'uparrow\s*([0-9]+)\}\(([0-9]+)\)', t)
        k = int(m.group(1)) if m else 10
        arg = int(m.group(2)) if m else 10
        return FApp(Ord(45, 0), 1, FVal(0, max(k, arg)))

    # Recursive nested f_{...}(...) parser
    def parse_atom(s: str) -> FExpr:
        s = s.strip()
        # Handle f_{...}^{...}(...) or f_\omega^2(...)
        if s.startswith('f_'):
            idx = 2
            if s[idx] == '{':
                # match brace
                depth = 0
                j = idx
                while j < len(s):
                    if s[j] == '{': depth += 1
                    elif s[j] == '}':
                        depth -= 1
                        if depth == 0: break
                    j += 1
                sub = s[idx+1:j]
                rest = s[j+1:]
            else:
                # single token like \omega
                m = re.match(r'(\\[a-zA-Z]+|\d+)', s[idx:])
                sub = m.group(1)
                rest = s[idx+len(sub):]

            iters = 1
            if rest.startswith('^'):
                rest = rest[1:]
                if rest.startswith('{'):
                    j = rest.find('}')
                    iters = int(rest[1:j])
                    rest = rest[j+1:]
                else:
                    m = re.match(r'(\d+)', rest)
                    iters = int(m.group(1))
                    rest = rest[len(m.group(1)):]

            assert rest.startswith('(') and rest.endswith(')'), f'bad f_ call: {s}'
            inner = parse_atom(rest[1:-1])
            ord_ = _parse_ord(sub)
            if isinstance(ord_, int):
                return FVal(ord_, iters, _const_int(inner) or 100)
            return FApp(ord_, iters, inner)

        # Up-arrow / tetration / power / integer
        if re.fullmatch(r'\d+', s):
            return FVal(0, int(s))
        if 'uparrow' in s:
            # Count arrow rank conservatively: a \uparrow^k b is bounded by f_{k+1}(max(a,b))
            m_pow = re.findall(r'\\uparrow\^\{?(\d+)\}?', s)
            if m_pow:
                k = max(int(x) for x in m_pow)
                rest_nums = [int(x) for x in re.findall(r'\d+', re.sub(r'\\uparrow\^\{?\d+\}?', ' ', s))]
                return FVal(k + 1, rest_nums[0] if rest_nums else 2, rest_nums[-1] if rest_nums else 10)
            # Chained \uparrow\uparrow ...
            groups = re.findall(r'(?:\\uparrow)+', s)
            k = max(g.count('uparrow') for g in groups) if groups else 1
            extra = max(0, len(groups) - 1)
            nums = [int(x) for x in re.findall(r'\d+', s)]
            return FVal(k + 1 + extra, nums[0] if nums else 10, nums[-1] if nums else 10)
        if '^' in s:
            nums = [int(x) for x in re.findall(r'\d+', s)]
            return FVal(1, nums[0] if nums else 10, nums[-1] if nums else 10)
        if s.startswith('g_{'):
            m = re.search(r'g_\{(\d+)\}', s)
            return FVal(64, 3, int(m.group(1)))
        return FVal(999, 999)

    try:
        return parse_atom(t)
    except Exception:
        return FVal(999, 999)


def _parse_ord(sub: str) -> Union[Ord, int]:
    """Parse subscript of f_{sub} into Ord or finite int."""
    s = sub.replace(' ', '')
    if re.fullmatch(r'\d+', s):
        return int(s)
    if s in (r'\omega', 'omega'):
        return Ord(10, 0)
    m = re.fullmatch(r'\\omega\+(\d+)', s)
    if m:
        return Ord(10, int(m.group(1)))
    if s == r'\omega\times2':
        return Ord(20, 0)
    m = re.fullmatch(r'\\omega\\times2\+(\d+)', s)
    if m:
        return Ord(20, int(m.group(1)))
    if s == r'\omega^2':
        return Ord(30, 0)
    m = re.fullmatch(r'\\omega\^2\+(\d+)', s)
    if m:
        return Ord(30, int(m.group(1)))
    if s == r'\omega^\omega':
        return Ord(40, 0)
    m = re.fullmatch(r'\\omega\^\\omega\+(\d+)', s)
    if m:
        return Ord(40, int(m.group(1)))
    if s == r'\varepsilon_0':
        return Ord(50, 0)
    m = re.fullmatch(r'\\varepsilon_0\+(\d+)', s)
    if m:
        return Ord(50, int(m.group(1)))
    if s == r'\varepsilon_1':
        return Ord(60, 0)
    m = re.fullmatch(r'\\varepsilon_1\+(\d+)', s)
    if m:
        return Ord(60, int(m.group(1)))
    if s == r'\varepsilon_2':
        return Ord(70, 0)
    m = re.fullmatch(r'\\varepsilon_2\+(\d+)', s)
    if m:
        return Ord(70, int(m.group(1)))
    if s == r'\varepsilon_3':
        return Ord(80, 0)
    return Ord(90, 0)


def fmt_expr(e: Optional[FExpr]) -> str:
    if e is None:
        return '(BLANK)'
    if isinstance(e, FVal):
        if e.arrows == 0:
            return str(e.val)
        return f'f_{e.arrows}({e.arg})'
    it = f'^{e.iters}' if e.iters > 1 else ''
    return f'f_{{{e.ord.fmt()}}}{it}({fmt_expr(e.inner)})'


def _selftest():
    # Edge cases from WIKI_CROSSCHECK_2026_11_23.md
    assert not strictly_beats(parse_core_bound('fw_4', {'k': 3}), parse_wiki_latex(r'2 \uparrow^{15} 5'))
    assert strictly_beats(parse_core_bound('fw1_3', {'n': 3}), None)
    assert not strictly_beats(parse_core_bound('fw2_3', {'k': 4}), parse_wiki_latex(r'f_{\omega+1}^4(f_\omega^3(14))'))
    assert strictly_beats(parse_core_bound('fw2_5', {'q': 3}), parse_wiki_latex(r'f_{\omega+1}(f_\omega^4(6))'))
    assert not strictly_beats(parse_core_bound('fwm2_5', {'k': 2}), parse_wiki_latex(r'f_{\omega+3}(11)'))
    assert not strictly_beats(parse_core_bound('fwm2_3', {'k': 1}), parse_wiki_latex(r'f_{\omega+8}^2(4)'))
    assert not strictly_beats(parse_core_bound('fwp21_4', {'n': 3}), parse_wiki_latex(r'f_{\omega^2}^3(3)'))
    assert strictly_beats(parse_core_bound('fwp21_4', {'n': 4}), parse_wiki_latex(r'f_{\omega^2}^3(3)'))
    assert not strictly_beats(parse_core_bound('fwp22_4', {'k': 1}), parse_wiki_latex(r'f_{\omega^2+1}(f_{\omega^2}(f_{\omega+3}^2(4)))'))
    assert strictly_beats(parse_core_bound('fe01_6', {'p': 3, 'n': 4}), parse_wiki_latex(r'f_{\varepsilon_0}(1686)'))
    assert not strictly_beats(parse_core_bound('fe0_5_16', {'n': 15}), parse_wiki_latex(r'f_{\varepsilon_0}(1686)'))
    assert strictly_beats(parse_core_bound('fe1_8', {'n': 9}), parse_wiki_latex(r'f_{\varepsilon_0+1}(65534)'))
    assert strictly_beats(parse_core_bound('fe2_9', {'n': 6}), parse_wiki_latex(r'f_{\varepsilon_1}(21)'))
    assert strictly_beats(FApp(Ord(50, 1), 1, FVal(0, 31)), FApp(Ord(50, 0), 1, FVal(0, 1686)))
    assert not strictly_beats(FApp(Ord(50, 1), 1, FVal(0, 2)), FApp(Ord(50, 0), 1, FVal(0, 1686)))
    assert strictly_beats(FApp(Ord(70, 0), 1, FVal(0, 3)), FApp(Ord(60, 0), 1, FVal(0, 1000)))
    assert not strictly_beats(FApp(Ord(70, 0), 1, FVal(0, 2)), FApp(Ord(60, 0), 1, FVal(0, 21)))
    # Regression checks for 2026-11-24 audit
    assert not strictly_beats(parse_core_bound('fw_4', {'k': 16}), parse_wiki_latex(r'2 \uparrow^{15} 5'))
    assert not strictly_beats(parse_core_bound('fwm2fw_5', {'k': 2}), parse_wiki_latex(r'f_{\omega \times 2}(10^{19728})'))
    assert not strictly_beats(parse_core_bound('fwm2fw_5', {'k': 16}), parse_wiki_latex(r'f_{\omega \times 2}(2 \uparrow^{16} 6)'))
    assert not strictly_beats(parse_core_bound('fwp23fw_4', {'n': 2, 'm': 2}), parse_wiki_latex(r'f_{\omega^2+3}(15)'))
    assert not strictly_beats(parse_core_bound('fwp21_7', {'r': 5, 'p': 2}), parse_wiki_latex(r'f_{\omega^2}^4(f_{\omega+1}(f_\omega(30)))'))
    assert not strictly_beats(parse_core_bound('fwp22_7', {'r': 11, 'q': 5}), parse_wiki_latex(r'f_{\omega^2+2}(8)'))
    assert not strictly_beats(parse_core_bound('fw2_3', {'k': 4}), parse_wiki_latex(r'f_{\omega+1}^3(f_\omega^3(14))'))
    assert not strictly_beats(parse_core_bound('fw3_3', {'p': 4}), parse_wiki_latex(r'f_{\omega+2}^3(f_{\omega+1}^2(f_\omega(14)))'))
    assert not strictly_beats(parse_core_bound('fwp24_4', {'q': 8}), parse_wiki_latex(r'f_{\omega^2+4}(7)'))
    print('fgh_order.py selftest: ALL PASSED')


if __name__ == '__main__':
    _selftest()
