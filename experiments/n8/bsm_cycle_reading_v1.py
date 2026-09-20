"""
BSM cycle reading.  For each runner, its reading is CALCULATED cycle by cycle, where a cycle
is one lap of the slowest runner, t in [c/v1, (c+1)/v1].  No first-window requirement, no
lattice, no candidate search.

Inside a cycle the boundary set is finite and named: every zone endpoint (8k +- 1)/(8d) of
each of the runner's seven differences d, plus the two ends of the cycle.  Zones
((8k-1)/(8d), (8k+1)/(8d)) are OPEN, so their endpoints are clear.  Boundary points and open
cells are evaluated separately; touching zones are never merged.  ">= 1/8" is inclusive.

Integer speeds: exact integer arithmetic.  A runner's reading has period 1/gcd(its
differences), so if no cycle inside one period is lonely, that is decided, not capped.

Irrational speeds: exact arithmetic in Q(sqrt 2) (a + b*sqrt2 with rational a, b and exact
sign tests).  No period exists; a cycle cap is stated and reported.
"""
from fractions import Fraction as F
from math import gcd, floor, ceil
import sys


# ---------------------------------------------------------------- exact test, integer speeds
def clear_pq(e, p, q):
    """difference e is at circle distance >= 1/8 at t = p/q  (Prop 2.1 form)."""
    r = (e * p) % q
    return 8 * min(r, q - r) >= q


def lonely_pq(ds, p, q):
    return all(clear_pq(e, p, q) for e in ds)


def reduce_pq(p, q):
    g = gcd(p, q)
    return p // g, q // g


def read_cycle_int(ds, v1, c, closed=False):
    """Full BSM reading of one cycle.  Returns (lonely boundary points, lonely cells, the
    boundary points as reduced (p,q)), all exact."""
    T0, T1 = (c, v1), (c + 1, v1)
    pts = {reduce_pq(*T0), reduce_pq(*T1)}
    for d in set(ds):
        lo = ceil(F(8 * d * c, v1))
        hi = floor(F(8 * d * (c + 1), v1))
        for j in range(lo, hi + 1):
            if j % 8 in (1, 7):
                pts.add(reduce_pq(j, 8 * d))
    pts = sorted(pts, key=lambda pq: F(pq[0], pq[1]))
    test = (lambda p, q: all(_closed(e, p, q) for e in ds)) if closed else (lambda p, q: lonely_pq(ds, p, q))
    lonely_pts = [pq for pq in pts if test(*pq)]
    lonely_cells = []
    for (p1, q1), (p2, q2) in zip(pts, pts[1:]):
        mp, mq = reduce_pq(p1 * q2 + p2 * q1, 2 * q1 * q2)
        if test(mp, mq):
            lonely_cells.append(((p1, q1), (p2, q2)))
    return lonely_pts, lonely_cells, pts


def _closed(e, p, q):
    """deliberately WRONG: closed zones (strict inequality).  Control C-b only."""
    r = (e * p) % q
    return 8 * min(r, q - r) > q


def read_runner_int(V, i, closed=False):
    """Read cycles of the slowest runner until the runner is lonely, or one full period of
    its reading has been read.  Returns a record."""
    v1 = min(V)
    ds = [abs(V[i] - V[j]) for j in range(len(V)) if j != i]
    g = 0
    for e in ds:
        g = gcd(g, e)
    # period of the reading is 1/g; cycles needed to cover it: ceil(v1/g)
    ncycles = -(-v1 // g)
    for c in range(ncycles):
        lp, lc, pts = read_cycle_int(ds, v1, c, closed)
        # BSM consistency: a clear open cell has clear endpoints (zones are open)
        for a, b in lc:
            assert (a in lp) and (b in lp) or closed, ("cell clear, endpoint not", V, i, c, a, b)
        if lp:
            p, q = lp[0]
            kind = []
            for d in sorted(set(ds)):
                if (8 * d * p) % q == 0:
                    j = 8 * d * p // q
                    if j % 8 == 1:
                        kind.append(f"opening of {d}")
                    elif j % 8 == 7:
                        kind.append(f"closing of {d}")
            return dict(runner=i, speed=V[i], cycle=c, t=F(p, q), n_lonely_points=len(lp),
                        n_lonely_cells=len(lc), n_boundary=len(pts), kind=kind or ["cycle end"],
                        recheck=_recheck(ds, F(p, q)))
    return dict(runner=i, speed=V[i], cycle=None, period_cycles=ncycles)


def _recheck(ds, t):
    """independent: circle distance computed directly from the fractional part."""
    for e in ds:
        x = e * t
        fr = x - (x.numerator // x.denominator)
        if min(fr, 1 - fr) < F(1, 8):
            return False
    return True


# ---------------------------------------------------------------- exact Q(sqrt2) arithmetic
class R2:
    """a + b*sqrt(2), a and b Fractions.  Exact order and floor."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(s, o): o = _r(o); return R2(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __sub__(s, o): o = _r(o); return R2(s.a - o.a, s.b - o.b)
    def __rsub__(s, o): return _r(o) - s
    def __mul__(s, o): o = _r(o); return R2(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = _r(o); n = o.a * o.a - 2 * o.b * o.b
        return s * R2(o.a / n, -o.b / n)
    def __neg__(s): return R2(-s.a, -s.b)
    def __rtruediv__(s, o): return _r(o) / s

    def sign(s):
        a, b = s.a, s.b
        if a >= 0 and b >= 0: return 0 if (a == 0 and b == 0) else 1
        if a <= 0 and b <= 0: return -1
        # opposite signs: compare a^2 with 2 b^2
        d = a * a - 2 * b * b
        if a > 0: return 1 if d > 0 else (-1 if d < 0 else 0)
        return -1 if d > 0 else (1 if d < 0 else 0)

    def __lt__(s, o): return (s - o).sign() < 0
    def __le__(s, o): return (s - o).sign() <= 0
    def __ge__(s, o): return (s - o).sign() >= 0
    def __gt__(s, o): return (s - o).sign() > 0
    def __eq__(s, o): return (s - o).sign() == 0
    def __hash__(s): return hash((s.a, s.b))

    def approx(s): return float(s.a) + float(s.b) * 2 ** 0.5

    def floor(s):
        n = floor(s.approx())
        while R2(n) > s: n -= 1
        while R2(n + 1) <= s: n += 1
        return n

    def __repr__(s):
        return f"{s.a}" + (f" + {s.b}*sqrt2" if s.b else "")


def _r(x): return x if isinstance(x, R2) else R2(x)


def lonely_r2(ds, t):
    for e in ds:
        x = e * t
        fr = x - x.floor()
        if fr < F(1, 8) or fr > F(7, 8):
            return False
    return True


def read_runner_r2(V, i, cap_cycles):
    v1 = min(V)
    ds = [abs(V[i] - V[j]) if V[i] > V[j] else V[j] - V[i] for j in range(len(V)) if j != i]
    for c in range(cap_cycles):
        T0, T1 = R2(c) / v1, R2(c + 1) / v1
        pts = {T0, T1}
        for d in ds:
            lo = (8 * d * T0).floor()
            hi = (8 * d * T1).floor() + 1
            for j in range(lo, hi + 1):
                if j % 8 in (1, 7):
                    t = R2(j) / (8 * d)
                    if T0 <= t <= T1:
                        pts.add(t)
        pts = sorted(pts, key=lambda x: (x.approx(),))
        # exact re-sort guard: adjacent float ties are resolved exactly
        pts.sort(key=lambda x: x.approx())
        for k in range(len(pts) - 1):
            assert pts[k] <= pts[k + 1]
        lp = [t for t in pts if lonely_r2(ds, t)]
        lc = []
        for a, b in zip(pts, pts[1:]):
            if lonely_r2(ds, (a + b) / 2):
                lc.append((a, b))
                assert a in lp and b in lp, ("cell clear, endpoint not", i, c)
        if lp:
            return dict(runner=i, cycle=c, t=lp[0], t_approx=lp[0].approx(),
                        n_lonely_points=len(lp), n_lonely_cells=len(lc), n_boundary=len(pts))
    return dict(runner=i, cycle=None, cap=cap_cycles)


if __name__ == "__main__":
    pass
