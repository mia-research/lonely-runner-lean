"""Exact arithmetic in Q(sqrt 2): x = a + b*sqrt2, a, b Fractions. Field operations, exact sign (integer comparison of
a^2 and 2 b^2), exact floor (a float estimate only proposes candidates; exact signs decide). Positive control at the
bottom: run as a script."""
from fractions import Fraction as F
from math import floor, isqrt
class Q2:
    __slots__ = ('a', 'b')
    def __init__(s, a, b=0): s.a = F(a); s.b = F(b)
    def _c(o): return o if isinstance(o, Q2) else Q2(o)
    def __add__(s, o): o = Q2._c(o); return Q2(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return Q2(-s.a, -s.b)
    def __sub__(s, o): return s + (-Q2._c(o))
    def __rsub__(s, o): return Q2._c(o) - s
    def __mul__(s, o): o = Q2._c(o); return Q2(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = Q2._c(o); n = o.a * o.a - 2 * o.b * o.b
        return s * Q2(o.a / n, -o.b / n)
    def __rtruediv__(s, o): return Q2._c(o) / s
    def sign(s):
        a, b = s.a, s.b
        if b == 0: return (a > 0) - (a < 0)
        if a == 0: return (b > 0) - (b < 0)
        if a > 0 and b > 0: return 1
        if a < 0 and b < 0: return -1
        sa = a * a - 2 * b * b          # a^2 vs 2 b^2 (never 0 unless a = b = 0)
        return (1 if sa > 0 else -1) * (1 if a > 0 else -1)
    def __lt__(s, o): return (s - o).sign() < 0
    def __le__(s, o): return (s - o).sign() <= 0
    def __gt__(s, o): return (s - o).sign() > 0
    def __ge__(s, o): return (s - o).sign() >= 0
    def __eq__(s, o): return (s - Q2._c(o)).sign() == 0
    def __hash__(s): return hash((s.a, s.b))
    def __float__(s): return float(s.a) + float(s.b) * 2 ** 0.5
    def floor(s):
        k = floor(float(s))
        for kk in (k - 1, k, k + 1, k - 2, k + 2):
            if s >= kk and s < kk + 1: return kk
        raise RuntimeError('floor')
    def __repr__(s): return '%s%+s*r2' % (s.a, s.b) if s.b else str(s.a)
E = F(1, 8)
def dist(x):
    f = x - x.floor(); return f if f < 1 - f else 1 - f
if __name__ == '__main__':
    r2 = Q2(0, 1)
    assert r2 * r2 == 2 and (Q2(3, 2) / Q2(3, 2)) == 1 and Q2(1, 1).floor() == 2 and Q2(-1, 1).floor() == 0
    assert (Q2(F(7, 5), 0) - r2).sign() < 0 and (Q2(F(3, 2), 0) - r2).sign() > 0
    assert dist(Q2(F(1, 8), 0)) == E and dist(Q2(0, F(1, 1)) * 3) == dist(Q2(0, 3))
    print("Q(sqrt2) positive control: pass")
