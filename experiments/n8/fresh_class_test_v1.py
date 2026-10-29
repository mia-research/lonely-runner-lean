# E643: does the other agent's Fresh.NativeComparableFourthGrid.Class (with ScaledClass: V free) hold on a reading set S (whole numbers = the 7 disparities of the subject)?
# Exact Fractions.  Arithmetic part: K common, readings a,b,c over u are 8m+7/(8K); H<=A<=3B, B<=3A, H>=1; e between; slow others: 2d<=d_u and fract(d*K/d_u) in [1/8,3/4].
# InWay part: W=V+1/(8 d_u); Z=lo(a,W); Y=lo(b,Z); InWay(b,Z), InWay(c,Y), lo(s,U)=(ceil(sU-7/8)+1/8)/s, InWay(d,t): distInt(d t)<1/8.
import sys, math, itertools, pickle
from fractions import Fraction as F
def fl(x): return math.floor(x)
def ce(x): return -math.floor(-x)
def distint(x): f = x - fl(x); return min(f, 1 - f)
def lo(s, U): return (F(ce(s * U - F(7, 8))) + F(1, 8)) / s
def hk(a, u):
    r = F(a, u) if not isinstance(a, F) else a / u
    H = fl(r / 8); d = r - 8 * H
    if d <= 0 or d > F(7, 8): return None
    K = F(7, 8) / d
    return (H, K) if K.denominator == 1 else None
def test(S):
    S = list(S); out = {'arith': [], 'full': []}
    for u in S:
        for a, b, c in itertools.product(S, repeat=3):
            ra, rb, rc = hk(a, u), hk(b, u), hk(c, u)
            if not (ra and rb and rc): continue
            (H, K), (A, K2), (B, K3) = ra, rb, rc
            if not (K == K2 == K3 and K >= 1 and H >= 1 and H <= A <= 3 * B and B <= 3 * A): continue
            for e in S:
                if not (a <= e <= b and e <= c): continue
                if not all(2 * d <= u and (lambda f: F(1, 8) <= f <= F(3, 4))((F(d) * K / u) - fl(F(d) * K / u)) for d in S if d not in (u, a, b, c, e)): continue
                out['arith'].append((u, a, b, c, e, int(K)))
                V = K / F(u); W = V + F(1, 8 * u); Z = lo(F(a), W); Y = lo(F(b), Z)
                if distint(b * Z) < F(1, 8) and distint(c * Y) < F(1, 8): out['full'].append((u, a, b, c, e, int(K)))
    return out
if __name__ == '__main__':
    sets = [tuple(int(x) for x in s.split(',')) for s in sys.argv[1:]] if len(sys.argv) > 1 else pickle.load(open('survivors44.pkl', 'rb'))
    na = nf = 0
    for S in sets:
        r = test(S); na += bool(r['arith']); nf += bool(r['full'])
        print(S, 'arith', len(r['arith']), 'full', len(r['full']), (r['full'] or r['arith'])[:1])
    print('sets', len(sets), 'with arithmetic fit', na, 'with full Class fit', nf)
