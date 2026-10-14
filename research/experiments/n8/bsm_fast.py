from math import gcd
from functools import reduce

def _lcm(a,b): return a*b//gcd(a,b)

def bsm_count(D):
    """Number of maximal lonely components for integer constraint set D on [0,1].
       Pure integer arithmetic.  Boundary points t=(8k+-1)/(8d) and open cells are
       evaluated separately; cells are probed at their midpoint, which is exact once
       everything is placed over the common denominator M."""
    L = reduce(_lcm, D)
    M = 16*L                      # 8L for boundaries, doubled so midpoints are integral
    B = {0, M}
    for d in D:
        step = M//d               # integer
        for k in range(0, d+1):
            for s in (-1, 1):
                t = k*step + s*(step//8)
                if 0 <= t <= M: B.add(t)
    B = sorted(B)
    def ok(n):
        for d in D:
            r = (d*n) % M
            if 8*min(r, M-r) < M: return False
        return True
    pt = [ok(t) for t in B]
    cell = [ok((B[i]+B[i+1])//2) for i in range(len(B)-1)]
    # count maximal closed lonely runs
    n = 0; inrun = False
    for i in range(len(B)):
        here = pt[i]
        right = cell[i] if i < len(cell) else False
        if here and not inrun:
            n += 1; inrun = True
        if inrun and not right:
            inrun = False
    return n

def reduce_int(V):
    """V: list of Fraction/int speeds -> (reduced integer speeds, cycle length as Fraction)"""
    from fractions import Fraction as Q
    V = [Q(v) for v in V]
    L = reduce(_lcm, [v.denominator for v in V])
    Vi = [int(v*L) for v in V]
    g = reduce(gcd, [abs(Vi[j]-Vi[i]) for i in range(len(V)) for j in range(i+1,len(V))])
    return [(v-min(Vi))//g for v in Vi], Q(L, g)

def min_rate(V):
    from fractions import Fraction as Q
    Vr, P = reduce_int(V)
    best = None
    for i in range(8):
        D = sorted({abs(w-Vr[i]) for w in Vr if w!=Vr[i]})
        r = Q(bsm_count(D)) / P
        if best is None or r < best: best = r
    return best
