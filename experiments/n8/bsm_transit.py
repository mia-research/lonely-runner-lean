from fractions import Fraction as Q
from functools import reduce
from math import gcd

def boundary_set(D):
    """The predicate ||d t|| >= 1/8 changes only at t = (8k +- 1)/(8d)."""
    B = {Q(0), Q(1)}
    for d in D:
        for k in range(0, d+1):
            for s in (-1, 1):
                t = Q(8*k + s, 8*d)
                if 0 <= t <= 1:
                    B.add(t)
    return sorted(B)

def lonely_at(D, t):
    for d in D:
        r = (d*t) % 1
        if min(r, 1-r) < Q(1,8):
            return False
    return True

def bsm_good(D):
    """Boundary Set Method.  Boundary POINTS and OPEN CELLS are evaluated
       separately: the bad set of each d is the OPEN interval between its two
       boundaries, so an endpoint can be lonely while the cell interior is not.
       Each open cell is probed at three interior points; disagreement means the
       boundary list is incomplete."""
    B = boundary_set(D)
    pieces = []          # (lo, hi, closed_lo, closed_hi) lonely segments
    anomalies = 0
    cell_ok = []
    for i in range(len(B)-1):
        lo, hi = B[i], B[i+1]
        probes = [lo + (hi-lo)*Q(p,4) for p in (1,2,3)]
        vals = [lonely_at(D, p) for p in probes]
        if len(set(vals)) != 1:
            anomalies += 1
        cell_ok.append(vals[1])
    pt_ok = [lonely_at(D, t) for t in B]
    # assemble maximal closed lonely sets
    out = []
    cur = None
    for i, t in enumerate(B):
        left  = cell_ok[i-1] if i > 0 else False
        right = cell_ok[i]   if i < len(cell_ok) else False
        if pt_ok[i]:
            if cur is None: cur = t
            if not right:
                out.append((cur, t)); cur = None
        else:
            if cur is not None:
                out.append((cur, B[i-1] if not left else t)); cur = None
    if cur is not None:
        out.append((cur, B[-1]))
    out = [(a,b) for a,b in out if not (a==b==Q(0)) and not (a==b==Q(1))]
    return out, len(B), anomalies

def reduce_config(V):
    L = reduce(lambda a,b: a*b//gcd(a,b), [v.denominator for v in V])
    Vi = [int(v*L) for v in V]
    g = reduce(gcd, [abs(Vi[j]-Vi[i]) for i in range(len(V)) for j in range(i+1, len(V))])
    return [(v - min(Vi))//g for v in Vi], Q(L, g)
