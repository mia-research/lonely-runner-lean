"""E140: the owner's example, speeds 1, 2, 2+eps, 3, 4, 5, 6, 7 (the AP with a runner beside runner 2), eps = 1/100,
1/1000, 1/10000.  Every runner as subject: the cascade's lonely time t* (exact), in units where the speeds are as given.
For the pair (2, 2+eps) as subject, compare with the forced location: the partner's first exit 1/(8 eps), then the first
instant after it where the other six are clear (they have period 1 in t).  Exact."""
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade_t(ds):
    ds = sorted(ds); t = F(1, 8 * ds[0])
    while True:
        way = [d for d in ds if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def six_clear_after(six, t0):
    # first t >= t0 with every one of the six clear; the six are whole numbers so the clear set has period 1
    best = None
    for k in range(floor(t0) - 1, floor(t0) + 3):
        for num in range(0, 8 * 840 + 1):
            t = k + F(num, 8 * 840)
            if t < t0: continue
            if all(nd(d * t) >= E8 for d in six): return t
    return None
for eps in (F(1, 100), F(1, 1000), F(1, 10000)):
    v = [F(1), F(2), 2 + eps, F(3), F(4), F(5), F(6), F(7)]
    print("eps = %s" % eps)
    for i, vs in enumerate(v):
        ds = [abs(w - vs) for j, w in enumerate(v) if j != i]
        t = cascade_t(ds)
        line = "   subject speed %-10s t* = %-14s = %10.4f" % (vs, t, float(t))
        if vs in (2, 2 + eps):
            six = [d for d in ds if d != eps]
            line += "   partner clears at 1/(8 eps) = %s; other six: first clear instant after it = %s" % (1 / (8 * eps), six_clear_after(six, 1 / (8 * eps)))
        print(line)
