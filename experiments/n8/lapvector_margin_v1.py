"""Exact margin of a runner: max over the first window of min_d ||d t||, minus 1/8.

f(t) = min_d ||d t|| is piecewise linear.  Local maxima sit at
  - peaks of a single ||d t||  ->  t = (2k+1)/(2d)
  - crossings ||d_a t|| = ||d_b t||  ->  t = k/(d_a+d_b) or k/(d_a-d_b)
  - the two window endpoints.
Evaluating that finite set is exact.
"""
from fractions import Fraction as F

def _nrm(num, den):
    r = num % den
    return min(r, den - r), den          # ||num/den|| = r'/den

def fval(ds, p, q):
    """min_d ||d p/q|| as a Fraction."""
    best = None
    for d in ds:
        r = (d * p) % q
        v = min(r, q - r)
        if best is None or v < best:
            best = v
    return F(best, q)

def margin(ds):
    m = min(ds); lo, hi = F(1, 8*m), F(7, 8*m)
    dens = set()
    for d in ds:
        dens.add(2*d)
    for a in range(len(ds)):
        for b in range(a+1, len(ds)):
            dens.add(ds[a]+ds[b])
            if ds[a] != ds[b]:
                dens.add(abs(ds[a]-ds[b]))
    best = max(fval(ds, 1, 8*m), fval(ds, 7, 8*m))
    bt = lo
    for q in dens:
        klo = int(lo*q); khi = int(hi*q)+1
        for k in range(max(klo-1,0), khi+1):
            t = F(k, q)
            if t < lo or t > hi:
                continue
            v = fval(ds, t.numerator, t.denominator)
            if v > best:
                best, bt = v, t
    return best - F(1,8), bt
