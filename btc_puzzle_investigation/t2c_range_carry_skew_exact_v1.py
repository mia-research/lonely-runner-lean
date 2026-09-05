#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
t2c_range_carry_skew_exact_v1.py — EXACT (non-sampled) carry skew P_k = Pr[eps=1 | d in [2^{k-1},2^k)].

Upgrades the sampled table in REVIEW_eis_carry_framing_suppression_v1.md (40k samples) to exact
integer counts. No secrets, no leakage claim: maps the PUBLIC range through the PUBLIC GLV map.

Mechanism (exact):
  glv(d) Babai-reduces (d,0) on L = {(x,y): x + lambda*y = 0 mod n} via coordinate rounding of
  c1 = d*GB2y/GDET, c2 = -d*GB1y/GDET. Between rounding boundaries c1,c2 (half-integers), the
  correction m = c1*GB1 + c2*GB2 is constant, so a(d) = d - m1 (slope 1), b = -m2 (constant).
  Carry law (verified 0/200000 mismatches, provable from |a|,|b| < 2^129 << n):
      eps = 0 if a>=0,b>=0 ; 1 if a<0,b<0 ; [a+b>=0] on mixed signs.
  So eps is piecewise-constant on d with breakpoints only at
      (i) rounding boundaries  d = GDET*(2j+1)/(2*GB2y)  and  d = -GDET*(2j+1)/(2*GB1y)  (rational)
     (ii) sign-flip integers   m1  (a=0)  and  m1+m2  (a+b=0)  inside each segment.
  Exact count = sum over elementary intervals of (#integers in interval) * eps(interval).

Validation: (V1) full enumeration on small ranges; (V2) binomial check vs 200k samples at k=129,135,160;
(V3) local glv asserted identical to t2c_range_glv_structure_v1.glv on random d.
Exact integers / Fractions only.
"""
import math, random, sys, os
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
assert pow(LAM, 3, N_ORDER) == 1 and LAM != 1

def _rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2 * r >= de else q
def _dot(u, v): return u[0]*v[0] + u[1]*v[1]
def _gauss(u, v):
    while True:
        if _dot(v, v) < _dot(u, u): u, v = v, u
        m = _rdiv(_dot(u, v), _dot(u, u)); v = (v[0]-m*u[0], v[1]-m*u[1])
        if _dot(v, v) >= _dot(u, u): return u, v
GB1, GB2 = _gauss((N_ORDER, 0), (-LAM, 1))
GDET = GB1[0]*GB2[1] - GB1[1]*GB2[0]

def glv(d):
    c1 = _rdiv(d*GB2[1], GDET); c2 = _rdiv(-d*GB1[1], GDET)
    return d - (c1*GB1[0]+c2*GB2[0]), -(c1*GB1[1]+c2*GB2[1])

def eps(d):
    a, b = glv(d); return int((a % N_ORDER) + (b % N_ORDER) >= N_ORDER)

def eps_signlaw(a, b):
    if a >= 0 and b >= 0: return 0
    if a < 0 and b < 0: return 1
    return int(a + b >= 0)

# V3: identical to the original module
import t2c_range_glv_structure_v1 as orig
random.seed(7)
for _ in range(500):
    d = random.randrange(1, N_ORDER)
    assert glv(d) == orig.glv(d) and eps(d) == orig.eps(d)
print("[V3] local glv/eps identical to t2c_range_glv_structure_v1 on 500 random d: OK")

def rounding_boundaries(lo, hi):
    """rational d in (lo,hi) where c1(d) or c2(d) is a half-integer."""
    cuts = []
    for num in (GB2[1], -GB1[1]):          # c_i(d) = d*num/GDET
        if num == 0: continue
        # d = GDET*(2j+1)/(2*num) in (lo,hi); j-range from the inverse map (sign of num unknown)
        j_at = lambda dd: Fraction(2*dd*num - GDET, 2*GDET)
        jA, jB = j_at(lo), j_at(hi)
        for j in range(math.floor(min(jA, jB)) - 1, math.ceil(max(jA, jB)) + 2):
            dj = Fraction(GDET * (2*j + 1), 2 * num)
            if lo < dj < hi:
                cuts.append(dj)
    return cuts

def exact_skew(k, verbose=False):
    """exact #{eps=1} and total for d in [2^{k-1}, 2^k)."""
    lo, hi = 2**(k-1), 2**k
    cuts = sorted(set(rounding_boundaries(lo, hi))) + [Fraction(hi)]
    total = hi - lo
    ones = 0
    x = Fraction(lo)
    runs = []   # (start_fraction_of_range, end_, epsval) for the interval map
    for y in cuts:
        # integers in [x, y): ceil(x) .. ceil(y)-1
        t0, t1 = math.ceil(x), math.ceil(y)
        if t1 > t0:
            t = t0
            a, b = glv(t)
            v = eps_signlaw(a, b)
            assert v == eps(t)              # direct check at the sample point
            # sign-flip integers inside (t0, t1): m1 and m1+m2 -- verify constancy
            m1, m2 = t - a, -b
            flips = sorted({f for f in (m1, m1 + m2) if t0 < f < t1})
            pts = [t0] + flips + [t1]
            for i in range(len(pts) - 1):
                vv = eps(pts[i])
                assert eps(pts[i+1] - 1) == vv   # constancy on the whole elementary run
                ones += vv * (pts[i+1] - pts[i])
                if verbose and pts[i+1] - pts[i] > total // 16:
                    runs.append((Fraction(pts[i]-lo, total), Fraction(pts[i+1]-lo, total), vv))
        x = y
    return ones, total, runs

# V1: full enumeration on small ranges
random.seed(11)
for (a0, L) in [(2**20, 10_000), (2**60, 5_000), (2**100, 3_000)]:
    lo, hi = a0, a0 + L
    ones_direct = sum(eps(d) for d in range(lo, hi))
    # reuse exact_skew machinery on [lo,hi)
    cuts = sorted(set(rounding_boundaries(lo, hi))) + [Fraction(hi)]
    ones_exact = 0; x = Fraction(lo)
    for y in cuts:
        t0, t1 = math.ceil(x), math.ceil(y)
        if t1 > t0:
            t = t0; a1, b1 = glv(t)
            m1, m2 = t - a1, -b1
            flips = sorted({f for f in (m1, m1 + m2) if t0 < f < t1})
            pts = [t0] + flips + [t1]
            for i in range(len(pts) - 1):
                ones_exact += eps(pts[i]) * (pts[i+1] - pts[i])
        x = y
    assert ones_direct == ones_exact, (a0, ones_direct, ones_exact)
print("[V1] exact counter == full enumeration on 3 small ranges: OK")

# main table
print()
print("=" * 96)
print(" EXACT range->carry skew  P_k = Pr[eps_LBE=1 | d uniform in [2^(k-1), 2^k)]   (exact integer counts)")
print("=" * 96)
res = {}
for k in list(range(127, 143)) + [145, 146]:
    ones, total, runs = exact_skew(k)
    res[k] = (ones, total)
    print(f"  k={k:3d}:  ones {ones:>26d} / 2^{k-1:<3d}   P_k = {ones/total:.9f}   (P_k - 1/2 = {ones/total - 0.5:+.9f})")
print("-" * 96)

# V2: binomial consistency vs fresh samples at k=129,135,140 (exact fractions vs sampled rate)
random.seed(20260821)
for k in (129, 135, 140):
    lo, hi = 2**(k-1), 2**k
    M = 200_000
    s = sum(eps(random.randrange(lo, hi)) for _ in range(M))
    pex = Fraction(res[k][0], res[k][1])
    print(f"[V2] k={k}: sampled {s}/{M} = {s/M:.4f}  vs exact {float(pex):.4f} "
          f"(|z| = {abs(s/M - float(pex))/math.sqrt(float(pex)*(1-float(pex))/M):.2f} sigma)")

# the interval map at k=129 (which sub-ranges of the PUBLIC range have eps pinned)
ones, total, runs = exact_skew(129, verbose=True)
print()
print(" k=129 interval map (runs longer than 1/16 of the range; positions as exact fractions):")
for (f0, f1, v) in runs:
    print(f"   [{f0} .. {f1}) of the range  ->  eps = {v}")
print("=" * 96)
