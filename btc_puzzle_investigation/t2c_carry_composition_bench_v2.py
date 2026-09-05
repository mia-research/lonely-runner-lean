#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
t2c_carry_composition_bench_v2.py -- HONEST re-do of the T2c carry-composition benchmark, fixing the two
deck-stacking issues found in the v1 self-audit (see PREREG_..._DEVIATIONS D3):

  FIX (a): the 1-D partition variant is now ONE BSGS over I with the giant-steps REORDERED by the public
           carry prior -- NOT per-run BSGS. This removes the v1 per-run-setup artifact (the fake 14-21x
           "liability"). For a UNIFORM d, reordering giants cannot change the expected steps-to-find, so
           this reports the TRUE no-help ratio (~1), not an inflated one.
  FIX (b): the actual "sqrt6 composition" is the 2-D GLV DLP -- solve P=[a]G+[b]*phi(G) over the (a,b)
           box, where the carry eps is a CONTIGUOUS sign-region constraint (no fragmentation). We build
           that solver and measure its op-count directly vs the 1-D interval baseline, across k.

Model scale, ZERO secp power. Group-op counts = # EC point additions (exact integers). No float in the
signal path (check_no_float.sh must pass). Not the CLOSED lambda-fold: all search stays bounded.
"""
import sys, os, math, random, statistics
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model_curve_infra_v1 as M

# ---- GLV lattice / eps / partition (ported to (n,lam)) ----
def _rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2 * r >= de else q
def _dot(u, v): return u[0] * v[0] + u[1] * v[1]
def _gauss(u, v):
    while True:
        if _dot(v, v) < _dot(u, u): u, v = v, u
        m = _rdiv(_dot(u, v), _dot(u, u)); v = (v[0] - m * u[0], v[1] - m * u[1])
        if _dot(v, v) >= _dot(u, u): return u, v

class Lattice:
    def __init__(self, n, lam):
        assert pow(lam, 3, n) == 1 and lam % n != 1
        self.n = n; self.lam = lam
        self.GB1, self.GB2 = _gauss((n, 0), (-lam, 1))
        self.GDET = self.GB1[0] * self.GB2[1] - self.GB1[1] * self.GB2[0]
    def glv(self, d):
        c1 = _rdiv(d * self.GB2[1], self.GDET); c2 = _rdiv(-d * self.GB1[1], self.GDET)
        return d - (c1 * self.GB1[0] + c2 * self.GB2[0]), -(c1 * self.GB1[1] + c2 * self.GB2[1])
    def eps(self, d):
        a, b = self.glv(d); return int((a % self.n) + (b % self.n) >= self.n)

def _rounding_boundaries(lat, lo, hi):
    cuts = []
    for num in (lat.GB2[1], -lat.GB1[1]):
        if num == 0: continue
        j_at = lambda dd: Fraction(2 * dd * num - lat.GDET, 2 * lat.GDET)
        jA, jB = j_at(lo), j_at(hi)
        for j in range(math.floor(min(jA, jB)) - 1, math.ceil(max(jA, jB)) + 2):
            dj = Fraction(lat.GDET * (2 * j + 1), 2 * num)
            if lo < dj < hi: cuts.append(dj)
    return cuts

def partition_runs(lat, k):
    lo, hi = 2 ** (k - 1), 2 ** k
    cuts = sorted(set(_rounding_boundaries(lat, lo, hi))) + [Fraction(hi)]
    runs = []; x = Fraction(lo)
    for y in cuts:
        t0, t1 = math.ceil(x), math.ceil(y)
        if t1 > t0:
            t = t0; a, b = lat.glv(t); m1, m2 = t - a, -b
            flips = sorted({f for f in (m1, m1 + m2) if t0 < f < t1})
            pts = [t0] + flips + [t1]
            for i in range(len(pts) - 1):
                v = lat.eps(pts[i]); runs.append((pts[i], pts[i + 1], v))
        x = y
    merged = []
    for (a0, a1, v) in runs:
        if merged and merged[-1][2] == v and merged[-1][1] == a0:
            merged[-1] = (merged[-1][0], a1, v)
        else: merged.append((a0, a1, v))
    return merged

# ---- counting EC ops ----
class Ctr:
    __slots__ = ("ops",)
    def __init__(self): self.ops = 0
def cadd(c, P, Q, t): t.ops += 1; return c.add(P, Q)
def cmul(c, k, P, t):
    if P is None or k == 0: return None
    if k < 0: k, P = -k, c.neg(P)
    R = None; Q = P
    while k:
        if k & 1: R = cadd(c, R, Q, t)
        Q = cadd(c, Q, Q, t); k >>= 1
    return R

# ============================ FIX (a): 1-D BSGS, standard group-op metric ======
# METRIC (both 1-D and 2-D): group operations = (baby steps) + (giant steps examined until solution),
# 1 unit each -- the standard BSGS cost. This is instrument-consistent across solvers (no per-cell
# scalar-mult vs incremental-add mismatch). We run the real solver for correctness but the reported
# count is baby+giant steps.
_NULL = Ctr()
def bsgs_ordered(curve, G, P, lo, hi, ctr, cell_order=None):
    """BSGS on [lo,hi); giant cells visited in cell_order or natural. Metric = m (baby) + giant cells
    examined until d found. For UNIFORM d, the order cannot change the EXPECTED giant count (FIX a)."""
    w = hi - lo; m = M.isqrt(w - 1) + 1
    Plo = cmul(curve, lo, G, _NULL)
    Q = curve.add(P, curve.neg(Plo)) if Plo is not None else P            # [d-lo]G
    table = {}; cur = None
    for j in range(m):
        if cur not in table: table[cur] = j
        cur = curve.add(cur, G)
    ctr.ops += m                                                          # baby steps
    ncells = (w - 1) // m + 1
    order = cell_order if cell_order is not None else range(ncells)
    for step, i in enumerate(order, 1):
        base = cmul(curve, i * m, G, _NULL)
        giant = curve.add(Q, curve.neg(base))
        j = table.get(giant)
        if j is not None and 0 <= i * m + j < w:
            ctr.ops += step                                              # giant steps examined
            return lo + i * m + j
    return None

def cell_order_by_carry(lat, k, m, ncells, lo):
    """Order giant cells by the public carry prior: cells whose majority eps matches the interval's
    majority class first (the best a public labeling can do -- and, for uniform d, no better than random)."""
    runs = partition_runs(lat, k)
    # per-cell majority eps via run coverage
    ones_frac = []
    ri = 0
    for i in range(ncells):
        c0 = lo + i * m; c1 = c0 + m
        ones = 0
        for (rlo, rhi, v) in runs:
            a = max(c0, rlo); b = min(c1, rhi)
            if b > a and v == 1: ones += b - a
        ones_frac.append(ones)
    # interval majority class
    tot_ones = sum(hi - lo2 for (lo2, hi, v) in runs if v == 1)
    maj = 1 if 2 * tot_ones >= (2 ** (k - 1)) else 0
    key = (lambda i: -ones_frac[i]) if maj == 1 else (lambda i: ones_frac[i])
    return sorted(range(ncells), key=key)

# ============================ FIX (b): 2-D GLV meet-in-the-middle ==============
def glv_box(lat, k):
    """Exact bounding box [aL,aH)x[bL,bH) of {glv(d): d in [2^(k-1),2^k)}, from the run structure."""
    runs = partition_runs(lat, k)
    aL = bL = None; aH = bH = None
    for (rlo, rhi, v) in runs:
        a0, b0 = lat.glv(rlo)          # a=d-m1 (slope 1), b const on the run
        a_lo, a_hi = a0, a0 + (rhi - 1 - rlo)
        for (x, lo_) in ((a_lo, True), (a_hi, True)):
            aL = x if aL is None else min(aL, x); aH = x if aH is None else max(aH, x)
        bL = b0 if bL is None else min(bL, b0); bH = b0 if bH is None else max(bH, b0)
    return aL, aH + 1, bL, bH + 1

def bsgs_2d(curve, G, Q, P, aL, aH, bL, bH, ctr, eps_region=None, lat=None):
    """Solve [a]G+[b]Q==P, (a,b) in box. Metric = Wb (baby over b) + a-steps examined (giant over a).
    If eps_region in {0,1}, giant steps over the WHOLE a-range still cost 1 each (you cannot skip a rows
    of a non-axis-aligned sign-region for free) -- the eps constraint only filters the ACCEPT test, so it
    saves at most a constant factor via a smaller effective box, not the giant scan itself."""
    table = {}; pt = cmul(curve, bL, Q, _NULL)
    for b in range(bL, bH):
        table.setdefault(pt, b); pt = curve.add(pt, Q)
    ctr.ops += (bH - bL)                                                  # baby steps
    aG = cmul(curve, aL, G, _NULL)
    for step, a in enumerate(range(aL, aH), 1):
        target = curve.add(P, curve.neg(aG))              # P-[a]G = [b]Q
        b = table.get(target)
        if b is not None and (eps_region is None or lat is None
                              or int((a % lat.n) + (b % lat.n) >= lat.n) == eps_region):
            ctr.ops += step                                              # giant steps examined
            return (a, b)
        aG = curve.add(aG, G)
    return None

# ============================ validation =====================================
def validate():
    N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
    import t2c_range_glv_structure_v1 as orig
    lat = Lattice(N_SECP, LAM); random.seed(7)
    ok = all(lat.glv(d) == orig.glv(d) and lat.eps(d) == orig.eps(d)
             for d in (random.randrange(1, N_SECP) for _ in range(300)))
    print(f"  [V] ported glv/eps == t2c on 300 secp d: {ok}"); assert ok

def make_arm(q):
    a = M.select_j0_prime_order(q, exclude_anomalous=True)
    if a is None: return None
    return dict(q=a.q, B=a.B, n=a.N, beta=a.beta, lam=a.lam, G=(a.Gx, a.Gy),
                curve=M.Curve(a.q, 0, a.B), lat=Lattice(a.N, a.lam),
                Q=(a.beta * a.Gx % a.q, a.Gy))

def run(qs, T, seed=20260826):
    print("== validation =="); validate()
    print(f"\n== HONEST T2c carry-composition bench  T={T}  (op = EC add) ==")
    for q in qs:
        arm = make_arm(q)
        if arm is None: print(f"  q={q}: none"); continue
        n = arm["n"]; nb = n.bit_length(); lat = arm["lat"]; cu = arm["curve"]
        G = arm["G"]; Q = arm["Q"]
        print(f"\n curve q={arm['q']} B={arm['B']} n={n}(~2^{nb})  sqrt(n)~2^{nb//2}")
        print(f"   {'k':>3} {'P_k':>6} {'1Dbase':>8} {'1Dvar':>8} {'R1D':>6} | "
              f"{'boxWa':>7} {'boxWb':>6} {'2Dfull':>9} {'2D/1D':>8} {'2Doracle':>9} {'2Dor/1D':>8}")
        rng = random.Random(seed + q)
        # k schedule: span the genuinely-2-D regime [nb//2 .. nb]
        ks = sorted(set([nb // 2, nb // 2 + 2, (nb // 2 + nb) // 2, nb - 2, nb - 1]))
        ks = [k for k in ks if 4 <= k <= nb]
        for k in ks:
            runs = partition_runs(lat, k)
            ones = sum(hi - lo for (lo, hi, v) in runs if v == 1)
            Pk = Fraction(ones, 2 ** (k - 1))
            lo, hi = 2 ** (k - 1), 2 ** k
            m = M.isqrt((hi - lo) - 1) + 1; ncells = (hi - lo - 1) // m + 1
            corder = cell_order_by_carry(lat, k, m, ncells, lo)
            aL, aH, bL, bH = glv_box(lat, k); Wa, Wb = aH - aL, bH - bL
            b1 = []; v1 = []; f2 = []; o2 = []
            for _ in range(T):
                d = rng.randrange(lo, hi); P = cu.mul(d, G)
                c = Ctr(); r = bsgs_ordered(cu, G, P, lo, hi, c); assert r == d; b1.append(c.ops)
                c = Ctr(); r = bsgs_ordered(cu, G, P, lo, hi, c, corder); assert r == d; v1.append(c.ops)
                c = Ctr(); r = bsgs_2d(cu, G, Q, P, aL, aH, bL, bH, c); assert cu.add(cu.mul(r[0], G), cu.mul(r[1], Q)) == P; f2.append(c.ops)
                epsd = lat.eps(d)
                c = Ctr(); r = bsgs_2d(cu, G, Q, P, aL, aH, bL, bH, c, eps_region=epsd, lat=lat); o2.append(c.ops)
            mb = statistics.median(b1); mv = statistics.median(v1)
            m2 = statistics.median(f2); mo = statistics.median(o2)
            print(f"   {k:>3} {float(Pk):>6.3f} {int(mb):>8} {int(mv):>8} {float(Fraction(int(mv),int(mb))):>6.3f} | "  # noqa: float
                  f"{Wa:>7} {Wb:>6} {int(m2):>9} {float(Fraction(int(m2),int(mb))):>8.2f} "                          # noqa: float
                  f"{int(mo):>9} {float(Fraction(int(mo),int(mb))):>8.2f}")                                          # noqa: float

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[1 << 18, 1 << 22])
    ap.add_argument("--T", type=int, default=80)
    a = ap.parse_args()
    qs = []
    for q0 in a.qs:
        q = q0 | 1
        while not (q % 3 == 1 and M.is_prime(q) and M.select_j0_prime_order(q, exclude_anomalous=True) is not None):
            q += 2
        qs.append(q)
    run(qs, a.T)
