#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
t2c_carry_partition_kangaroo_bench_v1.py -- runner for PREREG_t2c_carry_partition_kangaroo_bench_v1.md
(+ DEVIATIONS D1: BSGS solver, deterministic op-count; D2: small model curves).

Question: does a CARRY-PARTITION-guided interval-DLP solver cost fewer group operations than a plain
interval solver, and does any reduction GROW with the interval bit-length k? Model scale, ZERO secp power.

Three arms, same BSGS engine (group-op count = # EC point additions), on a j=0/mu6 model curve:
  BASELINE : BSGS over the whole interval I=[2^(k-1),2^k).
  VARIANT  : PUBLIC carry partition only -- search the eps-classes in descending prior-mass order, run by
             run, until d is found. NEVER reads eps(d_target). (non-oracle)
  ORACLE   : firing control -- GIVEN the run containing d, BSGS on that run (must fire: ratio sqrt(w_run/|I|)).

Signal path exact int; op-counts are integers; ratios are Fractions. No float in the signal path
(check_no_float.sh must pass). Not the CLOSED lambda-fold (RESULT_curve_island_lambda_folding): all search
stays inside I, no orbit-identification.
"""
import sys, os, math, random, statistics
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model_curve_infra_v1 as M

# ============================ GLV lattice / eps / partition (ported to (n,lam)) ===
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
    """Full list of contiguous integer runs (lo, hi, epsval) partitioning [2^(k-1), 2^k)."""
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
                v = lat.eps(pts[i])
                assert lat.eps(pts[i + 1] - 1) == v      # constancy on the elementary run
                runs.append((pts[i], pts[i + 1], v))
        x = y
    merged = []                                          # merge adjacent equal-eps runs
    for (a0, a1, v) in runs:
        if merged and merged[-1][2] == v and merged[-1][1] == a0:
            merged[-1] = (merged[-1][0], a1, v)
        else:
            merged.append((a0, a1, v))
    return merged

# ============================ counting EC ops ================================
class Ctr:
    __slots__ = ("ops",)
    def __init__(self): self.ops = 0

def cadd(curve, Pt, Qt, ctr):
    ctr.ops += 1
    return curve.add(Pt, Qt)

def cmul(curve, k, Pt, ctr):
    if Pt is None or k == 0: return None
    if k < 0: k, Pt = -k, curve.neg(Pt)
    R = None; Q = Pt
    while k:
        if k & 1: R = cadd(curve, R, Q, ctr)
        Q = cadd(curve, Q, Q, ctr)
        k >>= 1
    return R

def bsgs(curve, G, P, lo, hi, ctr):
    """Solve [d]G==P with d in [lo,hi); return d or None. Counts EC adds into ctr."""
    w = hi - lo
    if w <= 0: return None
    m = M.isqrt(w - 1) + 1                                # ceil(sqrt(w))
    Plo = cmul(curve, lo, G, ctr)
    Q = cadd(curve, P, curve.neg(Plo), ctr) if Plo is not None else P   # [d-lo]G
    table = {}; cur = None                               # baby: {[j]G: j}
    for j in range(m):
        if cur not in table: table[cur] = j
        cur = cadd(curve, cur, G, ctr)
    mG = cmul(curve, m, G, ctr); neg_mG = curve.neg(mG)
    giant = Q; imax = (w - 1) // m
    for i in range(imax + 1):
        j = table.get(giant)
        if j is not None:
            dprime = i * m + j
            if 0 <= dprime < w:
                return lo + dprime
        giant = cadd(curve, giant, neg_mG, ctr)
    return None

# ============================ arms ===========================================
def arm_baseline(curve, G, P, k, ctr):
    return bsgs(curve, G, P, 2 ** (k - 1), 2 ** k, ctr)

def arm_oracle(curve, G, P, d, runs, ctr):
    for (lo, hi, v) in runs:                              # the run containing d (firing control)
        if lo <= d < hi:
            return bsgs(curve, G, P, lo, hi, ctr)
    return None

def arm_variant(curve, G, P, runs, ctr):
    # classes ordered by descending total width (prior mass); search run by run until found
    from collections import defaultdict
    cls = defaultdict(list); width = defaultdict(int)
    for (lo, hi, v) in runs:
        cls[v].append((lo, hi)); width[v] += hi - lo
    order = sorted(cls.keys(), key=lambda v: -width[v])
    for v in order:
        for (lo, hi) in cls[v]:
            r = bsgs(curve, G, P, lo, hi, ctr)
            if r is not None:
                return r
    return None

# ============================ validation =====================================
def validate():
    print("== validation ==")
    # V3: ported glv/eps reproduce t2c on secp (n,lam)
    N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
    import t2c_range_glv_structure_v1 as orig
    lat = Lattice(N_SECP, LAM); random.seed(7); ok = True
    for _ in range(500):
        d = random.randrange(1, N_SECP)
        if lat.glv(d) != orig.glv(d) or lat.eps(d) != orig.eps(d): ok = False; break
    print(f"  [V3] ported glv/eps == t2c_range_glv_structure_v1 on 500 secp d: {ok}")
    assert ok
    return True

# ============================ curve setup ====================================
def make_arm(q):
    a = M.select_j0_prime_order(q, exclude_anomalous=True)
    if a is None: return None
    curve = M.Curve(a.q, 0, a.B)
    lat = Lattice(a.N, a.lam)
    return dict(q=a.q, B=a.B, n=a.N, beta=a.beta, lam=a.lam, G=(a.Gx, a.Gy), curve=curve, lat=lat)

def select_ks(lat, nbits):
    Ps = {}
    for k in range(4, nbits + 1):
        runs = partition_runs(lat, k)
        ones = sum(hi - lo for (lo, hi, v) in runs if v == 1)
        tot = 2 ** (k - 1)
        Ps[k] = (Fraction(ones, tot), runs)
    def dev(k): return abs(Ps[k][0] - Fraction(1, 2))
    ks = sorted(Ps)
    k_strong = max(ks, key=dev)
    # weak = largest k with |P-1/2| < 1/100 (fallback: smallest dev)
    weak_cand = [k for k in ks if dev(k) < Fraction(1, 100)]
    k_weak = max(weak_cand) if weak_cand else min(ks, key=dev)
    mid_cand = [k for k in ks if k > k_strong]
    k_mid = min(mid_cand, key=lambda k: abs(dev(k) - Fraction(1, 10))) if mid_cand else k_strong
    chosen = sorted(set([k_strong, k_mid, k_weak,
                         (k_strong + k_weak) // 2, (k_strong + k_mid) // 2]))
    chosen = [k for k in chosen if 6 <= k <= nbits]
    return chosen, Ps

# ============================ main bench ======================================
def run(qs, T, seed=20260826):
    validate()
    print(f"\n== T2c carry-partition BSGS benchmark  T={T} draws/k  (BASELINE vs VARIANT; ORACLE=firing control) ==")
    for q in qs:
        arm = make_arm(q)
        if arm is None:
            print(f"  q={q}: no j=0 prime-order curve"); continue
        n = arm["n"]; nbits = n.bit_length(); lat = arm["lat"]; curve = arm["curve"]; G = arm["G"]
        ks, Ps = select_ks(lat, nbits)
        print(f"\n curve q={arm['q']} B={arm['B']} n={n} (~2^{nbits}) beta={arm['beta']} lam~{arm['lam']}")
        print(f"   k-schedule {ks}")
        rng = random.Random(seed + q)
        for k in ks:
            Pk, runs = Ps[k]
            lo, hi = 2 ** (k - 1), 2 ** k
            nruns = len(runs)
            base_ops = []; var_ops = []; orc_ops = []
            for _ in range(T):
                d = rng.randrange(lo, hi)
                P = curve.mul(d, G)
                cb = Ctr(); rb = arm_baseline(curve, G, P, k, cb); assert rb == d, (k, d, rb)
                cv = Ctr(); rv = arm_variant(curve, G, P, runs, cv); assert rv == d
                co = Ctr(); ro = arm_oracle(curve, G, P, d, runs, co); assert ro == d
                base_ops.append(cb.ops); var_ops.append(cv.ops); orc_ops.append(co.ops)
            mb = statistics.median(base_ops); mv = statistics.median(var_ops); mo = statistics.median(orc_ops)
            Rk = Fraction(int(mv), int(mb)); Ro = Fraction(int(mo), int(mb))
            # ceiling: oracle-class prediction Pk^1.5+(1-Pk)^1.5 (as a display float via isqrt-free note)
            pf = float(Pk)                                                # noqa: float (display of exact Pk)
            ceil_cls = pf ** 1.5 + (1 - pf) ** 1.5                        # noqa: float (display)
            print(f"   k={k:3d} P_k={pf:.4f} runs={nruns:4d} | base={int(mb):>8} var={int(mv):>9} "  # noqa: float
                  f"orc={int(mo):>8} | R_k(var)={float(Rk):.3f} R(orc)={float(Ro):.3f} "             # noqa: float
                  f"[class-ceil~{ceil_cls:.3f}]")                                                     # noqa: float

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[1 << 20, 1 << 23])
    ap.add_argument("--T", type=int, default=150)
    a = ap.parse_args()
    # snap qs to a prime q == 1 mod 3 at/above the target (j=0 needs q==1 mod3)
    qs = []
    for q0 in a.qs:
        q = q0 | 1
        while not (q % 3 == 1 and M.is_prime(q)):
            q += 2
        qs.append(q)
    run(qs, a.T)
