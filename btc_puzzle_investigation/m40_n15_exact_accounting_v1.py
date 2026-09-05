#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
m40_n15_exact_accounting_v1.py — the FIRST statistics projecting onto M40's forced mu3-invariant
subspace, + the N15 joint-readout budget — exact, total enumeration, no sampling (small p).

Objects (public functions of Q = [d]G, exact integer computation):
  f(d) = chi2(y_{[d]G})           — the M40 sign sequence (y-parity readout)
  e(d) = Eisenstein flap class    — 0 (core |u-v|<=1/2) / + / -  (build.eps's 3 classes)
  sext(d) = sextant of the lift   — 6 sectors of the Eisenstein torus cell
  band(d) = s-band                — s<3/16 / 3/16<=s<1/4 / s>=1/4

Computations:
  A1  orbit-constancy h[lam d]==h[d] (all d; lam order-3) — M40 re-verified, 8 primes both arms
  A2  antisymmetry h[-d] == leg*h[d] (p=3 mod 4) — sharpens M40: free signs = (n-1)/6 (mu6 domain)
  A3  exact class sizes + H(f) + posterior support (the honest "worth" of knowing f(D))
  A4  PAIRWISE SUM INTERACTION: MI( f(d1+d2) ; (f(d1), f(d2)) ) exactly over all (d1,d2) in [1,n)^2
      — the first group-law statistic ON the forced subspace (M40's "no statistic projects onto it")
  B1  exact entropies H(e), H(sext), H(band), H(f), all joints, the tuple
  B2  MI(d; tuple) = H(tuple) (deterministic readouts) — the FREE pruning budget, exact
  B3  synergy: H(tuple) - sum of marginals; per-cell sizes (min/max) — is the joint cell structure
      more than the product of parts?
Deterministic first pass per ROADMAP_REDIRECT_v3 (no leakage claim; counts exact, floats only for
display of entropies).
"""
import math, sys, os
from fractions import Fraction
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# ---------------- minimal exact EC + Eisenstein lift (same as ideation_claims_firsthand_v1) ----------------

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def tonelli(a, p):
    a %= p
    if a == 0: return 0
    if legendre(a, p) != 1: return None
    if p % 4 == 3: return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r

def curve_walk(p, B=7):
    """h[d]=chi2(y_{[d]G}), xs[d]=x_{[d]G} for d in [0,n); n prime."""
    n = p + 1 + sum(legendre((x * x % p * x + B) % p, p) for x in range(p))
    G = None
    for x in range(p):
        y = tonelli((x * x % p * x + B) % p, p)
        if y: G = (x, y); break
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        if P == Q:
            m = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
        else:
            m = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (m * m - x1 - x2) % p
        return (x3, (m * (x1 - x3) - y1) % p)
    h = [0] * n; xs = [None] * n
    Q = None
    for d in range(n):
        if Q is not None:
            h[d] = legendre(Q[1], p); xs[d] = Q[0]
        Q = add(Q, G)
    assert Q is None
    return n, h, xs

def qform(U, V): return U * U - U * V + V * V
def ip2(u, v): return 2*u[0]*v[0] - u[0]*v[1] - u[1]*v[0] + 2*u[1]*v[1]
def gauss_reduce_q(b1, b2):
    while True:
        if qform(*b2) < qform(*b1): b1, b2 = b2, b1
        num, den = ip2(b1, b2), 2 * qform(*b1)
        mu = (2 * num + den) // (2 * den)
        if mu == 0: return b1, b2
        b2 = (b2[0] - mu * b1[0], b2[1] - mu * b1[1])

class Lift:
    def __init__(self, p):
        self.p = p
        for c in range(2, 1000):
            w = pow(c, (p - 1) // 3, p)
            if w != 1:
                self.w0 = w; break
        v1 = (p, 0); v2 = ((-self.w0) % p, 1)
        self.b1, self.b2 = gauss_reduce_q(v1, v2)
    def lift(self, x):
        p = self.p
        det = self.b1[0] * self.b2[1] - self.b2[0] * self.b1[1]
        r1 = round(Fraction(x * self.b2[1], det))
        r2 = round(Fraction(-x * self.b1[1], det))
        best = None
        for d1 in range(-2, 3):
            for d2 in range(-2, 3):
                a1, a2 = r1 + d1, r2 + d2
                U = x - a1 * self.b1[0] - a2 * self.b2[0]
                V = - a1 * self.b1[1] - a2 * self.b2[1]
                key = (max(abs(U), abs(V)), qform(U, V))
                if best is None or key < best[0]:
                    best = (key, U, V)
        return best[1], best[2]

def readouts(U, V, p):
    """(e_class, sextant, band) from the exact lift; e in {0,+,-}, sext in 0..5, band in 0..2."""
    s_num = qform(U, V)
    if 4 * (U - V) ** 2 <= p:
        e = 0
    else:
        e = 1 if (U - V) > 0 else 2
    # sextant: sector of angle in the Eisenstein metric, 60-degree sectors from (u,v) coords
    # use the three hexagon "coordinates" u, v, u-v to fix the sector exactly (integer compare)
    a1, a2, a3 = U, V, U - V
    sext = 0
    if a1 >= 0 and a2 >= 0: sext = 0        # between axes u+ and v+
    elif a1 >= 0 and a3 >= 0: sext = 1      # u+ side toward u-v+
    elif a3 >= 0 and a2 < 0: sext = 2
    elif a1 < 0 and a2 < 0: sext = 3
    elif a1 < 0 and a3 < 0: sext = 4
    else: sext = 5
    if 16 * s_num < 3 * p: band = 0
    elif 4 * s_num < p: band = 1
    else: band = 2
    return e, sext, band

def H_bits(counter, N):
    h = 0.0
    for c in counter.values():
        if c:
            f_ = c / N
            h -= f_ * math.log2(f_)
    return h

def main():
    primes = [(43, "7"), (67, "7"), (79, "7"), (127, "7"), (163, "7"), (211, "7"),
              (349, "1"), (61, "1-anom")]
    print("=" * 104)
    print(" M40 forced-subspace statistics (first on record) + N15 joint budget — EXACT total enumeration")
    print("=" * 104)
    for (p, arm) in primes:
        n, h, xs = curve_walk(p)
        L = Lift(p)
        leg = 1 if p % 4 == 1 else -1
        lam = None
        for g in range(2, n):
            if pow(g, 3, n) == 1 and g != 1:
                lam = g; break
        # A1 orbit constancy
        ok_A1 = all(h[(lam * d) % n] == h[d] for d in range(n))
        # A2 antisymmetry
        ok_A2 = all(h[(-d) % n] == leg * h[d] for d in range(n))
        # free-sign count on mu6 fundamental domain
        seen = set(); free = 0
        for d in range(1, n):
            orb = frozenset({d % n, (lam * d) % n, (lam * lam * d) % n,
                             (-d) % n, (-lam * d) % n, (-lam * lam * d) % n})
            if orb not in seen:
                seen.add(orb); free += 1
        # A3 exact class sizes
        cp = sum(1 for d in range(1, n) if h[d] == 1)
        cm = sum(1 for d in range(1, n) if h[d] == -1)
        assert cp + cm == n - 1
        Hf = H_bits({1: cp, -1: cm}, n - 1)
        worth = -math.log2(max(cp, cm) / (n - 1))       # best-case posterior pruning from f(D)
        # A4 pairwise sum interaction: exact over all (d1,d2) in [1,n)^2
        N2 = (n - 1) ** 2
        c_joint = Counter()   # (f(s), f(d1), f(d2))
        c_s = Counter(); c_p = Counter()
        for d1 in range(1, n):
            f1 = h[d1]
            for d2 in range(1, n):
                fs = h[(d1 + d2) % n]
                f2 = h[d2]
                c_joint[(fs, f1, f2)] += 1
                c_s[fs] += 1; c_p[(f1, f2)] += 1
        # MI(f(s); (f1,f2)) exact
        MI = 0.0
        for (fs, f1, f2), c in c_joint.items():
            MI += c / N2 * math.log2((c * N2) / (c_s[fs] * c_p[(f1, f2)]))
        # B: tuple readouts
        ce = Counter(); cs = Counter(); cb = Counter()
        cj_es = Counter(); cj_ef = Counter(); cj_sf = Counter(); cj_all = Counter()
        cell = {}
        for d in range(1, n):
            U, V = L.lift(xs[d])
            e, sext, band = readouts(U, V, p)
            f_ = h[d]
            ce[e] += 1; cs[sext] += 1; cb[band] += 1
            cj_es[(e, sext)] += 1; cj_ef[(e, f_)] += 1; cj_sf[(sext, f_)] += 1
            cj_all[(e, sext, band, f_)] += 1
            cell.setdefault((e, sext, band, f_), []).append(d)
        N = n - 1
        He, Hs, Hb = H_bits(ce, N), H_bits(cs, N), H_bits(cb, N)
        Hes, Hef, Hsf = H_bits(cj_es, N), H_bits(cj_ef, N), H_bits(cj_sf, N)
        Hall = H_bits(cj_all, N)
        sizes = [len(v) for v in cell.values()]
        print(f" p={p:>3} n={n:>3} [mod12={arm}] lam={lam}")
        print(f"   A1 mu3-constancy {ok_A1} | A2 antisym h(-d)=leg*h(d) {ok_A2} | "
              f"mu6 free signs = {free} (=(n-1)/6? {free == (n-1)//6})")
        print(f"   A3 classes +:{cp} -:{cm}  H(f)={Hf:.4f} b | posterior worth of f(D) = {worth:.4f} b "
              f"(=1b if balanced)")
        print(f"   A4 MI(f(d1+d2) ; f(d1),f(d2)) = {MI:.6f} bits over all {N2} pairs "
              f"({'FLAT (<= noise 1e-3)' if MI < 1e-3 else 'NONZERO - group-law coupling!'})")
        print(f"   B H(e)={He:.4f} H(sext)={Hs:.4f} H(band)={Hb:.4f} H(f)={Hf:.4f} | "
              f"joints: e+sext {Hes:.4f} e+f {Hef:.4f} sext+f {Hsf:.4f}")
        print(f"   B TUPLE(e,sext,band,f): H={Hall:.4f} bits (the FREE pruning budget; MI(d;tuple) same) "
              f"| synergy vs sum {Hall - (He + Hs + Hb + Hf):+.4f}")
        print(f"     cells: {len(cell)} | min {min(sizes)} max {max(sizes)} of N={N} "
              f"| max-cell pruning {math.log2(N / max(sizes)):.4f} b")
    print("=" * 104)

if __name__ == "__main__":
    main()
