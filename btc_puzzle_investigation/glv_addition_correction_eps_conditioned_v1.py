#!/usr/bin/env python3
"""
glv_addition_correction_eps_conditioned_v1.py

Probe (user): for random d1,d2, the raw additive correction in the lift
   V = eis(x([d1+d2]G)) - ( eis(x([d1]G)) + eis(x([d2]G)) )   in Z[omega]
conditioned on the mu3-orbit label eps (0=core / +-=flap) of the three points.
Hypothesis: addition is "more linear" (smaller correction) when points are in the
mu3-core.

CONFOUND (stated up front): eps=0 (core) <=> eis(X) in the LOW-norm central region
(norm-band law: core s<3/16), eps=+- <=> high-norm. So core points are smaller
vectors, and |V|^2 will be smaller in the core TRIVIALLY (smaller inputs), not
necessarily "more linear". So we report BOTH:
  (raw)   mean |V|^2 / p                         -- will move with point magnitude
  (scale) mean |V|^2 / (|U1|^2+|U2|^2+|Usum|^2)  -- scale-INVARIANT linearity measure
The hypothesis "more linear in core" is supported ONLY if the SCALE-invariant ratio
drops with #core; if only the raw norm drops, that is the magnitude confound.

Also: distinct/top-mass of V per (eps1,eps2,epssum) cell (does V concentrate?), and
a label-permutation control (does eps carry info about V beyond magnitude?).
All norms exact integers; group means are ratios of exact integer sums.

Primary testbed p=100003 (universal geometry, full group, large N); secp headline
confirmation at smaller N.
"""
import random
from collections import Counter, defaultdict
from fractions import Fraction as F
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm
from glv_fundamental_domain_law_v1 import cube_roots


def make(p, R1=None, R2=None):
    if R1 is None:
        R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    R1t, R2t = tuple(R1), tuple(R2)
    b1, b2 = cube_roots(p)

    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def om2(w):
        u, v = w
        return (v - u, -u)

    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET)
        c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2

    def eps(X):
        U0 = eis(X); U1 = eis((beta * X) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 0
        if c == R1t or c == R2t: return 1
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]): return -1
        return 2
    return eis, eps


def add_curve(P1, P2, p):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1; x2, y2 = P2
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def report(name, samples):
    """samples: list of (eps1,eps2,epssum, |V|^2, denom=|U1|^2+|U2|^2+|Usum|^2, V)."""
    M = len(samples)
    print(f"\n=== {name}  (M={M}) ===")
    p_ref = samples[0][6]

    def group_stats(keyfn):
        g = defaultdict(lambda: [0, 0, 0])  # [count, sum|V|^2, sum denom]
        for e1, e2, es, vn, dn, V, p in samples:
            k = keyfn(e1, e2, es)
            g[k][0] += 1; g[k][1] += vn; g[k][2] += dn
        return g

    # (1) raw |V|^2/p and scale-invariant ratio, by #core among the 3 points
    print("  by #core (points with eps=0) among {P1,P2,Psum}:")
    print(f"    {'#core':>5} {'count':>7} {'mean|V|^2/p':>12} {'scale-inv |V|^2/Σ|U|^2':>22}")
    g = group_stats(lambda e1, e2, es: sum(1 for e in (e1, e2, es) if e == 0))
    for k in sorted(g):
        cnt, sv, sd = g[k]
        raw = float(F(sv, cnt * p_ref))
        sci = float(F(sv, sd)) if sd else 0.0
        print(f"    {k:>5} {cnt:>7} {raw:>12.4f} {sci:>22.4f}")
    print("    (hypothesis 'more linear in core' => scale-inv ratio DROPS as #core rises;")
    print("     if only mean|V|^2/p drops, that is the magnitude confound)")

    # (2) by eps_sum alone
    print("  by eps_sum (class of the SUM point):")
    g = group_stats(lambda e1, e2, es: es)
    for k in sorted(g):
        cnt, sv, sd = g[k]
        print(f"    eps_sum={k:>2}: count={cnt:>7} mean|V|^2/p={float(F(sv,cnt*p_ref)):.4f} "
              f"scale-inv={float(F(sv,sd)) if sd else 0:.4f}")

    # (3) per (eps1,eps2,eps_sum) cell: distinct/top-mass of V (concentration?)
    cells = defaultdict(Counter)
    for e1, e2, es, vn, dn, V, p in samples:
        cells[(e1, e2, es)][V] += 1
    tops = sorted(((max(c.values()) / sum(c.values()), k, len(c), sum(c.values()))
                   for k, c in cells.items() if sum(c.values()) >= 100), reverse=True)
    print("  per-cell V concentration (top-mass, distinct, n) -- best 3 cells:")
    for tm, k, dist, n in tops[:3]:
        print(f"    eps={k}: top-mass={tm:.5f} distinct={dist} n={n}")
    print(f"    (top-mass ~ 1/n everywhere => V spread in every class; >0.05 => concentration)")


def main():
    P = 100003
    eis, eps = make(P)
    # precompute
    G = None
    for x in range(1, P):
        rhs = (x * x * x + 7) % P
        if pow(rhs, (P - 1) // 2, P) == 1:
            y = sqrt_mod(rhs, P)
            if y: G = (x, int(y)); break
    pts = [None, G]; cur = G
    while True:
        cur = add_curve(cur, G, P)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    U = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    E = [None] + [eps(pts[k][0]) for k in range(1, n + 1)]

    rng = random.Random(2718281)
    samples = []
    NPAIR = 60000
    for _ in range(NPAIR):
        a = rng.randrange(1, n + 1); b = rng.randrange(1, n + 1)
        Ps = add_curve(pts[a], pts[b], P)
        if Ps is None: continue
        Us = eis(Ps[0]); es = eps(Ps[0])
        V = (Us[0] - U[a][0] - U[b][0], Us[1] - U[a][1] - U[b][1])
        vn = enorm(V)
        dn = enorm(U[a]) + enorm(U[b]) + enorm(Us)
        samples.append((E[a], E[b], es, vn, dn, V, P))
    report(f"p={P}", samples)

    # scale-invariant control: shuffle eps labels vs V, does #core->ratio survive?
    print("\n  CONTROL: shuffle (eps1,eps2,eps_sum) triples across samples, recompute")
    print("  #core->scale-inv ratio; if the real trend vanishes under shuffle it is real,")
    print("  if it persists it was an artifact of the |U|^2 magnitude alone.")
    labs = [(s[0], s[1], s[2]) for s in samples]
    rng.shuffle(labs)
    shuf = [(labs[i][0], labs[i][1], labs[i][2], samples[i][3], samples[i][4],
             samples[i][5], samples[i][6]) for i in range(len(samples))]
    g = defaultdict(lambda: [0, 0, 0])
    for e1, e2, es, vn, dn, V, p in shuf:
        k = sum(1 for e in (e1, e2, es) if e == 0)
        g[k][0] += 1; g[k][1] += vn; g[k][2] += dn
    print(f"    {'#core':>5} {'count':>7} {'scale-inv (shuffled labels)':>28}")
    for k in sorted(g):
        cnt, sv, sd = g[k]
        print(f"    {k:>5} {cnt:>7} {float(F(sv, sd)) if sd else 0:>28.4f}")


if __name__ == "__main__":
    main()
