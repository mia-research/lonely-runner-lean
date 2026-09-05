#!/usr/bin/env python3
"""
glv_crossterm_seam_probe_v1.py

The additive-correction ratio |V|^2/Sum|U|^2 ~ 1.0 came from the cross term
  B(U_sum, U1+U2)  (Eisenstein bilinear form)  averaging to ZERO
i.e. U_sum is directionally independent of U1+U2. Probe: is there a DIRECTIONAL
conditioning under which the normalized cross term (cosine) is systematically
nonzero -- a directional seam where the group law partially aligns in the lift?

Condition the cosine on sextant(U1+U2) and on (sextant U1, sextant U2). Per-cell
mean cosine with z = mean/(sd/sqrt(count)); |z|>~3 in a cell = a directional tilt.
Exact-integer bilinear form B and norms; sqrt only in the reported cosine statistic.
p=100003 (universal lift geometry).
"""
import math, random
from collections import defaultdict
from sympy.ntheory.residue_ntheory import sqrt_mod
from glv_addition_correction_eps_conditioned_v1 import make, add_curve
from lift_sextant_rhombus_law_proof_v2 import enorm

P = 100003


def sextant(u, v):
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3


def B(x, y):
    # symmetric Eisenstein bilinear form with B(x,x)=enorm(x); 2B is integer
    return (2 * x[0] * y[0] - x[0] * y[1] - x[1] * y[0] + 2 * x[1] * y[1])  # = 2*B


def main():
    eis, eps = make(P)
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

    rng = random.Random(99)
    NPAIR = 60000
    recs = []   # (s12, s1, s2, cos)
    allcos = []
    for _ in range(NPAIR):
        a = rng.randrange(1, n + 1); b = rng.randrange(1, n + 1)
        Ps = add_curve(pts[a], pts[b], P)
        if Ps is None: continue
        Us = eis(Ps[0]); U1 = U[a]; U2 = U[b]
        W = (U1[0] + U2[0], U1[1] + U2[1])
        nW = enorm(W); nS = enorm(Us)
        if nW == 0 or nS == 0: continue
        cos = B(Us, W) / (2 * math.sqrt(nS * nW))   # 2B/(2 sqrt) = cosine
        recs.append((sextant(*W), sextant(*U1), sextant(*U2), cos))
        allcos.append(cos)
    M = len(recs)
    gm = sum(allcos) / M
    gsd = (sum((c - gm) ** 2 for c in allcos) / M) ** 0.5
    print(f"p={P}, M={M}")
    print(f"GLOBAL mean cosine = {gm:+.5f}  (predict 0 for directional independence)  "
          f"sd={gsd:.4f}  z={gm/(gsd/M**0.5):+.2f}")

    # by sextant(U1+U2)
    g = defaultdict(list)
    for s12, s1, s2, c in recs: g[s12].append(c)
    print("\n  mean cosine by sextant(U1+U2):")
    worst = 0.0
    for s in sorted(g):
        arr = g[s]; m = sum(arr) / len(arr)
        sd = (sum((x - m) ** 2 for x in arr) / len(arr)) ** 0.5
        z = m / (sd / len(arr) ** 0.5)
        worst = max(worst, abs(z))
        print(f"    s(U1+U2)={s}: n={len(arr):>6} mean={m:+.5f} z={z:+.2f}")

    # by (sextant U1, sextant U2) -- 36 cells, report the extreme |z|
    g2 = defaultdict(list)
    for s12, s1, s2, c in recs: g2[(s1, s2)].append(c)
    zs = []
    for k, arr in g2.items():
        if len(arr) < 200: continue
        m = sum(arr) / len(arr); sd = (sum((x - m) ** 2 for x in arr) / len(arr)) ** 0.5
        zs.append((m / (sd / len(arr) ** 0.5), k, m, len(arr)))
    zs.sort(key=lambda t: -abs(t[0]))
    print("\n  (sextant U1, sextant U2) cells with largest |z| (of 36):")
    for z, k, m, nn in zs[:4]:
        print(f"    (s1,s2)={k}: n={nn} mean={m:+.5f} z={z:+.2f}")
    print(f"\n  worst single-sextant |z| = {worst:.2f}; worst pair-cell |z| = {abs(zs[0][0]):.2f}")
    print("  (all |z|<~3 => no directional tilt found at sextant resolution; the cross")
    print("   term stays zero-mean under directional conditioning. >~4 stable = a seam.)")


if __name__ == "__main__":
    main()
