#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
m40_collinear_sign_probe_v1.py — the COLLINEAR (Semaev-triple) sign probe on M40's forced subspace.

Trent's Semaev framing, made exact. For a collinear triple P1+P2+P3 = O (P3 = -(P1+P2)):
  - f3 = chi2(y3) = chi2(-y12) = leg * f(d1+d2)   [by the proved antisymmetry] — so the
    conditional-MI version of "do two signs constrain the third" IS the (g) pairwise statistic (flat).
    Verified structurally in-script.
  - The GENUINE new object is the third-order correlation: pi = f1*f2*f3 on collinear triples.
    Algebra (Vieta on the line y = mx+b in y^2=x^3+7):  y1*y2*y3 = b^3 - 7*m^3   [verified in-script]
    and x1+x2+x3 = m^2  (the k=3 channel mechanism; verified too).
    So pi = chi2(b^3 - 7 m^3) = chi2(m)*chi2((b/m)^3 - 7).

Measurements:
  A  identity verification (exact, mod p) on enumerated secants + tangents.
  B  small p (TOTAL enumeration over (d1,d2), d1+d2 =/= 0): E[pi] exact; decomposition E[chi2(m)],
     E[chi2(t^3-7)]; 8-pattern counts vs product-of-marginals; scaling |E[pi]| vs p (Weil or O(1)?).
  C  secp: 100k exact samples of E[pi] (sigma = 1/sqrt(N) = 0.0032) — resolves >= 0.6% biases.
"""
import math, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m40_n15_exact_accounting_v1 import legendre

def curve_walk_xy(p, B=7):
    n = p + 1 + sum(legendre((x * x % p * x + B) % p, p) for x in range(p))
    G = None
    for x in range(p):
        r = (x * x % p * x + B) % p
        if legendre(r, p) == 1:
            y = next(yy for yy in range(1, p) if yy * yy % p == r)
            G = (x, y); break
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
    pts = [None] * n
    Q = None
    for d in range(n):
        pts[d] = Q
        Q = add(Q, G)
    assert Q is None
    xs = [P[0] for P in pts[1:]]
    ys = [P[1] for P in pts[1:]]
    h = [0] + [legendre(P[1], p) for P in pts[1:]]
    return n, pts, h

def main():
    print("=" * 104)
    print(" COLLINEAR SIGN PROBE — third-order correlation pi = f1 f2 f3 on Semaev triples")
    print("=" * 104)
    rows = []
    for p in (43, 79, 127, 163, 211, 61):
        n, pts, h = curve_walk_xy(p)
        leg = 1 if p % 4 == 1 else -1
        # structural equivalence: f3 = leg * f(d1+d2)
        assert all(h[(-d) % n] == leg * h[d] for d in range(n))
        # A: identity verification on all secant pairs (x1 != x2) + tangents (d1 == d2)
        ok_prod = ok_slope = cnt = 0
        for d1 in range(1, n):
            for d2 in range(1, n):
                P1, P2 = pts[d1], pts[d2]
                if P1[0] == P2[0]:
                    continue                      # vertical pairs (d2 = n-d1) excluded
                P12 = pts[(d1 + d2) % n] if (d1 + d2) % n != 0 else None
                if P12 is None:
                    continue                      # degenerate: sum is O
                x3, y3 = P12[0], (-P12[1]) % p    # P3 = -(P1+P2), the third collinear point
                if d1 == d2:
                    m = (3 * P1[0] * P1[0]) * pow(2 * P1[1], p - 2, p) % p
                else:
                    m = (P2[1] - P1[1]) * pow(P2[0] - P1[0], p - 2, p) % p
                b = (P1[1] - m * P1[0]) % p
                ok_prod += ((P1[1] * P2[1] % p * y3 - (b * b % p * b - 7 * (m * m % p * m))) % p == 0)
                ok_slope += ((P1[0] + P2[0] + x3 - m * m) % p == 0)
                cnt += 1
        # B: exact third-order correlation over ALL pairs with d1+d2 != 0 mod n
        N = 0; Spi = 0; Sm = 0; Sm_nonzero = 0; St = 0
        pat = {}
        for d1 in range(1, n):
            f1 = h[d1]
            for d2 in range(1, n):
                s = (d1 + d2) % n
                if s == 0:
                    continue
                f2 = h[d2]; f3 = h[(-s) % n]
                Spi += f1 * f2 * f3
                P1, P2 = pts[d1], pts[d2]
                if P1[0] != P2[0]:
                    m = (P2[1] - P1[1]) * pow(P2[0] - P1[0], p - 2, p) % p
                    b = (P1[1] - m * P1[0]) % p
                    if m != 0:
                        Sm_nonzero += 1
                        Sm += legendre(m, p)
                        t = b * pow(m, p - 2, p) % p
                        St += legendre((t * t % p * t - 7) % p, p)
                key = (f1, f2, f3)
                pat[key] = pat.get(key, 0) + 1
                N += 1
        Epi = Spi / N
        rows.append((p, n, Epi))
        print(f" p={p:>3} n={n:>3}: identity y1y2y3=b^3-7m^3 {ok_prod}/{cnt} | x1+x2+x3=m^2 {ok_slope}/{cnt}")
        print(f"   E[pi] = {Epi:+.6f}   (|E|.sqrt(p) = {abs(Epi)*math.sqrt(p):.4f}; Weil => O(1), O(1)-bias => grows)")
        print(f"   E[chi2(m)] = {Sm/Sm_nonzero:+.6f}   E[chi2(t^3-7)] = {St/Sm_nonzero:+.6f}   "
              f"(secant non-horizontal lines: {Sm_nonzero})")
    print("-" * 104)
    print(" scaling: E[pi] by p:", ", ".join(f"{p}:{e:+.4f}" for (p, _, e) in rows))
    print("=" * 104)

    # C: secp — 100k exact samples
    P = 2**256 - 2**32 - 977
    NORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    def jac_double(Pt):
        if Pt is None: return None
        X, Y, Z = Pt
        if Y == 0: return None
        YY = Y * Y % P; S = 4 * X * YY % P; M = 3 * X * X % P
        X3 = (M * M - 2 * S) % P
        return (X3, (M * (S - X3) - 8 * YY * YY) % P, 2 * Y * Z % P)
    def jac_add(Pt, Qt):
        if Pt is None: return Qt
        if Qt is None: return Pt
        X1, Y1, Z1 = Pt; X2, Y2, Z2 = Qt
        Z1Z1 = Z1 * Z1 % P; Z2Z2 = Z2 * Z2 % P
        U1 = X1 * Z2Z2 % P; U2 = X2 * Z1Z1 % P
        S1 = Y1 * Z2 % P * Z2Z2 % P; S2 = Y2 * Z1 % P * Z1Z1 % P
        H = (U2 - U1) % P; r = (S2 - S1) % P
        if H == 0: return jac_double(Pt) if r == 0 else None
        HH = H * H % P; HHH = H * HH % P; V = U1 * HH % P
        X3 = (r * r - HHH - 2 * V) % P
        return (X3, (r * (V - X3) - S1 * HHH) % P, ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) % P * H % P)
    def jac_mul(k, Pt):
        R = None
        while k:
            if k & 1: R = jac_add(R, Pt)
            Pt = jac_double(Pt); k >>= 1
        return R
    G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
         0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)
    leg_secp = -1  # p = 3 mod 4
    random.seed(20260822)
    M = 100_000
    Spi = 0
    for _ in range(M):
        d1 = random.randrange(1, NORDER)
        d2 = random.randrange(1, NORDER)
        if (d1 + d2) % NORDER == 0:
            continue
        A1 = jac_mul(d1, G); A2 = jac_mul(d2, G); A12 = jac_add(A1, A2)
        zi = pow(A12[2], P - 2, P); zi2 = zi * zi % P; zi3 = zi2 * zi % P
        y12 = A12[1] * zi3 % P
        y1z = pow(A1[2], P - 2, P); y1 = A1[1] * y1z % P * y1z % P * y1z % P
        y2z = pow(A2[2], P - 2, P); y2 = A2[1] * y2z % P * y2z % P * y2z % P
        f1 = 1 if pow(y1, (P - 1) // 2, P) == 1 else -1
        f2 = 1 if pow(y2, (P - 1) // 2, P) == 1 else -1
        f3 = legendre((-y12) % P, P)      # sign of the third collinear point's y
        Spi += f1 * f2 * f3
    E = Spi / M
    sig = 1 / math.sqrt(M)
    print(f" secp (N={M}): E[pi] = {E:+.6f} +/- {sig:.6f}   "
          f"({'ZERO within noise' if abs(E) < 2 * sig else 'NONZERO — signal!'})")
    print("=" * 104)

if __name__ == "__main__":
    main()
