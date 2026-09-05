#!/usr/bin/env python3
"""
xy_interference_U_v1.py — the x&y INTERACTION as the complete twisted sum U, referenced
to the slippage label eps.  (User's "two intertwining parts, Frobenius/slippage as reference.")

CORE OBJECT: U(a,b,c) = sum_d e_p(b*x_d + c*y_d) * e_n(a*d),  x_d,y_d = coords of [d]G.
  * T(a,b)   = U(a,b,0)          -- x only, EVEN in a  (all prior nulls live here; closure bounds it)
  * T_y(a,b) = sum_c s^(c) U(a,b,c) -- y-sign twisted, ODD in a  (the complement half)
  So U carries BOTH halves; the b<->c coupling is the x/y interference. A shadow = info split
  across even(b)+odd(c) so neither T nor T_y shows it but U does.

TESTS:
 (1) [exact] symmetry group of U (even/odd + GLV mu_3) -- the known structure.
 (2) [derive+verify] avg_a |U(a,b,c)|^2 = n  => sqrt(n) cancellation ON AVERAGE for every (b,c).
     (underwrites T_y bounded via sawtooth, up to the max-vs-avg gap.)
 (3) [interference hunt] max_a |U(a,b,c)| over a GRID of (b,c): does COUPLING b,c ever beat
     the pure-x value (c=0)?  Especially the curve-tied diagonals c=+-b. CM vs non-CM control.
 (4) [the leak axis, v14/15] the ALIGNED joint readout in (b,c)-space vs a SEPARABLE one:
     can a NON-separable F(x,y) align where neither coordinate marginal does?
 (5) [eps-referenced] partition by slippage eps; is the b<->c coupling different on core vs flap?
     the mu_3-orbit flap-triple (sigma(x),sigma(bx),sigma(b^2x)) with common s_y.

Exact: sigma, eps, symmetry checks (integers). Float: the character-sum magnitudes |U| (roots
of unity, analytic-size, no key in path -- same carve-out as glv_closure_verification).
"""
import math
from fractions import Fraction as Fr
import numpy as np
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import find_point, padd, mul, curve_points_order, legendre, tonelli


def prime_order_curve(lo, hi, a=0, b=7):
    for q in range(lo, hi):
        if isprime(q) and q % 3 == 1:
            m = q + 1
            for x in range(q):
                m += legendre((x**3 + a * x + b) % q, q)
            if isprime(m):
                # find generator
                for x0 in range(1, q):
                    r = (x0**3 + a * x0 + b) % q
                    if legendre(r, q) == 1:
                        G = (x0, tonelli(r, q)); break
                return q, m, G
    return None


def padd_ab(P, Q, p, a):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        lam = (3 * x1 * x1 + a) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def orbit(G, p, n, acoef):
    xs = [None] * n; ys = [None] * n; acc = None
    for d in range(1, n):
        acc = padd_ab(acc, G, p, acoef); xs[d], ys[d] = acc
    return xs, ys


def U_row(xs, ys, b, c, p, n):
    idx = [d for d in range(n) if xs[d] is not None]
    ph = np.zeros(n, dtype=complex)
    ph[idx] = np.exp(2j * np.pi * ((b * np.array([xs[d] for d in idx])
                                    + c * np.array([ys[d] for d in idx])) % p) / p)
    return np.fft.fft(ph)                       # U(a,b,c) for all a


def main():
    p, n, G = prime_order_curve(700, 3000)
    print(f"CM y^2=x^3+7 / F_{p}, n={n} (prime).  Complete twisted sum U(a,b,c).")
    xs, ys = orbit(G, p, n, 0)

    # cube root + GLV
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    beta0 = pow(g, e, p); lam = beta = None
    for bb in (beta0, beta0 * beta0 % p):
        for c in [c for c in range(2, n) if pow(c, 3, n) == 1]:
            if all(xs[(c * d) % n] == (bb * xs[d]) % p for d in range(1, 25)):
                lam, beta = c, bb; break
        if lam: break

    # (1) symmetry group
    print("\n[1] symmetry group of U (exact):")
    def Uab(a, b, c): return U_row(xs, ys, b, c, p, n)[a % n]
    e1 = max(abs(Uab(-a, b, c) - Uab(a, b, -c)) for a in (1, 2, 3) for b in (1, 2) for c in (1, 2))
    e2 = max(abs(Uab(a, b, c) - Uab(a * lam % n, b * beta % p, c)) for a in (1,2) for b in (1,2) for c in (0,1))
    print(f"    U(-a,b,c) = U(a,b,-c)  [d->-d: x even, y odd]: max|diff|={e1:.2e}")
    print(f"    U(a,b,c) = U(a*lam, b*beta, c) [GLV mu_3, y fixed]: max|diff|={e2:.2e}")
    print("    => T=U(.,.,0) is EVEN in a (x-only, closure-bounded); the ODD-in-a half needs c!=0 (y).")

    # (2) average |U|^2 over a
    print("\n[2] avg_a |U(a,b,c)|^2 = n  (sqrt-n cancellation on average):")
    for (b, c) in [(1, 0), (1, 1), (3, 7), (1, -1)]:
        U = U_row(xs, ys, b, c, p, n)
        print(f"    (b,c)=({b:>2},{c:>2}): mean_a|U|^2 = {float(np.mean(np.abs(U)**2)):.1f}  (n={n})")

    # (3) interference hunt: does coupling b,c beat pure-x (c=0)?
    print("\n[3] interference hunt: max_(a!=0)|U(a,b,c)| / sqrt(n)  over a (b,c) grid")
    print("    (pure-x c=0 = T; does any coupled c!=0, esp c=+-b, exceed it?)")
    def scan(xs, ys, tag):
        rng = np.random.default_rng(0)
        bs = rng.choice(range(1, p), size=min(40, p - 1), replace=False)
        best = {}  # category -> (max ratio, (b,c))
        allratios = {"c=0 (pure x)": [], "c=+-b (diag)": [], "c generic": []}
        for b in bs:
            for c, cat in [(0, "c=0 (pure x)"), (b, "c=+-b (diag)"), ((-b) % p, "c=+-b (diag)"),
                           (int(rng.integers(1, p)), "c generic")]:
                U = U_row(xs, ys, b, c, p, n); U[0] = 0
                r = float(np.max(np.abs(U))) / math.sqrt(n)
                allratios[cat].append(r)
        for cat, rs in allratios.items():
            print(f"      [{tag}] {cat:16}: max {max(rs):.3f}  mean {np.mean(rs):.3f}  (sqrt-n units)")
    scan(xs, ys, "CM")
    nc = prime_order_curve(700, 3000, a=1, b=1)
    if nc:
        pc, ncn, Gc = nc; xc, yc = orbit(Gc, pc, ncn, 1)
        scan(xc, yc, "nonCM")

    # (4) aligned joint readout vs separable
    print("\n[4] the leak axis: does a NON-SEPARABLE joint readout align where marginals don't?")
    a0 = 1
    # build the full U(a0, b, c) matrix over (b,c); aligned joint readout Fhat(b,c)=conj(U)/|U|
    Ubc = np.zeros((p, p), dtype=complex)
    for b in range(p):
        Ubc[b, :] = np.array([U_row(xs, ys, b, c, p, n)[a0] for c in range(p)]) if p <= 250 else 0
    if p <= 250:
        nz = np.abs(Ubc) > 1e-9
        Fh = np.zeros_like(Ubc); Fh[nz] = np.conj(Ubc[nz]) / np.abs(Ubc[nz]); Fh[0, 0] = 0
        corr = abs(np.sum(Fh * Ubc)) / n
        norm_inf = float(np.sum(np.abs(Fh)))  # ||F||_1 of coeffs ~ sup of readout scale proxy
        # separable best: c=0 row only (pure x) aligned
        Fh_sep = np.zeros_like(Ubc); r0 = Ubc[:, 0]; nz0 = np.abs(r0) > 1e-9
        Fh_sep[nz0, 0] = np.conj(r0[nz0]) / np.abs(r0[nz0]); Fh_sep[0, 0] = 0
        corr_sep = abs(np.sum(Fh_sep * Ubc)) / n
        print(f"    joint-aligned |Corr|/n-units = {corr/math.sqrt(n):.3f} (sqrt-n),  "
              f"separable(x-only) = {corr_sep/math.sqrt(n):.3f}")
        print(f"    ratio joint/separable = {corr/max(corr_sep,1e-9):.2f}x "
              f"(>>1 => the COUPLING adds alignment beyond x alone; but requires knowing U)")
    else:
        print(f"    (skipped full (b,c) matrix at p={p}: too large)")

    # (5) eps-referenced mu_3-orbit flap triple x s_y
    print("\n[5] slippage-referenced interaction: flap-triple (sigma x,sigma bx,sigma b^2x) x s_y")
    eis, eps = build(p)
    R1, R2 = reduced_basis(p); R1 = tuple(R1); R2 = tuple(R2); DET = R1[0]*R2[1]-R1[1]*R2[0]
    def coeffs(z): return Fr(z[0]*R2[1]-z[1]*R2[0], DET), Fr(z[1]*R1[0]-z[0]*R1[1], DET)
    # orientation detect
    pl = sum(1 for x in range(1,p) if ((lambda uv:(uv[0]+uv[1]))(coeffs(eis(x)))>Fr(1,2) or (uv:=coeffs(eis(x)))[0]+uv[1]<-Fr(1,2))==(eps(x)!=0))
    def sg(x, plus=True):
        u,v = coeffs(eis(x)); s = u+v if plus else u-v
        return 0 if abs(s)<=Fr(1,2) else (1 if s>0 else -1)
    USE_PLUS = pl >= (p-1)/2
    sigma = lambda x: sg(x, USE_PLUS)
    # (a) sigma mu_3-invariant?  sigma(x) == sigma(beta x) for ALL x
    inv = all(sigma(x) == sigma(beta * x % p) for x in range(1, p))
    print(f"    sigma(x) == sigma(beta x) for all x: {inv}   => flap sign is mu_3-INVARIANT")
    print(f"    (with sigma(-x)=-sigma(x): sigma is the mu_2-isotypic part of the mu_6 action)")
    # (b) sigma (even in d) vs s_y (odd in d): product is ODD => sum over d is EXACTLY 0
    sig = np.array([sigma(xs[d]) for d in range(1, n)])
    sy = np.array([1 if ys[d] % 2 == 0 else -1 for d in range(1, n)])
    print(f"    sum_d sigma(x_d)*s_y(d) = {int(np.sum(sig*sy))}  (EXACTLY 0: even x odd = odd, "
          f"pairs d,n-d cancel => flap-sign and y-parity are DECORRELATED by symmetry, NO first-order coupling)")

    # (c) THE leak axis at small p: does a NON-separable joint readout F(x,y) align where marginals don't?
    print("\n[4b] aligned JOINT vs SEPARABLE readout (small p, the v14/15 leak axis):")
    ps, ns, Gs = prime_order_curve(150, 400)
    xss, yss = orbit(Gs, ps, ns, 0)
    a0 = 1
    Ubc = np.array([[U_row(xss, yss, b, c, ps, ns)[a0] for c in range(ps)] for b in range(ps)])
    def align(mask):
        Fh = np.zeros_like(Ubc); m = mask & (np.abs(Ubc) > 1e-9)
        Fh[m] = np.conj(Ubc[m]) / np.abs(Ubc[m])
        return abs(np.sum(Fh * Ubc)) / ns / math.sqrt(ns)
    full = np.ones_like(Ubc, dtype=bool); full[0, 0] = False
    sep = np.zeros_like(Ubc, dtype=bool); sep[:, 0] = True; sep[0, 0] = False   # x-only (c=0)
    print(f"    p={ps},n={ns}:  JOINT-aligned = {align(full):.3f}  SEPARABLE(x-only) = {align(sep):.3f}  "
          f"(sqrt-n units; ratio {align(full)/max(align(sep),1e-9):.2f}x)")
    print("    both require KNOWING U (=knowing all x_d,y_d) to build => computability barrier,")
    print("    per v14/15; the coupling adds alignment but not a COMPUTABLE readout.")


if __name__ == "__main__":
    main()
