#!/usr/bin/env python3
"""
t_y_maxbound_v1.py -- Item #2 of the ranked menu: PROVE / REFUTE the odd-half (y-twisted)
max-bound.  Object:  U(a,b,c) = sum_{d in Z/n} e_p(b*x_d + c*y_d) * e_n(a*d),
with (x_d,y_d)=[d]G on a prime-order curve.  T=U(.,.,0) is the KS-bounded x-only sum.

QUESTION (open per v15/v16 handover): is  max_a |U(a,b,c)| = O(sqrt(p)*polylog)  UNIFORMLY
over ALL (b,c)?  Only avg_a|U|^2 = n (a Parseval fact) was proven; the max over (b,c) was the
"live un-bounded corner".

SOURCE-FIRST FINDING (this file tests it empirically): bx+cy is a rational function on E of
pole order <= 3 at O (x: order 2, y: order 3).  The Kohel-Shparlinski / Lange-Shparlinski
character-sum bound for sum_d psi(f([d]G)) e_n(ad) holds for any nonconstant rational f with a
constant depending only on deg(f) -- hence UNIFORM in the coefficients (b,c).  So the bound is
expected to hold (grade CITED, general-f KS).  This script CONFIRMS or REFUTES it for the secp
form, hunts for an exceptional (b,c) scar, and measures the scaling max/sqrt(p) vs log p.

TESTS:
 (1) full (b,c) scan (small p): global max_{a!=0,(b,c)!=0}|U|, its argmax structure, ratio/sqrt(p).
 (2) scaling: max/sqrt(p) and max/(sqrt(p)*log p) across a range of p.  O(log p) => bound holds.
 (3) does c!=0 EVER exceed the pure-x (c=0) max?  (the y-coordinate breaking KS.)
 (4) CM (y^2=x^3+7) vs non-CM control.
 (5) s_y-twisted T_y = sum_d e_p(b x_d) s_y(d) e_n(ad), s_y odd in d (v15's object).

FLOAT CARVE-OUT: the character-sum magnitudes |U| are roots-of-unity analytic-size quantities
with NO key / no leakage-signal in the path -- the same carve-out used by
glv_closure_verification_v1.py.  Exact-int arithmetic is used for the curve/group; numpy FFT is
used only for the |U| magnitudes.  (btc CLAUDE.md: the no-float rule governs the signal path.)
"""
import math
import numpy as np


# ---- exact integer number theory / curve arithmetic (signal path: no float) ----

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def tonelli(n, p):
    n %= p
    if n == 0:
        return 0
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r

def ec_add(P, Q, p, a):
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        lam = (3 * x1 * x1 + a) % p * pow(2 * y1 % p, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)

def prime_order_curve(lo, hi, a=0, b=7):
    from sympy import isprime
    for q in range(lo, hi):
        if not isprime(q) or q % 3 != 1:
            continue
        m = q + 1
        for x in range(q):
            m += legendre((x * x % q * x + a * x + b) % q, q)
        if isprime(m):
            for x0 in range(1, q):
                r = (x0 * x0 % q * x0 + a * x0 + b) % q
                if legendre(r, q) == 1:
                    return q, m, (x0, tonelli(r, q))
    return None

def group_coords(G, p, n, a):
    xs = [0] * n; ys = [0] * n
    acc = None
    for d in range(1, n):
        acc = ec_add(acc, G, p, a)
        xs[d], ys[d] = acc
    return xs, ys


# ---- character sums (analytic-size: numpy float allowed here) ----

def U_all_a(xsA, ysA, b, c, p):
    """U(a,b,c) for all a, via FFT over d.  xsA,ysA are int numpy arrays (index d=0..n-1, d=0 unused)."""
    ph = np.exp(2j * np.pi * ((b * xsA + c * ysA) % p) / p)
    ph[0] = 0.0            # d=0 (identity) carries no coordinate; exclude
    return np.fft.fft(ph)

def Ty_all_a(xsA, syA, b, p):
    """T_y(a,b) = sum_d e_p(b x_d) s_y(d) e_n(a d), s_y odd in d."""
    ph = np.exp(2j * np.pi * ((b * xsA) % p) / p) * syA
    ph[0] = 0.0
    return np.fft.fft(ph)


def full_scan(xs, ys, p, n):
    """Global max over a!=0 and ALL (b,c)!=(0,0) of |U|.  Returns (maxratio, argmax b,c, cat)."""
    xsA = np.array(xs, dtype=np.int64); ysA = np.array(ys, dtype=np.int64)
    sp = math.sqrt(p)
    gmax = 0.0; garg = None
    max_c0 = 0.0                       # best pure-x (c=0) = T
    max_cne = 0.0                      # best c!=0
    for b in range(p):
        for c in range(p):
            if b == 0 and c == 0:
                continue
            U = np.abs(U_all_a(xsA, ysA, b, c, p))
            U[0] = 0.0                 # exclude a=0
            m = float(U.max())
            if c == 0:
                max_c0 = max(max_c0, m)
            else:
                max_cne = max(max_cne, m)
            if m > gmax:
                gmax = m; garg = (b, c)
    return dict(gmax_ratio=gmax / sp, arg=garg, max_c0_ratio=max_c0 / sp,
                max_cne_ratio=max_cne / sp)

def sampled_scan(xs, ys, p, n, nsamp=3000, seed=0):
    xsA = np.array(xs, dtype=np.int64); ysA = np.array(ys, dtype=np.int64)
    sp = math.sqrt(p)
    rng = np.random.default_rng(seed)
    gmax = 0.0; garg = None
    # always include all diagonals c=+-b and c=0, plus random (b,c)
    cand = []
    for b in range(1, p):
        cand.append((b, 0)); cand.append((b, b % p)); cand.append((b, (-b) % p))
    for _ in range(nsamp):
        cand.append((int(rng.integers(0, p)), int(rng.integers(0, p))))
    cand.append((0, 1))
    for (b, c) in cand:
        if b == 0 and c == 0:
            continue
        U = np.abs(U_all_a(xsA, ysA, b, c, p)); U[0] = 0.0
        m = float(U.max())
        if m > gmax:
            gmax = m; garg = (b, c)
    return dict(gmax_ratio=gmax / sp, arg=garg)

def ty_scan(xs, ys, p, n):
    xsA = np.array(xs, dtype=np.int64)
    # s_y odd in d: +1 if y_d < p/2 else -1  (=> s_y(n-d) = -s_y(d))
    syA = np.array([0] + [1 if ys[d] < p / 2 else -1 for d in range(1, n)], dtype=float)
    sp = math.sqrt(p)
    gmax = 0.0; argb = None
    for b in range(1, p):
        Ty = np.abs(Ty_all_a(xsA, syA, b, p)); Ty[0] = 0.0
        m = float(Ty.max())
        if m > gmax:
            gmax = m; argb = b
    return dict(gmax_ratio=gmax / sp, argb=argb)


def analyze_argmax(b, c, p, beta=None):
    """Structure of the argmax (b,c): diagonal? GLV/CM ratio? """
    tags = []
    if c == 0:
        tags.append("c=0 (pure-x / T)")
    if c == b:
        tags.append("c=+b diag")
    if c == (-b) % p:
        tags.append("c=-b diag")
    if beta and b != 0:
        r = c * pow(b, p - 2, p) % p
        if r in (beta, beta * beta % p):
            tags.append("c/b = beta (GLV)")
    return tags or ["generic"]


def main():
    print("=" * 78)
    print("T_y ODD-HALF MAX-BOUND  --  item #2  (U(a,b,c)=sum e_p(bx+cy)e_n(ad))")
    print("=" * 78)

    # (1)+(2) full scan + scaling on secp-form, small p; then sampled larger p
    print("\n[1/2] max_{a!=0,(b,c)!=0} |U| / sqrt(p)  and scaling vs log p  (secp y^2=x^3+7)")
    print("      also: max over c=0 (pure-x=T, KS-bounded) vs c!=0 (does y break KS?)")
    small = [(60, 200), (200, 400), (400, 700)]      # full (b,c) scan
    for lo, hi in small:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        # GLV beta
        e = (p - 1) // 3; g = 2
        while pow(g, e, p) == 1:
            g += 1
        beta = pow(g, e, p)
        sc = full_scan(xs, ys, p, n)
        tags = analyze_argmax(sc['arg'][0], sc['arg'][1], p, beta)
        print("   p=%-4d n=%-4d  FULL  max/sqrt(p)=%.3f  /(sqrt(p)logp)=%.3f  argmax(b,c)=%s %s"
              % (p, n, sc['gmax_ratio'], sc['gmax_ratio'] / math.log(p), sc['arg'], tags))
        print("            c=0(T) max/sqrt(p)=%.3f   c!=0 max/sqrt(p)=%.3f   %s"
              % (sc['max_c0_ratio'], sc['max_cne_ratio'],
                 "c!=0 EXCEEDS c=0 (y adds)" if sc['max_cne_ratio'] > sc['max_c0_ratio'] + 1e-9
                 else "c=0 >= c!=0 (y no larger)"))
    for lo, hi in [(700, 1100), (1500, 2000), (2500, 3200)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        sc = sampled_scan(xs, ys, p, n)
        print("   p=%-4d n=%-4d  SAMP  max/sqrt(p)=%.3f  /(sqrt(p)logp)=%.3f  argmax(b,c)=%s"
              % (p, n, sc['gmax_ratio'], sc['gmax_ratio'] / math.log(p), sc['arg']))

    # (4) CM vs non-CM (full scan, matched-size p)
    print("\n[4] CM (y^2=x^3+7) vs non-CM control, full (b,c) scan, comparable p")
    rc = prime_order_curve(200, 400)
    if rc:
        p, n, G = rc; xs, ys = group_coords(G, p, n, 0)
        sc = full_scan(xs, ys, p, n)
        print("   CM    p=%-4d  max/sqrt(p)=%.3f  argmax=%s" % (p, sc['gmax_ratio'], sc['arg']))
    rn = prime_order_curve(200, 400, a=1, b=1)
    if rn:
        p, n, G = rn; xs, ys = group_coords(G, p, n, 1)
        sc = full_scan(xs, ys, p, n)
        print("   nonCM p=%-4d  max/sqrt(p)=%.3f  argmax=%s" % (p, sc['gmax_ratio'], sc['arg']))

    # (5) s_y-twisted T_y (v15's object)
    print("\n[5] s_y-twisted T_y = sum_d e_p(b x_d) s_y(d) e_n(a d),  s_y odd in d")
    for lo, hi in [(200, 400), (700, 1100), (1500, 2000)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r; xs, ys = group_coords(G, p, n, 0)
        t = ty_scan(xs, ys, p, n)
        print("   p=%-4d  max_{a,b}|T_y|/sqrt(p)=%.3f  /(sqrt(p)logp)=%.3f  argb=%s"
              % (p, t['gmax_ratio'], t['gmax_ratio'] / math.log(p), t['argb']))

    print("\n[done]")


if __name__ == "__main__":
    main()
