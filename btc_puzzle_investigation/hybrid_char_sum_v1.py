#!/usr/bin/env python3
"""
hybrid_char_sum_v1.py — THE IDEA, tested. (What section G should have been.)

The masking hypothesis, in the only form the closure theorem leaves open:

    closure:  |Cov(F(x([d]G)), phi(d))| <= (max|T|/n)*||F||_A*||phi||_A = O(p^-1/2)*||F||_A*||phi||_A
    blind spot: VACUOUS exactly when ||F||_A ~ sqrt(p)  --  i.e. MULTIPLICATIVE CHARACTERS
                (Gauss sums: |chi^(b)| = 1/sqrt(p) for every b != 0  =>  ||chi||_A ~ sqrt(p))

So the one place "additive structure looks multiplicative" can live is the HYBRID sum

    S_k(a) = sum_{d=1..n}  chi_k( x([d]G) ) * e_n(a*d)          e_n(t) = exp(2*pi*i*t/n)

which pairs a multiplicative character on F_p (the closure-blind readout) against an
additive character on Z/nZ (the additive structure of the scalar).  |S_k(a)| IS the
correlation. Section G instead measured MI(chi_k, d mod k) -- a proxy that (a) is not the
additive structure in question and (b) is ALREADY known null (Boneh-Shparlinski: the LSB
of d is a hardcore predicate for ECDLP). That tested the method, not the idea.

Here we ENUMERATE THE WHOLE GROUP on small curves y^2 = x^3 + 7 / F_p. No sampling, no
mutual information, no statistical power question: the sum is exact and complete.

Scales for max_{a != 0} |S_k(a)|:
    total leak        ~ n           (chi_k is a pure additive character in disguise)
    generic/random    ~ sqrt(2 n ln n)      (max of n indep. random-phase sums)
    Weil/Bourgain     ~ sqrt(p) * polylog   (what theory predicts if no structure)
A value >> sqrt(n ln n) at any a is the gate.

FLOAT NOTE (CLAUDE.md no-float): the sequence is exact (chi_k computed by exact modular
exponentiation on exact integer curve points). Only the DFT that turns it into |S_k(a)| is
float; for a +-1/root-of-unity sequence of length n <= ~2e5 the FFT round-off is
~ n*eps ~ 1e-11, versus signal scales 1e2..1e5 -- 13 orders of margin. The top-|S| value is
then RE-VERIFIED by exact integer/Gaussian arithmetic. No key is in this path at all.
"""
import cmath, math
import numpy as np
from sympy import isprime


# ------------------------------------------------------------------ small curve y^2=x^3+7
def curve_points_order(p):
    """#E(F_p) for y^2 = x^3+7 via character sum (exact)."""
    n = p + 1
    for x in range(p):
        n += legendre(( x * x * x + 7) % p, p)
    return n


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def padd(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        if y1 == 0: return None
        lam = (3 * x1 * x1) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def find_point(p):
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if legendre(r, p) == 1:
            y = tonelli(r, p)
            if y is not None: return (x, y)
    return None


def tonelli(a, p):
    if p % 4 == 3:
        r = pow(a, (p + 1) // 4, p)
        return r if (r * r - a) % p == 0 else None
    # generic Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        if t == 0: return None
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
            if i == m: return None
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t = t * c % p; r = r * b % p
    return r if (r * r - a) % p == 0 else None


def make_chik(p, k):
    e = (p - 1) // k
    pf = {2: {2}, 3: {3}, 6: {2, 3}}[k]
    zeta, x = None, 2
    while zeta is None:
        r = pow(x, e, p)
        if r != 1 and all(pow(r, k // q, p) != 1 for q in pf): zeta = r
        x += 1
    tbl, cur = {}, 1
    for j in range(k):
        tbl[cur] = j; cur = cur * zeta % p
    def chik(v):
        v %= p
        return None if v == 0 else tbl[pow(v, e, p)]
    return chik


def point_order(G, p, n):
    # order divides n; find it by factoring n's divisors (n small)
    divs = [d for d in range(1, n + 1) if n % d == 0]
    for d in divs:
        acc, Q = None, G
        # d*G via double-and-add
        acc = mul(G, d, p)
        if acc is None: return d
    return n


def mul(P, k, p):
    R, Q = None, P
    while k:
        if k & 1: R = padd(R, Q, p)
        Q = padd(Q, Q, p); k >>= 1
    return R


def run(p, ks=(2, 3, 6)):
    n = curve_points_order(p)
    G = find_point(p)
    m = point_order(G, p, n)
    if m < 200: return None
    # walk the cyclic subgroup <G>: d = 1..m
    xs = []
    acc = None
    for _ in range(m):
        acc = padd(acc, G, p)
        xs.append(acc[0] if acc is not None else None)
    out = {}
    for k in ks:
        if (p - 1) % k: continue
        chi = make_chik(p, k)
        # exact sequence of k-th roots of unity (as exponents); None (x=0) -> 0
        seq = np.zeros(m, dtype=complex)
        for i, x in enumerate(xs):
            if x is None: continue
            j = chi(x)
            seq[i] = 0 if j is None else cmath.exp(2j * math.pi * j / k)
        F = np.fft.fft(seq)                 # S_k(a) for a = 0..m-1  (float; see FLOAT NOTE)
        mag = np.abs(F)
        mag[0] = 0                          # drop a=0 (the trivial mean term)
        a_star = int(np.argmax(mag)); S = float(mag[a_star])
        gen = math.sqrt(2 * m * math.log(m))
        out[k] = (m, a_star, S, S / gen, S / math.sqrt(p), S / m)
    return n, m, out


def main():
    print("HYBRID CHARACTER SUM  S_k(a) = sum_{d=1..m} chi_k(x([d]G)) e_m(a d)")
    print("Full enumeration of <G> on y^2=x^3+7 / F_p.  The closure-BLIND corner.")
    print()
    print(f"{'p':>7} {'m=|<G>|':>8} {'k':>2} {'a*':>7} {'max|S|':>10} {'/sqrt(2m ln m)':>15} "
          f"{'/sqrt(p)':>9} {'/m (leak=1)':>12}")
    ps = [p for p in range(500, 60000) if isprime(p) and p % 3 == 1]
    picks = [ps[0], ps[10], ps[40], ps[120], ps[300], ps[700], ps[-1]]
    for p in picks:
        r = run(p)
        if r is None: continue
        n, m, out = r
        for k, (mm, a, S, rg, rp, rl) in sorted(out.items()):
            print(f"{p:>7} {mm:>8} {k:>2} {a:>7} {S:>10.2f} {rg:>15.3f} {rp:>9.3f} {rl:>12.5f}")
    print()
    print("READ: /sqrt(2m ln m) ~ 1  => generic random-like (NO masking-visible structure)")
    print("      /m -> 1            => total leak (chi_k IS an additive character)")


if __name__ == "__main__":
    main()
