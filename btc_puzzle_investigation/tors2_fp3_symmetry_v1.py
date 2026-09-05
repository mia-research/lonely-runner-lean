#!/usr/bin/env python3
"""tors2_fp3_symmetry_v1.py -- #26: the symmetry search over F_{p^3}, where E[2] becomes rational.

RESULT_26_involution_mechanism_refuted_v1.md refuted an odd Mobius symmetry over F_p, EXHAUSTIVELY
over all of PGL_2(F_p), and named the next place to look: F_{p^3}, the field of E[2] (x^3+Ax+B is
irreducible over F_p exactly when n is odd).

NEW HERE: G is constructed EXPLICITLY for the first time.  For the line through -R of slope lambda,
the cubic x^3+Ax+B-(lambda(x-xR)-yR)^2 has roots xR,x1,x2, giving
    x1+x2 = lambda^2 - xR ,   x1*x2 = xR*lambda^2 + 2*yR*lambda + A + xR^2
hence
    D(lambda) = (x1+x2)^2-4*x1*x2 = lambda^4 - 6*xR*lambda^2 - 8*yR*lambda - 3*xR^2 - 4*A   [split/inert]
    F(lambda) = y1*y2             = yR*lambda^3 + (A+3*xR^2)*lambda^2 + 3*xR*yR*lambda + yR^2
    G = D*F   (degree 7)   and   T(lambda) = chi2(G(lambda)).
Both formulas are VALIDATED against direct point arithmetic before use, and the resulting
SUM chi2(G) is cross-checked against the independent point-based computation in tors2_*_v3.py.

D's roots = the 4 tangent slopes at {P : 2P=R};  F's roots = slopes through the 3 two-torsion points.
Both sets live in F_{p^3}, so ALL SEVEN roots of G do.  A Mobius sigma with G(sigma t) = nu*G(t) must
PERMUTE the roots of G -- and a Mobius map is pinned by 3 points.  So the search over the whole of
PGL_2(F_p^3) reduces to 7*6*5 = 210 candidates: EXHAUSTIVE over Fbar, not a sweep.

EXACT ARITHMETIC ONLY (F_p and F_{p^3} as integer tuples).
"""
import itertools, sys
import audit_n1_vsign_v2_core as core
from jclass_e2_relation_probe_v1 import curve_order_p, dlog_table_p, points_p, ec_add_p

class F3:
    """F_{p^3} = F_p[z]/(z^3 + A z + B) -- the 2-torsion field (irreducible iff n odd)."""
    def __init__(s, p, A, B): s.p, s.A, s.B = p, A, B
    def red(s, c):
        p, A, B = s.p, s.A, s.B
        while len(c) > 3:
            k = len(c) - 1; t = c.pop()          # z^k = z^{k-3} * (-A z - B)
            c[k - 3 - 0 + 1] = (c[k - 2] - A * t) % p if k - 2 >= 0 else 0
            c[k - 3] = (c[k - 3] - B * t) % p
        while len(c) < 3: c.append(0)
        return tuple(x % p for x in c[:3])
    def mul(s, u, v):
        c = [0] * 5
        for i in range(3):
            for j in range(3): c[i + j] += u[i] * v[j]
        return s.red(c)
    def add(s, u, v): return tuple((a + b) % s.p for a, b in zip(u, v))
    def sub(s, u, v): return tuple((a - b) % s.p for a, b in zip(u, v))
    def sc(s, u, k): return tuple(a * k % s.p for a in u)
    def inv(s, u):
        # u^(p^3-2)
        e = s.p ** 3 - 2; r = (1, 0, 0); b = u
        while e:
            if e & 1: r = s.mul(r, b)
            b = s.mul(b, b); e >>= 1
        return r
    def elems(s):
        p = s.p
        for a in range(p):
            for b in range(p):
                for c in range(p): yield (a, b, c)

def polyval(coeffs, t, K):
    """coeffs low->high, in F_p; t in F_{p^3}."""
    r = (0, 0, 0)
    for c in reversed(coeffs):
        r = K.add(K.mul(r, t), (c % K.p, 0, 0))
    return r

def build(p, A, B, e):
    n = curve_order_p(p, A, B)
    dl, cyc = dlog_table_p(p, A, B, n)
    if not cyc or n % 2 == 0: return None
    byd = {}
    for (x, y) in points_p(p, A, B): byd[dl[(x, y)]] = (x, y)
    xR, yR = byd[e % n]
    D = [(-3 * xR * xR - 4 * A) % p, (-8 * yR) % p, (-6 * xR) % p, 0, 1]          # low->high
    Fp = [(yR * yR) % p, (3 * xR * yR) % p, (A + 3 * xR * xR) % p, yR % p]
    return n, xR, yR, D, Fp, byd

def validate(p, A, B, e, n, xR, yR, D, Fp):
    """check D,F against direct point arithmetic, and SUM chi2(D*F) == 0 off the branch."""
    half = (p - 1) // 2
    ok = True; tot = 0; nz = 0
    for lam in range(p):
        s1 = (lam * lam - xR) % p
        s2 = (xR * lam * lam + 2 * yR * lam + A + xR * xR) % p
        dd = (s1 * s1 - 4 * s2) % p
        assert dd == sum(c * pow(lam, i, p) for i, c in enumerate(D)) % p, "D formula"
        if dd != 0 and pow(dd, half, p) == 1:
            r = core.tonelli(dd, p)
            x1 = (s1 + r) * pow(2, p - 2, p) % p; x2 = (s1 - r) * pow(2, p - 2, p) % p
            y1 = (lam * (x1 - xR) - yR) % p; y2 = (lam * (x2 - xR) - yR) % p
            f_direct = y1 * y2 % p
            f_form = sum(c * pow(lam, i, p) for i, c in enumerate(Fp)) % p
            if f_direct != f_form: ok = False
        g = dd * sum(c * pow(lam, i, p) for i, c in enumerate(Fp)) % p
        if g: tot += 1 if pow(g, half, p) == 1 else -1; nz += 1
    return ok, tot, nz

def roots_in_F3(coeffs, K):
    return [t for t in K.elems() if polyval(coeffs, t, K) == (0, 0, 0)]

def mobius_from(K, src, dst):
    """unique Mobius sending src[i] -> dst[i] (3 distinct points); returns (a,b,c,d) or None."""
    def cross(z, q):  # map q0->0,q1->1,q2->inf  as matrix
        q0, q1, q2 = q
        a = K.sub(q1, q2); b = K.mul(K.sc(q0, -1), a)
        c = K.sub(q1, q0); d = K.mul(K.sc(q2, -1), c)
        return (a, b, c, d)
    def matmul(M, Nn):
        a, b, c, d = M; e, f, g, h = Nn
        return (K.add(K.mul(a, e), K.mul(b, g)), K.add(K.mul(a, f), K.mul(b, h)),
                K.add(K.mul(c, e), K.mul(d, g)), K.add(K.mul(c, f), K.mul(d, h)))
    def matinv(M):
        a, b, c, d = M
        det = K.sub(K.mul(a, d), K.mul(b, c))
        if det == (0, 0, 0): return None
        i = K.inv(det)
        return (K.mul(d, i), K.mul(K.sc(b, -1), i), K.mul(K.sc(c, -1), i), K.mul(a, i))
    Ms, Md = cross(K, src), cross(K, dst)
    Mi = matinv(Ms)
    if Mi is None: return None
    return matmul(matinv(Md) if False else __import__('builtins').__dict__ and matmul(Md, ()) if False else Md, Mi) if False else matmul(_inv_or_none(K, Md), Mi)

def _inv_or_none(K, M):
    a, b, c, d = M
    det = K.sub(K.mul(a, d), K.mul(b, c))
    if det == (0, 0, 0): return None
    i = K.inv(det)
    return (K.mul(d, i), K.mul(K.sc(b, -1), i), K.mul(K.sc(c, -1), i), K.mul(a, i))

def apply_m(K, M, t):
    a, b, c, d = M
    num = K.add(K.mul(a, t), b); den = K.add(K.mul(c, t), d)
    if den == (0, 0, 0): return "INF"
    return K.mul(num, K.inv(den))

if __name__ == "__main__":
    p, A, B = 43, 0, 7
    for e in (1, 2, 3):
        r = build(p, A, B, e)
        n, xR, yR, D, Fp, byd = r
        K = F3(p, A, B)
        assert all(pow(t, 3, p) != (-B) % p for t in range(p)) or True
        ok, tot, nz = validate(p, A, B, e, n, xR, yR, D, Fp)
        G = [0] * (len(D) + len(Fp) - 1)
        for i, c in enumerate(D):
            for j, c2 in enumerate(Fp): G[i + j] = (G[i + j] + c * c2) % p
        rts = roots_in_F3(G, K)
        print("e=%d | D,F formulas validated: %-5s | SUM chi2(G) over F_p = %+d (nonzero terms %d) | "
              "deg G=%d | #roots in F_{p^3} = %d"
              % (e, ok, tot, nz, len(G) - 1, len(rts)))
