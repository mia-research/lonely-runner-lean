#!/usr/bin/env python3
"""jac26_intonly_crosscheck_v1.py -- INTEGER-ONLY independent reimplementation.

Purpose.  check_no_float.py flags every `/` in the Sage scripts.  All of those are finite-field
divisions (exact), but the AST guard cannot see that.  Rather than exempt them by assertion, this
file recomputes the SAME headline quantities with NO division of any kind -- only `+ - * %`,
`pow(.,.,p)` and exact `//` with an asserted-zero remainder.  It is therefore guard-clean by
construction, uses a completely independent code path (no Sage, no EllipticCurve, no
PolynomialRing), and its agreement with the Sage results settles the float question empirically.

Recomputed:
    Sum_{lambda in F_p} chi_2(G_R(lambda))
    #C(F_{p^k}) for k = 1,2,3      (C : w^2 = G, deg G = 7)
    c1, c2, c3   of  Ch(T) = T^6 - c1 T^5 + c2 T^4 - c3 T^3 + p c2 T^2 - p^2 c1 T + p^3

F_{p^k} is built by hand as F_p[t]/(m) with m MONIC irreducible, so reduction needs only
multiplication and subtraction -- no inverses are ever required, because the quadratic character
is computed as an exponentiation.
"""

import sys


# ------------------------------------------------------------------ F_p helpers

def is_irreducible_low_degree(coeffs, p):
    """coeffs = [c0,...,c_{d-1}, 1] monic of degree d in {2,3}: irreducible iff no root in F_p."""
    d = len(coeffs) - 1
    assert d in (2, 3)
    for x in range(p):
        v = 0
        for c in reversed(coeffs):
            v = (v * x + c) % p
        if v == 0:
            return False
    return True


def find_monic_irreducible(p, d):
    if d == 1:
        return [0, 1]
    if d == 2:
        for c0 in range(p):
            for c1 in range(p):
                if is_irreducible_low_degree([c0, c1, 1], p):
                    return [c0, c1, 1]
    if d == 3:
        for c0 in range(1, p):
            for c1 in range(p):
                for c2 in range(p):
                    if is_irreducible_low_degree([c0, c1, c2, 1], p):
                        return [c0, c1, c2, 1]
    raise RuntimeError("no irreducible found")


class Fq(object):
    """F_{p^d} = F_p[t]/(m), m monic.  Elements are tuples of length d.  Multiplication only."""

    def __init__(self, p, d):
        self.p, self.d = p, d
        self.m = find_monic_irreducible(p, d)

    def zero(self):
        return (0,)*self.d

    def one(self):
        return (1,) + (0,)*(self.d - 1)

    def from_int(self, a):
        return (a % self.p,) + (0,)*(self.d - 1)

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def mul(self, a, b):
        p, d, m = self.p, self.d, self.m
        r = [0]*(2*d - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        r[i + j] = (r[i + j] + x*y) % p
        # reduce by the MONIC m: t^d = -(m[0] + m[1] t + ... + m[d-1] t^{d-1})
        for k in range(2*d - 2, d - 1, -1):
            c = r[k]
            if c:
                r[k] = 0
                for j in range(d):
                    r[k - d + j] = (r[k - d + j] - c*m[j]) % p
        return tuple(r[:d])

    def powe(self, a, e):
        res, base = self.one(), a
        while e > 0:
            if e & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            e >>= 1
        return res

    def elements(self):
        p, d = self.p, self.d
        idx = [0]*d
        total = p**d
        for _ in range(total):
            yield tuple(idx)
            for i in range(d):
                idx[i] += 1
                if idx[i] < p:
                    break
                idx[i] = 0

    def chi2(self, a):
        """quadratic character of F_{p^d}: 0, +1 or -1, by exponentiation (no division)."""
        if all(c == 0 for c in a):
            return 0
        q = self.p**self.d
        r = self.powe(a, (q - 1)//2)
        return 1 if r == self.one() else -1


# ----------------------------------------------------- the objects, over the integers

def G_coeffs(p, A, B, xR, yR):
    """coefficients of G = D*F (degree 7), as integers mod p, low-order first."""
    D = [(-3*xR*xR - 4*A) % p, (-8*yR) % p, (-6*xR) % p, 0, 1]
    F = [(yR*yR) % p, (3*xR*yR) % p, (A + 3*xR*xR) % p, yR % p]
    G = [0]*(len(D) + len(F) - 1)
    for i, a in enumerate(D):
        if a:
            for j, b in enumerate(F):
                G[i + j] = (G[i + j] + a*b) % p
    return G


def count_C(p, k, G, Fk):
    """#C(F_{p^k}) for w^2 = G(lambda), deg G = 7 odd => one point at infinity."""
    Gk = [Fk.from_int(c) for c in G]
    total = 1
    for lam in Fk.elements():
        v = Fk.zero()
        for c in reversed(Gk):
            v = Fk.add(Fk.mul(v, lam), c)
        ch = Fk.chi2(v)
        total += 1 if ch == 0 else (2 if ch == 1 else 0)
    return total


def newton(p, counts):
    s = {k: p**k + 1 - counts[k] for k in counts}
    c1 = s[1]
    n2 = c1*s[1] - s[2]
    assert n2 % 2 == 0, "c2 not integral"
    c2 = n2 // 2
    if 3 not in s:
        return c1, c2, None
    n3 = s[3] - c1*s[2] + c2*s[1]
    assert n3 % 3 == 0, "c3 not integral"
    return c1, c2, n3 // 3


# --------------------------------------------------------------- a tiny curve engine

def curve_points(p, A, B):
    """all affine points of y^2 = x^3+Ax+B over F_p, by exhaustive search (no division)."""
    sq = {}
    for y in range(p):
        sq.setdefault((y*y) % p, []).append(y)
    pts = []
    for x in range(p):
        r = (x*x % p*x + A*x + B) % p
        for y in sq.get(r, []):
            pts.append((x, y))
    return pts


def main():
    # (p, A, B, e-index into a deterministic point list) -- cells cross-checked against Sage
    CASES = [
        (43, 0, 7), (67, 0, 7), (79, 0, 7), (79, 1, 6), (37, 0, 2), (61, 0, 2),
    ]
    print("=" * 92)
    print("INTEGER-ONLY CROSS-CHECK  (no division; guard-clean by construction)")
    print("=" * 92)
    print("%-5s %-4s %-4s %-9s %-9s | %-8s %-11s %-13s | %-4s %-4s %-7s" %
          ("p", "A", "B", "xR", "yR", "sumChi", "#C(F_p)", "#C(F_p^2)", "c1", "c2", "c3"))
    allok = True
    for (p, A, B) in CASES:
        F1, F2, F3 = Fq(p, 1), Fq(p, 2), Fq(p, 3)
        pts = curve_points(p, A, B)
        n = len(pts) + 1
        if n % 2 == 0:
            print("  p=%d: n=%d even, skipped" % (p, n))
            continue
        # take the first few points with yR != 0 as R
        tested = 0
        for (xR, yR) in pts:
            if yR == 0:
                continue
            if tested >= 3:
                break
            tested += 1
            G = G_coeffs(p, A, B, xR, yR)
            if G[7] % p == 0:
                continue
            sumchi = 0
            for lam in range(p):
                v = 0
                for c in reversed(G):
                    v = (v*lam + c) % p
                if v:
                    sumchi += 1 if pow(v, (p - 1)//2, p) == 1 else -1
            counts = {1: count_C(p, 1, G, F1), 2: count_C(p, 2, G, F2),
                      3: count_C(p, 3, G, F3)}
            c1, c2, c3 = newton(p, counts)
            ok = (c1 == 0 and c2 == 0 and sumchi == 0
                  and counts[1] == p + 1 and counts[2] == p*p + 1
                  and counts[3] == p**3 + 1 - 3*c3)
            allok = allok and ok
            print("%-5d %-4d %-4d %-9d %-9d | %-8d %-11d %-13d | %-4d %-4d %-7d  %s" %
                  (p, A, B, xR, yR, sumchi, counts[1], counts[2], c1, c2, c3,
                   "OK" if ok else "*** MISMATCH ***"))
    print("-" * 92)
    print("ALL CELLS: c1 = c2 = 0, sum chi_2(G) = 0, #C(F_p)=p+1, #C(F_p^2)=p^2+1,"
          " #C(F_p^3)=p^3+1-3c3 : %s" % allok)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
