#!/usr/bin/env python3
"""
signal_path_v1.py — EXACT INTEGER signal path for PREREG_subrayleigh_cubic_coherence_v1.
check_no_float target: this module contains NO float, NO "/", NO "**0.5", NO math/np on
key-derived values. Everything is python int / modular arithmetic. It produces:
  - the exact [d]G orbit table (x_d, y_d) for a CANONICAL GENERATOR of E(F_p) (order exactly n),
  - the Legendre character chi2,
  - the integer exactness anchors E = p(n-2)-1 (slice-L2) and p^2(n-1) (global-L2).
The float transform/ensemble lives in run_v1.py (the sanctioned carve-out).
"""


def _factor(m):
    """distinct prime factors of m (trial division; m small model-scale)."""
    fs = []
    d = 2
    while d * d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        fs.append(m)
    return fs


class Curve:
    def __init__(self, p, B=7):
        self.p = p
        self.B = B

    def add(self, A, C):
        p = self.p
        if A is None:
            return C
        if C is None:
            return A
        x1, y1 = A
        x2, y2 = C
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if x1 == x2:
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        y3 = (lam * (x1 - x3) - y1) % p
        return (x3, y3)

    def mul(self, k, P):
        R = None
        Q = P
        while k > 0:
            if k & 1:
                R = self.add(R, Q)
            Q = self.add(Q, Q)
            k >>= 1
        return R

    def order_count(self):
        """#E(F_p) by exact point enumeration."""
        p, B = self.p, self.B
        npts = 1  # O
        for x in range(p):
            r = (x * x * x + B) % p
            if r == 0:
                npts += 1
            elif pow(r, (p - 1) // 2, p) == 1:
                npts += 2
        return npts

    def sqrt_mod(self, a):
        """Tonelli-Shanks, exact int. Returns a root of x^2=a mod p or None."""
        p = self.p
        a %= p
        if a == 0:
            return 0
        if pow(a, (p - 1) // 2, p) != 1:
            return None
        if p % 4 == 3:
            return pow(a, (p + 1) // 4, p)
        # Tonelli-Shanks
        q = p - 1
        s = 0
        while q % 2 == 0:
            q //= 2
            s += 1
        z = 2
        while pow(z, (p - 1) // 2, p) != p - 1:
            z += 1
        m = s
        c = pow(z, q, p)
        t = pow(a, q, p)
        r = pow(a, (q + 1) // 2, p)
        while t != 1:
            i = 0
            t2 = t
            while t2 != 1:
                t2 = t2 * t2 % p
                i += 1
            b = pow(c, 1 << (m - i - 1), p)
            m = i
            c = b * b % p
            t = t * c % p
            r = r * b % p
        return r


def orbit(p, B=7):
    """Return (n, X, Y): n=#E, X[d],Y[d]=coords of [d]G for a canonical generator G
    (minimal (x,then y) point of order EXACTLY n). X[0]=Y[0]=0 sentinel (O). Exact int."""
    E = Curve(p, B)
    n = E.order_count()
    facs = _factor(n)
    # canonical generator: minimal (x, then y) point of full order n
    G = None
    for x in range(p):
        r = (x * x * x + B) % p
        if r == 0:
            cand = [(x, 0)]
        else:
            if pow(r, (p - 1) // 2, p) != 1:
                continue
            y = E.sqrt_mod(r)
            cand = sorted([(x, y), (x, (p - y) % p)])
        for P in cand:
            # order == n  iff  [n//l]P != O for every prime l | n  (and [n]P == O)
            if E.mul(n, P) is not None:
                continue
            if all(E.mul(n // l, P) is not None for l in facs):
                G = P
                break
        if G is not None:
            break
    if G is None:
        return None
    X = [0] * n
    Y = [0] * n
    P = None
    for d in range(1, n):
        P = E.add(P, G)
        if P is None:
            return None  # not a generator (should not happen)
        X[d], Y[d] = P
    return n, X, Y, facs


def chi2_legendre(p):
    """Legendre symbol table chi2[b] in {-1,0,+1}, exact int (Euler)."""
    chi = [0] * p
    for b in range(1, p):
        chi[b] = 1 if pow(b, (p - 1) // 2, p) == 1 else -1
    return chi


def slice_L2_anchor(p, n):
    """Exact integer E = p(n-2) - 1  (Sum_{b=1..p-1} |T(b)|^2, n odd)."""
    return p * (n - 2) - 1


def global_L2_anchor(p, n):
    """Exact integer p^2 (n-1)  (Sum_{b,c} |U(b,c)|^2)."""
    return p * p * (n - 1)


if __name__ == "__main__":
    # smoke: report n, generator, anchors for a few schedule primes (exact int only)
    for p in [151, 211, 241, 691]:
        res = orbit(p)
        if res is None:
            print(f"p={p}: no generator found"); continue
        n, X, Y, facs = res
        print(f"p={p:5d} n={n:5d} facs={facs} G=({X[1]},{Y[1]}) "
              f"n_odd={n % 2 == 1} E_slice={slice_L2_anchor(p, n)} L2glob={global_L2_anchor(p, n)}")
