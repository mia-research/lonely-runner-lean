#!/usr/bin/env python3
"""gram_spectrum_exact_v1.py -- ITEM 2, THE ACTUAL RESOLUTION: the |T(a,b)|^2 operator is INTEGRABLE.

THE OBJECT.  T[b,a] = sum_d e_p(b x_d) e_n(a d).  Write M[b,d] = e_p(b x_d) (p x n) and F[d,a] =
e_n(a d) (n x n, F F* = n I).  Then T = M F, so

    T T*  =  M F F* M*  =  n * (M M*)   =:  n * H,

i.e. the singular values of T are sqrt(n) times those of M, and ALL spectral content of the |T|^2
object lives in the Gram operator H.

THE DERIVATION (to be verified below, not assumed).
    H[b,b'] = sum_d e_p(b x_d) conj(e_p(b' x_d)) = sum_d e_p((b-b') x_d) = c(b-b'),
so H is CIRCULANT, with eigenvalues indexed by k in F_p:
    mu_k = sum_m c(m) e_p(-k m) = sum_d sum_m e_p(m (x_d - k)) = p * #{d : x_d = k}.
Counting: d runs over 1..n-1 (the identity has no x-coordinate); n odd => no rational 2-torsion =>
x^3+Ax+B has no root in F_p => every x-coordinate is shared by exactly the two points (x, +-y).
Therefore #{d : x_d = k} = 1 + chi_2(k^3 + A k + B), and

    mu_k = p * (1 + chi_2(k^3 + A k + B))      taking ONLY the values 2p and 0,
    multiplicities: 2p with multiplicity (n-1)/2, 0 with multiplicity p - (n-1)/2.

WHY THIS IS THE ANSWER AND NOT AN OBSTACLE.  A spectrum with exactly TWO distinct eigenvalues is
maximally degenerate / integrable.  It has no level repulsion (all nonzero gaps are 0 or 2p), its
counting function is a two-step staircase, and Delta_3, Sigma^2 and the Wigner surmise are fixed by
the two multiplicities alone -- there is no fluctuation content for them to measure.  The RMT battery
is not INAPPLICABLE here; it is ANSWERED here, in closed form, in the strongest possible direction.

And the content is explicit: the eigenvalue at additive frequency k is p times the quadratic
character of the curve equation.  The whole "spectral" layer of |T(a,b)|^2 is chi_2(x^3+Ax+B).
"""

import numpy as np
import sys

sys.path.insert(0, ".")
from twist_orbit_spectrum_run_v1 import curve_orbit


def isprime(m):
    if m < 2:
        return False
    for d in range(2, int(m**0.5) + 1):
        if m % d == 0:
            return False
    return True


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1)//2, p) == 1 else -1)


def check(p, B=7, A=0):
    r = curve_orbit(p, B)
    if r is None:
        return None
    X, Y, n = r
    if (n - (p + 1))**2 > 4*p or not isprime(n) or n % 2 == 0:
        return None
    xs = np.asarray(X, dtype=np.int64)[1:] % p            # d = 1..n-1 (drop the identity)

    # ---- build M and H = M M* exactly enough to diagonalise
    M = np.exp(2j*np.pi*np.outer(np.arange(p), xs)/p)     # (p, n-1)
    H = M @ M.conj().T

    # C1: is H circulant?  H[b,b'] must depend only on b-b'
    c = H[0, :].copy()
    circ = max(abs(H[b, (b + m) % p] - c[m]) for b in range(0, p, max(1, p//17))
               for m in range(0, p, max(1, p//17)))

    # C2: eigenvalues vs the closed form  mu_k = p*(1 + chi2(k^3+Ak+B))
    ev = np.sort(np.linalg.eigvalsh(H))[::-1]
    pred = np.array(sorted((p*(1 + legendre(k*k % p*k + A*k + B, p)) for k in range(p)),
                           reverse=True), dtype=float)
    maxdiff = float(np.max(np.abs(ev - pred)))

    # C3: multiplicities and distinctness
    vals, cnts = np.unique(np.round(ev, 6), return_counts=True)
    n2p = int(cnts[np.argmin(np.abs(vals - 2*p))]) if len(vals) else 0
    # C4: does any x^3+A x+B vanish?  (must not, since n is odd)
    zeros = sum(1 for k in range(p) if (k*k % p*k + A*k + B) % p == 0)
    return dict(n=n, circ=circ, maxdiff=maxdiff, distinct=len(vals),
                vals=vals, cnts=cnts, mult2p=n2p, expect=(n - 1)//2, zeros=zeros)


if __name__ == "__main__":
    print("=" * 100)
    print("ITEM 2 RESOLUTION -- the Gram operator H = M M* of the |T(a,b)|^2 object is INTEGRABLE")
    print("=" * 100)
    print("  %-6s %-6s | %-11s %-12s %-9s %-22s %s"
          % ("p", "n", "circulant", "|eig-closed|", "#distinct", "spectrum (val x mult)",
             "mult(2p) == (n-1)/2"))
    ok = True
    for p in range(100, 500):
        if not isprime(p) or p % 3 != 1:
            continue
        r = check(p)
        if r is None:
            continue
        spec = ", ".join("%d x %d" % (v, c) for v, c in zip(r["vals"][::-1], r["cnts"][::-1]))
        good = (r["circ"] < 1e-6 and r["maxdiff"] < 1e-6 and r["distinct"] == 2
                and r["mult2p"] == r["expect"] and r["zeros"] == 0)
        ok = ok and good
        print("  %-6d %-6d | %-11.2e %-12.2e %-9d %-22s %s"
              % (p, r["n"], r["circ"], r["maxdiff"], r["distinct"], spec,
                 "YES" if r["mult2p"] == r["expect"] else "NO (%d vs %d)" % (r["mult2p"], r["expect"])))
    print()
    print("  ALL CHECKS PASS: %s" % ok)
    print()
    print("  => spec(T T*) = n * spec(H) = {2np with multiplicity (n-1)/2, 0 otherwise}.")
    print("  => EXACTLY TWO distinct eigenvalues.  No level repulsion; the counting function is a")
    print("     two-step staircase; Delta_3, Sigma^2 and the Wigner surmise are determined by the")
    print("     two multiplicities alone.  The RMT battery is ANSWERED in closed form, maximally")
    print("     degenerate -- the opposite of a chaotic/GUE spectrum.")
    print("  => the eigenvalue at additive frequency k is p*(1 + chi_2(k^3 + A k + B)):")
    print("     the entire spectral layer of |T(a,b)|^2 IS the quadratic character of the curve.")
