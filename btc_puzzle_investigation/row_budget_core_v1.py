#!/usr/bin/env python3
"""
row_budget_core_v1.py — instrument core for frontier #17 (the row budget).

    U(a,b,c) = sum_{d=1}^{n-1} e_p(b x_d + c y_d) e_n(a d)

KEY STRUCTURAL FACT, established here before any spec is executed.
For FIXED (b,c) the whole row U(.,b,c) over all a is ONE length-n DFT of
    g_{b,c}(d) = e_p(b x_d + c y_d),  d = 1..n-1,   g(0) = 0 ,
so the conservation

    sum_a |U(a,b,c)|^2 = n * sum_d |g(d)|^2 = n(n-1)

is exactly PARSEVAL, and therefore holds for ANY function of d of modulus 1.
=> It is NOT a property of the curve.  What the previous nulls failed to satisfy
is not "a curve conservation" but simply "being unit-modulus in d".  Any null
built as a unit-modulus function of d satisfies it automatically and for free.
This is recorded here because it changes what the probe can possibly show.

EXACTNESS.  The signal path is the integer exponent (b*x_d + c*y_d) mod p,
computed in exact python/int64 integer arithmetic.  Float enters only in the
DFT and the moments taken from it, never as a threshold applied to data.
"""
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod


def curve_orbit(p, b=7):
    """[d]G for d=0..n-1 as exact integer arrays (X, Y); n prime; returns None otherwise."""
    G = None
    for x in range(1, p):
        r = (x * x * x + b) % p
        if r and pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y:
                G = (x, int(y)); break
    if G is None:
        return None

    def add(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    pts = [None, G]; cur = G
    while True:
        cur = add(cur, G)
        if cur is None: break
        pts.append(cur)
        if len(pts) > 4 * p: return None
    n = len(pts)                     # pts[d] = [d]G, pts[0] = O
    assert add(pts[n - 1], G) is None
    if not all(n % q for q in range(2, int(n ** .5) + 1)):
        return None
    X = np.zeros(n, dtype=np.int64); Y = np.zeros(n, dtype=np.int64)
    for d in range(1, n):
        X[d], Y[d] = pts[d]
    return X, Y, n


class Rows:
    """Length-n row profiles |U(.,b,c)| via one FFT per (b,c)."""

    def __init__(self, p, X, Y, n):
        self.p, self.X, self.Y, self.n = p, X, Y, n
        self.tab = np.exp(2j * np.pi * np.arange(p) / p)     # e_p table

    def g(self, b, c):
        """unit-modulus target; exponent computed in exact integers."""
        e = (b * self.X + c * self.Y) % self.p               # int64, exact
        out = self.tab[e]
        out[0] = 0.0                                          # d = 0 excluded
        return out

    def row(self, b, c):
        """|U(a,b,c)| for all a, as a length-n float array."""
        return np.abs(np.fft.fft(self.g(b, c)))


def selftest():
    print("=" * 78)
    print("INSTRUMENT CHECK — the row budget is PARSEVAL (forced), plus a brute-force")
    print("=" * 78)
    rng = np.random.default_rng(11)
    for p in (163, 433, 991, 2089):
        r = curve_orbit(p)
        if r is None:
            print(f"  p={p}: no prime-order curve"); continue
        X, Y, n = r
        R = Rows(p, X, Y, n)
        worst = 0.0
        for _ in range(12):
            b = int(rng.integers(0, p)); c = int(rng.integers(0, p))
            u = R.row(b, c)
            budget = float((u ** 2).sum())
            worst = max(worst, abs(budget - n * (n - 1)) / (n * (n - 1)))
        print(f"  p={p:>5} n={n:>5}   max rel |sum_a |U|^2 - n(n-1)| = {worst:.3e}")

    # brute force at small p: direct double sum vs FFT
    print("\n  brute-force direct sum vs FFT, p=163")
    X, Y, n = curve_orbit(163)
    R = Rows(163, X, Y, n)
    b, c = 5, 9
    u = R.row(b, c)
    d = np.arange(1, n)
    e = (b * X[1:] + c * Y[1:]) % 163
    err = 0.0
    for a in (0, 1, 2, 7, n - 1):
        direct = np.sum(np.exp(2j * np.pi * e / 163) * np.exp(-2j * np.pi * a * d / n))
        err = max(err, abs(abs(direct) - u[a]))
    print(f"    max |direct| - |FFT| over 5 rows = {err:.3e}")

    # the SAME budget holds for a random unit-modulus target -> forced, not curve
    print("\n  a RANDOM unit-modulus target satisfies the same budget (=> forced):")
    gr = np.exp(2j * np.pi * rng.random(n)); gr[0] = 0
    ur = np.abs(np.fft.fft(gr))
    print(f"    rel |sum_a |U|^2 - n(n-1)| = "
          f"{abs((ur**2).sum() - n*(n-1))/(n*(n-1)):.3e}")
    print("    => the conservation is Parseval for a unit-modulus sequence in d.")
    print("       It is NOT a curve property, and any unit-modulus null carries it free.")


if __name__ == "__main__":
    selftest()
