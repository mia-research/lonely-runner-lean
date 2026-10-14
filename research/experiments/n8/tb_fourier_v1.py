r"""
tb_fourier_v1 -- the BOX-Fourier form of the character identity, and its verification.

Predecessor form (rt_char_v1, Thm 1):  o = (1/256) SUM_w K(w) eps(w) I(w).
That form puts the Klein characters first and hides the frequency decay inside I(w).

The form used here puts the FREQUENCY first.  Let

    G(v) = SUM over the 24 good c in {0,1,2,3}^4 of PROD_rho 1[ floor(4 v_rho) = c_rho ],
    good c  <=>  c_rho XOR mu_rho all distinct,  mu = (0,1,2,3).

G is the indicator of a union of 24 axis-parallel boxes of side 1/4 in T^4, of total
volume 24/256 = 3/32.  Its Fourier coefficients factor completely:

    Ghat(n) = S(n mod 4) * PROD_rho A(n_rho),                                     (*)

    A(m) = (1/4) INT_0^1 e(-m u / 4) du  =  1/4              if m = 0
                                        =  (1 - e(-m/4)) / (2 pi i m)  otherwise,
    S(j) = SUM over the 24 good c of (-i)^{ SUM_rho j_rho c_rho }   in Z[i].

|A(m)| = |sin(pi m/4)| / (pi |m|), so

    |A(m)| = 0                for m = 0 mod 4, m != 0      <-- kills every such frequency
           = 1 / (pi |m|)     for m = 2 mod 4
           = 1 / (sqrt2 pi |m|) for m odd
     A(0)  = 1/4.

And o(e) = SUM over the resonance lattice L(e) = {n : n.e = 0} of Ghat(n), in the
Fejer/Cesaro sense (see reports/n8_tail_bound.md Sec.2 for the honest statement --
here the identity is only CHECKED numerically, on truncations).

This module exports:
    S_table()          -- exact dict (Z/4)^4 -> complex Gaussian integer (as a pair)
    Ghat(n)            -- exact-ish (S is exact; A uses mpmath-free closed form)
    absA(m)            -- EXACT Fraction bound  |A(m)| <= absA_num(m), see below
    resonances(e, N)   -- all n in L(e) with ||n||_inf <= N
"""
from fractions import Fraction as F
from math import gcd
import cmath
import itertools

MU = (0, 1, 2, 3)
RHO = (1, 3, 5, 7)


# ------------------------------------------------------------------ good set
def good_c():
    out = []
    for c in itertools.product(range(4), repeat=4):
        if len({cr ^ mr for cr, mr in zip(c, MU)}) == 4:
            out.append(c)
    return out


GOOD = good_c()
assert len(GOOD) == 24


# ------------------------------------------------------------- S(j), exact Z[i]
def _pow_mi(k):
    """(-i)^k as an exact (re, im) integer pair."""
    return [(1, 0), (0, -1), (-1, 0), (0, 1)][k % 4]


def S_table():
    """S(j) for all j in (Z/4)^4, as exact integer pairs (re, im)."""
    out = {}
    for j in itertools.product(range(4), repeat=4):
        re = im = 0
        for c in GOOD:
            k = sum(jr * cr for jr, cr in zip(j, c)) % 4
            a, b = _pow_mi(k)
            re += a
            im += b
        out[j] = (re, im)
    return out


ST = S_table()


def S(n):
    return ST[tuple(x % 4 for x in n)]


def absS2(n):
    """|S(n)|^2, an exact integer."""
    re, im = S(n)
    return re * re + im * im


# --------------------------------------------------------------------- A(m)
def A(m):
    if m == 0:
        return 0.25 + 0j
    return (1 - cmath.exp(-2j * cmath.pi * m / 4)) / (2j * cmath.pi * m)


def absA_sq(m):
    """EXACT Fraction for |A(m)|^2 * pi^2 :  = sin^2(pi m/4)/m^2.  Returns the
    rational r with |A(m)|^2 = r / pi^2 (m != 0)."""
    s2 = {0: F(0), 1: F(1, 2), 2: F(1), 3: F(1, 2)}[m % 4]
    return s2 / (m * m)


def Ghat(n):
    z = complex(S(n)[0], S(n)[1])
    for m in n:
        z *= A(m)
    return z


# ------------------------------------------------------------- resonances
def resonances(e, N):
    """all n != 0 in Z^4 with n.e = 0 and ||n||_inf <= N."""
    out = []
    e1 = e[0]
    for n3 in range(-N, N + 1):
        for n5 in range(-N, N + 1):
            for n7 in range(-N, N + 1):
                s = n3 * e[1] + n5 * e[2] + n7 * e[3]
                if s % e1:
                    continue
                n1 = -s // e1
                if abs(n1) > N or (n1 == n3 == n5 == n7 == 0):
                    continue
                out.append((n1, n3, n5, n7))
    return out


# --------------------------------------------------------------------- report
if __name__ == "__main__":
    from ob_fast_v1 import o_fast

    print("=" * 78)
    print("S(j) = SUM over the 24 good c of (-i)^(j.c)   -- exact Gaussian integers")
    print("=" * 78)
    print(f"   S(0,0,0,0) = {ST[(0,0,0,0)]}   (= 24, the main term 24/256 = 3/32)")

    # distribution of |S|^2 by support pattern of j restricted to j_rho != 0 mod 4
    bysup = {}
    for j in itertools.product(range(4), repeat=4):
        k = sum(1 for x in j if x)
        bysup.setdefault(k, []).append(absS2(j))
    for k in sorted(bysup):
        v = bysup[k]
        print(f"   |supp j mod 4| = {k}:  {len(v):3d} classes, "
              f"max |S|^2 = {max(v):4d}  (max|S| = {max(v)**0.5:7.4f}), "
              f"mean |S|^2 = {sum(v)/len(v):7.3f}")
    tot = sum(absS2(j) for j in itertools.product(range(4), repeat=4))
    print(f"   SUM_j |S(j)|^2 = {tot}   (Parseval: must be 256*24 = {256*24})")

    # frequencies that can ever contribute: no coordinate = 0 mod 4 unless it is 0.
    print("\n   A(m) = 0 for every m = 0 mod 4 with m != 0, so a contributing")
    print("   resonance n has EVERY nonzero coordinate n_rho != 0 mod 4.")

    # max |S| on the live classes (all coords in {0,1,2,3} with the 0-mod-4 rule
    # already imposed: j_rho in {1,2,3} on the support)
    print("\n   max |S(j)| over j whose nonzero coords lie in {1,2,3}, by support size:")
    for k in range(5):
        vals = [absS2(j) for j in itertools.product(range(4), repeat=4)
                if sum(1 for x in j if x) == k]
        print(f"      |supp| = {k}: max |S| = {max(vals) ** 0.5:.6f}  "
              f"(|S|^2 = {max(vals)})")

    print()
    print("=" * 78)
    print("CHECK: Ghat(n) = S(n) PROD A(n_rho) against a direct numerical integral")
    print("=" * 78)
    import random
    random.seed(11)
    worst = 0.0
    for _ in range(12):
        n = tuple(random.randrange(-6, 7) for _ in range(4))
        # direct:  Ghat(n) = SUM_{c good} PROD_rho INT_{c/4}^{(c+1)/4} e(-n v) dv
        z = 0 + 0j
        for c in GOOD:
            t = 1 + 0j
            for m, cr in zip(n, c):
                if m == 0:
                    t *= 0.25
                else:
                    t *= (cmath.exp(-2j * cmath.pi * m * (cr + 1) / 4)
                          - cmath.exp(-2j * cmath.pi * m * cr / 4)) / (-2j * cmath.pi * m)
            z += t
        worst = max(worst, abs(z - Ghat(n)))
    print(f"   max |direct - formula| over 12 random n: {worst:.3e}")

    print()
    print("=" * 78)
    print("CHECK: o(e) = SUM_{n in L(e)} Ghat(n)  (truncated at height N)")
    print("=" * 78)
    tests = [(1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (9, 3, 5, 7),
             (25, 11, 77, 7), (41, 43, 13, 15)]
    for e in tests:
        exact = o_fast(e)
        line = f"   e = {str(e):>18}  o = {float(exact):.7f}   partial sums:"
        print(line)
        for N in (10, 40, 120):
            s = 3 / 32
            for n in resonances(e, N):
                s += Ghat(n).real
            print(f"        N = {N:4d}   {s:.7f}   err {s - float(exact):+.2e}")
