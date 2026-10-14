r"""
tb_ray_v1 -- the EXACT per-ray closed form, and the sharpest termwise bound.

Every nonzero n in the resonance lattice is k*p for a unique primitive p (up to
sign) and k != 0.  Summing the k-series in closed form FIRST is strictly sharper
than bounding |Ghat(n)| term by term, and the result is an exact RATIONAL number
per ray:

  Ghat(n) = S(n mod 4) PROD_rho A(n_rho),   A(m) = (1 - e(-m/4))/(2 pi i m), A(0)=1/4.

  Ray(p) := SUM_{k != 0} Ghat(k p)
          = (1/4)^{4-s} / ( (2 pi i)^s PROD_{rho in T} p_rho )
            * SUM_{r = 1,2,3}  W_p(r) Z_s(r) ,

  T = supp p, s = |T|,  W_p(r) = S(r p) PROD_{rho in T} ( 1 - (-i)^{r p_rho} ),
  Z_s(r) = SUM_{k = r mod 4, k != 0} k^{-s}:

      Z_2(1) = Z_2(3) = pi^2/8 ,  Z_2(2) = pi^2/16
      Z_3(1) = pi^3/32 = -Z_3(3) , Z_3(2) = 0
      Z_4(1) = Z_4(3) = pi^4/96 ,  Z_4(2) = pi^4/768

so every power of pi cancels and

      s = 2:  Ray(p) = -[ W(1)/8 + W(2)/16 + W(3)/8 ] / (64 PROD p)
      s = 3:  Ray(p) = i [ W(1) - W(3) ] / (1024 PROD p)
      s = 4:  Ray(p) =  [ (W(1)+W(3))/96 + W(2)/768 ] / (16 PROD p)

with PROD p = PROD_{rho in T} p_rho.  Ray(p) is a rational number (the imaginary
part is checked to be exactly 0).  If any p_rho with rho in T is = 0 mod 4 then
A(k p_rho) = 0 for every k and Ray(p) = 0 exactly.

Exports:
    ray_value(p)   exact Fraction
    ray_cap(s)     max over residue classes p mod 4 of |Ray(p)| * PROD|p_rho|
    primitive_rays(e, N)  primitive p in L(e), one per +- pair, height <= N
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import itertools

from tb_fourier_v1 import ST, GOOD

RHO = (1, 3, 5, 7)


# ------------------------------------------------- exact Gaussian rationals
def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def gscale(a, c):
    return (a[0] * c, a[1] * c)


def pow_mi(k):
    """(-i)^k"""
    return [(F(1), F(0)), (F(0), F(-1)), (F(-1), F(0)), (F(0), F(1))][k % 4]


def S_g(j):
    re, im = ST[tuple(x % 4 for x in j)]
    return (F(re), F(im))


def ray_value(p):
    T = [i for i in range(4) if p[i]]
    s = len(T)
    if s < 2:
        return F(0)
    if any(p[i] % 4 == 0 for i in T):
        return F(0)
    prod = 1
    for i in T:
        prod *= p[i]
    W = {}
    for r in (1, 2, 3):
        z = S_g(tuple(r * x for x in p))
        for i in T:
            f = pow_mi(r * p[i])
            z = gmul(z, (F(1) - f[0], -f[1]))
        W[r] = z
    if s == 2:
        num = gadd(gadd(gscale(W[1], F(1, 8)), gscale(W[2], F(1, 16))),
                   gscale(W[3], F(1, 8)))
        val = gscale(num, F(-1, 64 * prod))
    elif s == 3:
        num = gadd(W[1], gscale(W[3], -1))
        num = gmul((F(0), F(1)), num)                 # multiply by i
        val = gscale(num, F(1, 1024 * prod))
    else:
        num = gadd(gscale(gadd(W[1], W[3]), F(1, 96)), gscale(W[2], F(1, 768)))
        val = gscale(num, F(1, 16 * prod))
    assert val[1] == 0, (p, val)
    return val[0]


# --------------------------------------------------------------- ray caps
_CAP = {}


def ray_cap(s):
    """max over p mod 4 (support size s, no coordinate = 0 mod 4 on the support)
    of |Ray(p)| * |PROD_{rho in T} p_rho|.   Exact Fraction."""
    if s in _CAP:
        return _CAP[s]
    best = F(0)
    for T in itertools.combinations(range(4), s):
        for res in itertools.product((1, 2, 3), repeat=s):
            p = [0, 0, 0, 0]
            for t, r in zip(T, res):
                p[t] = r
            v = abs(ray_value(tuple(p)))
            prod = 1
            for t in T:
                prod *= p[t]
            best = max(best, v * prod)
    _CAP[s] = best
    return best


_CAPA = {}


def ray_cap_adm(s):
    """max |Ray(p)| * PI(p) over the residue patterns p mod 4 that a PRIMITIVE
    resonance of an all-odd speed tuple can have: no support coordinate = 0 mod 4
    (else Ray = 0), an EVEN number of odd coordinates (SUM n_rho e_rho = 0 with all
    e_rho odd forces SUM n_rho even), and not all support coordinates = 2 mod 4
    (that contradicts primitivity).  Exact Fraction."""
    if s in _CAPA:
        return _CAPA[s]
    best, arg = F(0), None
    for T in itertools.combinations(range(4), s):
        for res in itertools.product((1, 2, 3), repeat=s):
            nodd = sum(1 for r in res if r % 2)
            if nodd % 2 or nodd == 0:
                continue
            p = [0, 0, 0, 0]
            for t, r in zip(T, res):
                p[t] = r
            v = abs(ray_value(tuple(p)))
            prod = 1
            for t in T:
                prod *= p[t]
            if v * prod > best:
                best, arg = v * prod, tuple(p)
    _CAPA[s] = (best, arg)
    return _CAPA[s]


# ------------------------------------------------------------ enumeration
def primitive_rays(e, N):
    """primitive p with p.e = 0, ||p||_inf <= N, one representative per +- pair."""
    out = []
    for n3 in range(-N, N + 1):
        for n5 in range(-N, N + 1):
            for n7 in range(-N, N + 1):
                sm = n3 * e[1] + n5 * e[2] + n7 * e[3]
                if sm % e[0]:
                    continue
                n1 = -sm // e[0]
                if abs(n1) > N or (n1 == n3 == n5 == n7 == 0):
                    continue
                p = (n1, n3, n5, n7)
                if reduce(gcd, [abs(x) for x in p]) != 1:
                    continue
                for x in p:                       # keep the one with first nonzero > 0
                    if x:
                        if x < 0:
                            p = None
                        break
                if p is not None:
                    out.append(p)
    return out


if __name__ == "__main__":
    from ob_fast_v1 import o_fast

    print("=" * 78)
    print("ray caps:  max over p mod 4 of |Ray(p)| * PROD_{rho in supp} |p_rho|")
    print("=" * 78)
    for s in (2, 3, 4):
        c = ray_cap(s)
        print(f"   s = {s}:  cap = {c} = {float(c):.7f}")

    print()
    print("=" * 78)
    print("CHECK: o(e) - 3/32 = SUM over primitive rays p in L(e) of Ray(p)")
    print("=" * 78)
    tests = [(1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (9, 3, 5, 7),
             (25, 11, 77, 7), (41, 43, 13, 15)]
    for e in tests:
        o = o_fast(e)
        print(f"   e = {str(e):>18}  o - 3/32 = {float(o - F(3,32)):+.7f}")
        for N in (12, 40, 120):
            tot = F(0)
            for p in primitive_rays(e, N):
                tot += ray_value(p)
            print(f"        rays to height {N:4d}: {float(tot):+.7f}   "
                  f"err {float(tot - (o - F(3,32))):+.2e}")
