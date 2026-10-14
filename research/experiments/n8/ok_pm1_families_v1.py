#!/usr/bin/env python3
"""EVERY ALL-(+-1) RESONANCE FAMILY HAS AN EXACT RATIONAL VALUE.

f-hat(k) = -sin(pi k/4)/(pi k).  A height-1 resonance p (all coordinates +-1, support k)
contributes, over its whole family {m p} and both signs,

    C_k = 2 * (3/4)^(7-k) * sum_{m>=1} fhat(m)^k ,   fhat even so signs do not matter.

    sum_{m>=1} fhat(m)^k = (-1)^k pi^-k * sum_{m>=1} sin^k(pi m/4)/m^k .

Expand sin^k into a finite Fourier sum.  For k ODD it is a combination of sin(j m pi/4)
with no constant term, and sum_m sin(m x)/m^k is a Bernoulli polynomial -- rational * pi^k.
For k EVEN it is a combination of cos(j m pi/4) plus a constant, and both sum_m cos(mx)/m^k
and zeta(k) are rational multiples of pi^k.  Either way the pi^k cancels:

    >>> every all-(+-1) family value is an EXACT RATIONAL. <<<

This extends AB_SPLIT_v1 §A3, which had closed forms for support 2 only.  Computed here
exactly with Fraction + sympy-free Bernoulli evaluation, and checked numerically.
"""
from fractions import Fraction as F
import math

# sum_{m>=1} cos(m x)/m^2 = pi^2 (1/6 - u/2 + u^2/4)      with x = 2 pi u, u in [0,1]
# sum_{m>=1} sin(m x)/m^3 = pi^3 (u/3 - u^2 + 2u^3/3) ... use Bernoulli B_k(u) directly:
#   sum cos(2 pi m u)/m^(2n) = (-1)^(n+1) (2 pi)^(2n) B_{2n}(u) / (2 (2n)!)
#   sum sin(2 pi m u)/m^(2n+1) = (-1)^(n+1) (2 pi)^(2n+1) B_{2n+1}(u) / (2 (2n+1)!)
def bernoulli_poly(n, u):
    """B_n(u) exactly for Fraction u."""
    B = [F(1)]
    for m in range(1, n + 1):
        s = F(0)
        for k in range(m):
            s += F(math.comb(m + 1, k)) * B[k]
        B.append(-s / F(m + 1))
    return sum(F(math.comb(n, k)) * B[k] * u ** (n - k) for k in range(n + 1))

def S(k, u):
    """sum_{m>=1} cos(2 pi m u)/m^k (k even) or sin(2 pi m u)/m^k (k odd), as r with
       value = r * pi^k."""
    if k % 2 == 0:
        n = k // 2
        return F((-1) ** (n + 1) * 2 ** k, 2 * math.factorial(k)) * bernoulli_poly(k, u)
    else:
        n = (k - 1) // 2
        return F((-1) ** (n + 1) * 2 ** k, 2 * math.factorial(k)) * bernoulli_poly(k, u)

def sin_power_expansion(k):
    """sin^k(t) = const + sum_j c_j * (cos or sin)(j t), returning (const, {j: c_j})."""
    # sin t = (e^{it} - e^{-it})/(2i);  expand binomially, exact rationals with the i's
    from math import comb
    const = F(0); terms = {}
    for r in range(k + 1):
        c = F((-1) ** r * comb(k, r), 2 ** k)          # coefficient of e^{i(k-2r)t} / i^k
        j = k - 2 * r
        if j == 0:
            const += c
        elif j > 0:
            terms[j] = terms.get(j, F(0)) + 2 * c      # pair j with -j
    # divide by i^k : k even -> (-1)^(k/2) and cosines ; k odd -> (-1)^((k-1)/2) and sines
    sign = F((-1) ** (k // 2))
    return const * sign, {j: c * sign for j, c in terms.items()}

print("all-(+-1) resonance families: exact value of sum_{m>=1} fhat(m)^k\n")
print("   k    sum fhat(m)^k        contribution C_k = 2 (3/4)^(7-k) * sum      numeric check")
fh = lambda x: -math.sin(math.pi * x / 4) / (math.pi * x)
for k in range(2, 8):
    const, terms = sin_power_expansion(k)
    # sum_m sin^k(pi m/4)/m^k = const*zeta(k) + sum_j c_j * S(k, j/8)   [x = j*pi/4 = 2 pi (j/8)]
    tot = F(0)
    if const != 0:
        # zeta(k) for even k = |B_k| (2pi)^k / (2 k!)  -> rational * pi^k
        n = k // 2
        zr = F((-1) ** (n + 1) * 2 ** k, 2 * math.factorial(k)) * bernoulli_poly(k, F(0))
        tot += const * zr
    for j, c in terms.items():
        tot += c * S(k, F(j, 8))
    val = F((-1) ** k) * tot                       # (-1)^k pi^-k * (tot * pi^k)
    C = 2 * F(3, 4) ** (7 - k) * val
    num = sum(fh(m) ** k for m in range(1, 400001))
    ok = abs(num - float(val)) < 1e-7
    print(f"  {k:>2}   {str(val):>14}   {str(C):>28}   {float(val):+.9f} vs {num:+.9f}"
          f"  {'OK' if ok else 'DIFFERS'}")
print("\n  (numeric column is a CHECK on the exact rational, never its source)")
