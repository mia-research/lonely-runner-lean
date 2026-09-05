#!/usr/bin/env python3
"""Exact power ceiling of the pooled rank-sum T_dev, in the K -> infinity limit.

T_dev = R_sextant + R_norm + R_flap + R_CT,  each R_l in [0,K] an integer
permutation rank against a common control ensemble of size K.

Scale by K.  In the limit of large K each rank is U(0,1):
  H0 (no deviation)          : T/K ~ Irwin-Hall(4)
  H1 (ONE law fully saturated,
      i.e. R_flap = K exactly,
      other three uninformative): T/K ~ 1 + Irwin-Hall(3)

That is the BEST CASE for the pooled statistic against a deviation confined to
one law: the informative rank is pinned at its maximum.  The resulting power is
therefore an upper bound on what T_dev can achieve against a concentrated
effect, at ANY effect size and ANY K.

Exact rational arithmetic; no float in the computation.
"""

from fractions import Fraction as F
from math import comb


def ih_cdf(n: int, x: F) -> F:
    """Exact CDF of the Irwin-Hall(n) distribution (sum of n iid U(0,1))."""
    if x <= 0:
        return F(0)
    if x >= n:
        return F(1)
    total = F(0)
    k = 0
    while k <= x:
        total += F((-1) ** k * comb(n, k)) * (x - k) ** n
        k += 1
    from math import factorial
    return total / factorial(n)


def ih_quantile(n: int, q: F, iters: int = 200) -> F:
    """Exact-arithmetic bisection for the q-quantile of Irwin-Hall(n)."""
    lo, hi = F(0), F(n)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if ih_cdf(n, mid) < q:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


print(__doc__)
print(f"{'alpha':>8} {'crit value c':>16} {'T_dev power ceiling':>22}")
print("-" * 50)

for alpha in (F(5, 100), F(1, 100)):
    # one-sided upper tail under H0 = Irwin-Hall(4)
    c = ih_quantile(4, 1 - alpha)
    # power under H1 = 1 + Irwin-Hall(3):  P(1 + IH3 > c)
    power = 1 - ih_cdf(3, c - 1)
    print(f"{float(alpha):>8.2f} {float(c):>16.6f} {float(power):>22.4f}")

print()
print("Independent of K: both H0 and H1 laws are expressed in units of K, so the")
print("ceiling does not move as the control ensemble grows.  K=199 and K=10^4 give")
print("the same limit.")
print()

# Sanity: the null is calibrated by construction (the quantile is exact).
c05 = ih_quantile(4, F(95, 100))
print(f"check  P(IH4 > c) at alpha=0.05 : {float(1 - ih_cdf(4, c05)):.6f}  (target 0.05)")

# What a SINGLE-law test achieves when that law's rank saturates:
# R_flap = K  =>  its own permutation p-value = 1/(1+K) -> fires at any usable alpha.
print("single-law flap test, same saturated case: p = 1/(1+K); fires for K >= 99 at alpha=0.01")
