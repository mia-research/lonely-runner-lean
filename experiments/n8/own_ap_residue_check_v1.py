"""Cross-check the Lean form of Prop 6.7 (own-AP residue rule) against the cascade's
own `inWay` computed in floating point.

Lean statement (MomentIterationN.own_ap_residue_rule):
    inWay n ((c/k)*m) (nu/(n*m))  <->  exists M, n*|u*nu - m'*M| < m'
under  c = h*u,  n*k = h*m'  (h > 0, k > 0).  Here h = gcd(c, n*k).

`inWay n x t` is  circDist (x*t) < 1/n,  zones OPEN.
"""
from fractions import Fraction
from math import gcd
import random

n = 8

def circDist(x: Fraction) -> Fraction:
    f = x - (x.numerator // x.denominator)          # Int.fract, exact
    return min(f, 1 - f)

random.seed(20260917)
checked = agree = 0
boundary = 0
for _ in range(40000):
    k  = random.randint(1, 60)          # kappa
    c  = random.randint(-400, 400)
    nu = random.randint(-200, 200)
    h  = gcd(c, n * k)
    if h == 0:
        continue                        # c = 0 and n*k = 0 impossible, but guard
    u  = c // h
    m2 = (n * k) // h                   # m'
    assert c == h * u and n * k == h * m2

    # left-hand side: the cascade's own predicate, exact rationals, m cancels
    lhs = circDist(Fraction(c * nu, k * n)) < Fraction(1, n)

    # right-hand side: the integer rule.  The only M that can work is the nearest one.
    q = round(Fraction(u * nu, m2))
    rhs = any(n * abs(u * nu - m2 * M) < m2 for M in (q - 1, q, q + 1))

    checked += 1
    agree += (lhs == rhs)
    if n * abs(u * nu - m2 * q) == m2:
        boundary += 1

print(f"triples checked : {checked}")
print(f"agree           : {agree}")
print(f"disagree        : {checked - agree}")
print(f"exact-boundary cases (n*|.| == m', open zone excludes) : {boundary}")
