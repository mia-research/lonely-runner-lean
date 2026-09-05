#!/usr/bin/env python3
"""Decisive run: the (p/n) bias at n = 1 mod 8, with PRIME n, at secp's bit size.

Fixes the v2 control normalization: v2 counted jacobi==0 draws (gcd>1, possible only
for composite n) as control failures, pulling the control to 0.39. Here n is PRIME,
so the symbol is a Legendre symbol and the control is exactly 1/2 by construction.

Also measures the decay exponent of the small-p artifact.
Exact integers only.
"""
from math import isqrt
import random, sys

_SMALL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
          101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]
def is_prime(m, bases=(2,3,5,7,11,13,17,19,23,29,31,37)):
    if m < 2: return False
    for q in _SMALL:
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def cornacchia3(p, rnd):
    while True:
        g = rnd.randrange(2, p)
        w = pow(g, (p-1)//3, p)
        if w != 1: break
    r = (2*w + 1) % p
    if r < p - r: r = p - r
    a, b = p, r
    lim = isqrt(p)
    while b > lim: a, b = b, a % b
    c = p - b*b
    if c % 3: return None
    y2 = c // 3; y = isqrt(y2)
    return (b, y) if y*y == y2 else None

def run(bits, target_cell, rnd, seed_note=""):
    """collect instances with n PRIME and n = 1 mod 8; return (N, hits, ctl_hits)"""
    N = hits = ctl = 0
    Nall = hitsall = 0
    while N < target_cell:
        c = rnd.randrange(1 << (bits-1), 1 << bits) | 1
        c += (1 - c) % 3                      # force = 1 mod 3
        if c % 2 == 0: c += 3
        if c % 3 != 1: continue
        if not is_prime(c, bases=(2,3,5,7,11,13)): continue
        p = c
        rep = cornacchia3(p, rnd)
        if rep is None: continue
        a, b = rep
        if a*a + 3*b*b != p: continue
        for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
            n = p + 1 - t
            if n <= 3 or n % 2 == 0 or n % 3 != 1: continue
            pm = p % n
            if pm == 0: continue
            if n % 8 != 1:                     # cheap pre-filter: only the cell we need
                continue
            if not is_prime(n, bases=(2,3,5,7,11,13)): continue
            e2 = (n-1)//2
            N += 1
            hits += (pow(pm, e2, n) == 1)
            ctl  += (pow(rnd.randrange(2, n), e2, n) == 1)
    return N, hits, ctl

rnd = random.Random(31337)
print("=== (p/n)=+1 rate in the cell n = 1 mod 8, PRIME n, matched control ===")
print(f"  {'bits':>5} {'N':>6} {'rate':>8} {'ctl':>8} {'z(rate)':>9} {'z(ctl)':>8}  {'excess':>8}")
plan = [(16, 3000), (20, 3000), (24, 3000), (28, 2000), (32, 2000),
        (40, 1500), (48, 1500), (64, 1200), (96, 900), (128, 800), (192, 700), (256, 700)]
for bits, tgt in plan:
    N, h, c = run(bits, tgt, rnd)
    sd = (N*0.25)**0.5
    print(f"  {bits:>5} {N:>6} {h/N:>8.4f} {c/N:>8.4f} {(h-N/2)/sd:>+9.2f} {(c-N/2)/sd:>+8.2f}"
          f"  {h/N-0.5:>+8.4f}")
    sys.stdout.flush()
