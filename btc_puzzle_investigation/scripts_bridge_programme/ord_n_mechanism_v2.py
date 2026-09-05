#!/usr/bin/env python3
"""PREREG_ord_n_mechanism_v1: is the (p/n) excess exactly the forced sf(u)|6 sub-population?
Exact integers only."""
from math import isqrt
import random, sys
from collections import defaultdict

_SMALL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
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
    r = (2*w+1) % p
    if r < p - r: r = p - r
    a, b = p, r
    lim = isqrt(p)
    while b > lim: a, b = b, a % b
    c = p - b*b
    if c % 3: return None
    y2 = c//3; y = isqrt(y2)
    return (b, y) if y*y == y2 else None

def squarefree_part(u):
    """u = s^2 * m, m squarefree; return m. u > 0."""
    m = u
    d = 2
    while d*d <= m:
        if m % (d*d) == 0:
            while m % (d*d) == 0: m //= d*d
        d += 1
    return m

rnd = random.Random(4242)
print("=== H-mech: branch x squarefree-part decomposition, cell n = 1 mod 8, n prime ===\n")
print(f"{'bits':>5} {'N':>6} | {'FORCED sf|6':>12} {'N':>6} | {'FREE sf!|6':>11} {'N':>6} |"
      f" {'pred exc':>9} {'obs exc':>9} {'ratio':>7} {'ctl':>7}")

VIOLATIONS = []
for bits, tgt in [(16,4000),(20,4000),(24,3000),(28,2500),(32,2000),(40,1500),(48,1200),(64,1000)]:
    N = 0
    cells = defaultdict(lambda: [0,0])     # key -> [count, hits]
    ctl_h = 0
    while N < tgt:
        c = rnd.randrange(1 << (bits-1), 1 << bits) | 1
        c += (1 - c) % 3
        if c % 2 == 0: c += 3
        if c % 3 != 1 or not is_prime(c, bases=(2,3,5,7,11,13)): continue
        p = c
        rep = cornacchia3(p, rnd)
        if rep is None: continue
        a, b = rep
        if a*a + 3*b*b != p: continue
        for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
            n = p + 1 - t
            if n <= 3 or n % 2 == 0 or n % 3 != 1 or n % 8 != 1: continue
            pm = p % n
            if pm == 0: continue
            if not is_prime(n, bases=(2,3,5,7,11,13)): continue
            sq = pow(pm, (n-1)//2, n) == 1
            # p = t-1 (mod n) ALWAYS; n = 1 mod 8 => (-1/n)=+1 => (p/n) = (|t-1|/n)
            U = abs(t - 1)
            assert (pm - (t - 1)) % n == 0
            assert 0 < U <= 2*isqrt(p) + 2
            m = squarefree_part(U)
            key = "FORCED sf|6" if 6 % m == 0 else "FREE sf!|6"
            if key == "FORCED sf|6" and not sq:
                VIOLATIONS.append((bits, p, t, n, U, m))
            cells[key][0] += 1; cells[key][1] += sq
            ctl_h += (pow(rnd.randrange(2, n), (n-1)//2, n) == 1)
            N += 1
    def g(k):
        c_, h_ = cells[k]
        return (h_/c_ if c_ else float('nan')), c_
    rL, nL = (float('nan'), 0); rF, nF = g("FORCED sf|6"); rO, nO = g("FREE sf!|6")
    pred = 0.5 * nF / N
    obs = sum(c[1] for c in cells.values())/N - 0.5
    print(f"{bits:>5} {N:>6} | {rF:>12.4f} {nF:>6} | {rO:>11.4f} {nO:>6} |"
          f" {pred:>+9.4f} {obs:>+9.4f} {obs/pred if pred else float('nan'):>7.2f} {ctl_h/N:>7.4f}")
    sys.stdout.flush()

print(f"\nVIOLATIONS of 'sf(u)|6 => (p/n)=+1' : {len(VIOLATIONS)}")
for v in VIOLATIONS[:10]: print("   ", v)
