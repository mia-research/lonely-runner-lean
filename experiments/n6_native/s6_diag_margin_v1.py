#!/usr/bin/env python3
"""Margins for the lam = +-1 cases of the D >= 15, gcd 1 branch (not uniform). On the diagonal p4 = lam p1, the usable
p1-set is U = {p in [1/6,5/9] : lam p in A} union {p in [4/9,5/6] : lam p in A'} (E94 arcs), plus, when v4 = v3 + v1,
the sum interval I. Report the longest interval in U (and in U union I) in units of 1/D, over all such sets <= 80;
a value >= 1 guarantees a grid point j/D."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
def s6(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v3 % D == 0 and v1 % D != 0
def frac(x): return x - (x.numerator // x.denominator)
def longest(intervals):
    iv = sorted(intervals); best = F(0); cur = None
    for a, b in iv:
        if cur and a <= cur[1]: cur = (cur[0], max(cur[1], b))
        else:
            if cur: best = max(best, cur[1] - cur[0])
            cur = (a, b)
    if cur: best = max(best, cur[1] - cur[0])
    return best
def preimage(I, lam, Ar):
    """{p in I : lam p in arc Ar (mod 1)} as intervals, lam = +-1"""
    a, b = I; x, L = Ar[0], Ar[1] - Ar[0]; out = []
    if L >= 1: return [I]
    for sh in range(-3, 4):
        lo, hi = x + sh, x + L + sh
        if lam == -1: lo, hi = -hi, -lo
        l2, h2 = max(a, lo), min(b, hi)
        if l2 < h2: out.append((l2, h2))
    return out
worst = None; cnt = Counter()
for S in combinations(range(1, 81), 5):
    if math.gcd(*S) != 1 or not s6(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if D < 15 or math.gcd(v1, D) != 1 or 4 * v2 * v3 <= v4 * (5 * v2 - v3): continue
    lam = v4 * pow(v1, -1, D) % D; lam = lam - D if lam > D // 2 else lam
    if abs(lam) != 1: continue
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); L4 = v4 * (s1 - s0); mu = F(v4, 3 * v5)
    A = (F(1, 6) - L4 + mu - v4 * s0, F(5, 6) - mu - v4 * s0); Ap = (F(1, 6) - L4 + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
    U = preimage((F(1, 6), F(5, 9)), lam, A) + preimage((F(4, 9), F(5, 6)), lam, Ap)
    if v4 == v3 + v1:
        lo, hi = F(1, 3) + F(v3, 3 * v5), F(5, 6) * (1 - F(v1, v3))
        if lo < hi: U.append((lo, hi))
    m = longest(U) * D
    cnt[min(int(m), 10)] += 1
    if worst is None or m < worst[0]: worst = (m, S, lam)
print("longest usable interval x D (capped at 10):", dict(sorted(cnt.items())))
print("worst:", float(worst[0]), worst[1:])
