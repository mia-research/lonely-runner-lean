#!/usr/bin/env python3
"""The §6 near-runner fold region, derived. Window after k/D: s in [s0, s1] = [1/(6 v2), 5/(6 v3)], length l.
Runner 4 sweeps lambda4 = v4 l in [1/2, 2/3) (near-runner case); runner 5 needs a clear stretch of runner 4 of reading
length mu = v4/(3 v5) (so that v5 times its time length is >= 1/3). Runner 4 condition: p4 in an arc
A = [1/6 - lambda4 + mu - v4 s0, 5/6 - mu - v4 s0] (mod 1), length 2/3 + lambda4 - 2 mu >= 1/2.
Before k/D (mirror): A' = [1/6 - lambda4 + mu + v4 s1, 5/6 - mu + v4 s1]. Runner 1 clear across the after window if
p1 in [1/6, 5/9], across the before window if p1 in [4/9, 5/6] (sweep v1 l < 5/18).
Checks on the near-runner §6 sets <= 34: lengths of A; whether A and A' together cover the circle; and whether the
orbit k -> (p1, p4) (k = 1..D) meets (after-region) U (before-region): [1/6,5/9] x A  union  [4/9,5/6] x A'."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s6_near_v1.py").read().split("H = int(")[0])
def frac(x): return x - (x.numerator // x.denominator)
def in_arc(p, a, b):  # arc [a, b] mod 1 (length b - a <= 1)
    if b - a >= 1: return True
    return frac(p - a) <= b - a
sets = [S for S in combinations(range(1, 35), 5) if math.gcd(*S) == 1 and s6(S) and not uniform(S)]
lens = Counter(); cover = Counter(); orbit = Counter(); miss = []
for S in sets:
    v1, v2, v3, v4, v5 = S; D = v3 - v2; d = v4 - v3
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); l = s1 - s0; lam = v4 * l; mu = F(v4, 3 * v5)
    A = (F(1, 6) - lam + mu - v4 * s0, F(5, 6) - mu - v4 * s0)
    Ap = (F(1, 6) - lam + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
    lens[round(float(A[1] - A[0]), 2)] += 1
    grid = [F(i, 720) for i in range(720)]
    cover[all(in_arc(p, *A) or in_arc(p, *Ap) for p in grid)] += 1
    hit = any((F(1, 6) <= F(k * v1 % D, D) <= F(5, 9) and in_arc(F(k * d % D, D), *A)) or
              (F(4, 9) <= F(k * v1 % D, D) <= F(5, 6) and in_arc(F(k * d % D, D), *Ap)) for k in range(1, D + 1))
    orbit[hit] += 1
    if not hit: miss.append(S)
print(f"near-runner §6 sets <= 34: {len(sets)}")
print("length of A (rounded):", sorted(lens.items())[:10], "...")
print("A and A' cover the circle (720-point grid):", dict(cover))
print("orbit meets the derived region:", dict(orbit), "misses", miss[:12])
# classify the misses: the orbit's direction. With g1 = gcd(v1, D): if g1 = 1, p4 = lam * p1 (mod 1) with
# lam = delta * v1^{-1} mod D; report lam (and D - lam) and D.
rel = Counter()
for S in miss:
    v1, v2, v3, v4, v5 = S; D = v3 - v2; d = v4 - v3
    if math.gcd(v1, D) == 1:
        lam = d * pow(v1, -1, D) % D; rel[(min(lam, D - lam), "D=%d" % D)] += 1
    else: rel[("gcd(v1,D)>1", "D=%d" % D)] += 1
print("misses by orbit direction (lam = delta / v1 mod D, up to sign) and D:", sorted(rel.items(), key=lambda z: -z[1])[:20])
