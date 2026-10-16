#!/usr/bin/env python3
"""The §6 branch D >= 15, gcd(v1, D) = 1: what closes each set, in order: uniform; generic (|lam| >= 2); lam = 0
(check it is uniform); sum lemma with a k in I (v4 = v3 + v1); diagonal two-window region (lam = +-1): length of
([1/6,5/9] cap A) and ([4/9,5/6] cap A') on the circle, and whether a multiple of 1/D lies in one; rest listed.
Primitive §6 sets with D >= 15 up to H (D >= 15 needs v3 >= 30), and random ones up to 3000."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
def s6(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v3 % D == 0 and v1 % D != 0
def frac(x): return x - (x.numerator // x.denominator)
def arc_cap(I, A):
    """length of interval I = [a,b] (inside [0,1]) intersected with arc A = [x, x+L] mod 1, and a point list"""
    a, b = I; x, L = frac(A[0]), A[1] - A[0]
    if L >= 1: return b - a
    tot = F(0)
    for sh in (-1, 0, 1):
        lo, hi = max(a, x + sh), min(b, x + L + sh)
        if lo < hi: tot += hi - lo
    return tot
def classify(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if 4 * v2 * v3 <= v4 * (5 * v2 - v3): return "uniform"
    lam = v4 * pow(v1, -1, D) % D
    lam = lam - D if lam > D // 2 else lam
    if abs(lam) >= 2: return "generic"
    if lam == 0: return "lam 0 not uniform (!)"
    if v4 == v3 + v1:
        lo, hi = F(1, 3) + F(v3, 3 * v5), F(5, 6) * (1 - F(v1, v3))
        if any(lo <= F(j, D) <= hi for j in range(D)): return "sum lemma"
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); L4 = v4 * (s1 - s0); mu = F(v4, 3 * v5)
    A = (F(1, 6) - L4 + mu - v4 * s0, F(5, 6) - mu - v4 * s0); Ap = (F(1, 6) - L4 + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
    def on_arc(p, Ar):
        return (Ar[1] - Ar[0] >= 1) or frac(p - Ar[0]) <= Ar[1] - Ar[0]
    if any((F(1, 6) <= F(j, D) <= F(5, 9) and on_arc(F(lam * j % D, D), A)) or
           (F(4, 9) <= F(j, D) <= F(5, 6) and on_arc(F(lam * j % D, D), Ap)) for j in range(D)):
        return f"diagonal region, lam {lam}"
    return f"rest, lam {lam}" + (", sum" if v4 == v3 + v1 else "")
def run(sets, label):
    c = Counter(); ex = []
    for S in sets:
        k = classify(S); c[k] += 1
        if k.startswith("rest") and len(ex) < 8: ex.append(S)
    print(f"{label}: {len(sets)} sets:", dict(sorted(c.items(), key=lambda z: -z[1])), "rest examples", ex)
H = int(sys.argv[1]) if len(sys.argv) > 1 else 60
small = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s6(S) and S[2] - S[1] >= 15 and math.gcd(S[0], S[2] - S[1]) == 1]
run(small, f"§6, D >= 15, gcd 1, <= {H}")
random.seed(15); big = []
while len(big) < 3000:
    S = tuple(sorted(random.sample(range(1, 3001), 5)))
    if math.gcd(*S) == 1 and s6(S) and S[2] - S[1] >= 15 and math.gcd(S[0], S[2] - S[1]) == 1: big.append(S)
run(big, "random, <= 3000")
