"""Local analysis at the three tight configurations (tight_search_v2): does isolation survive every
small deformation, at an opening/closing of the two runners that pin each class?

Tight set T (disparities), lonely only at a/8.  At class a the pinning runners read exactly 1/8 or
7/8 (mod 1) at t = a/8.  Deform d -> d(1 + r_d), |r_d| <= rho.  Candidates: every opening (M+1/8)/d
and closing (M+7/8)/d of the pinning runners of classes a and 8 - a, with M within 1 of the
undeformed lap.  Claim (as at the AP): for small rho, some class pair {1,7} or {3,5} survives at one
of these named instants.  Exact fractions.
"""
import random
from fractions import Fraction as F
from math import floor
def nd(x): x = x % 1; return min(x, 1 - x)
TIGHT = [(1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 12), (1, 4, 5, 6, 7, 11, 13)]
def pinners(T, a):
    return [i for i, d in enumerate(T) if (d * F(a, 8)) % 1 in (F(1, 8), F(7, 8))]
def cands(T, D, a):
    out = []
    for aa in (a, 8 - a):
        for i in pinners(T, aa):
            x = T[i] * F(aa, 8)
            for M in (floor(x) - 1, floor(x), floor(x) + 1):
                for s in (F(1, 8), F(7, 8)):
                    t = (M + s) / D[i]
                    if t > 0: out.append(t)
    return out
rnd = random.Random(46)
for T in TIGHT:
    print(f"{T}: pinning runners by class: {{a: [T[i] for i in pinners]}} = {{{', '.join(f'{a}: {[T[i] for i in pinners(T, a)]}' for a in (1, 3, 5, 7))}}}")
    for rho in (F(1, 50), F(1, 100), F(1, 200), F(1, 400)):
        ok = {1: 0, 3: 0}; either = 0; n = 2000
        for _ in range(n):
            D = [d * (1 + F(rnd.randrange(-10**5, 10**5 + 1), 10**5) * rho) for d in T]
            got = {a: any(all(nd(x * t) >= F(1, 8) for x in D) for t in cands(T, D, a)) for a in (1, 3)}
            for a in got: ok[a] += got[a]
            either += got[1] or got[3]
        print(f"   |r| <= {rho}: pair {{1,7}} survives {ok[1]}/{n};  pair {{3,5}} {ok[3]}/{n};  at least one pair {either}/{n}")
