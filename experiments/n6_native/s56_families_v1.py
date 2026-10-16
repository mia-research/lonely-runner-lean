#!/usr/bin/env python3
"""Observation only. Parametric families for §5/§6, in the framework's objects:
  §6 (v3 = c D, v2 = (c-1) D): at each meeting time k/D runners 2 and 3 are on the subject (laps k(c-1), kc); just after
     it they are clear together on J+_k = [k/D + 1/(6 v2), k/D + 5/(6 v3)], just before on J-_k (mirror). Family M6(k, side):
     runner 1 clear on a sub-window of J_k (any lap), runners 4, 5 by window_two there.
  §5 (v1 = c' D, runners 2, 3 within D of each other): family M5(j): runners 2, 3 both on lap j, clear on
     [(j + 1/6)/v2, (j + 5/6)/v3]; runner 1 clear on a sub-window (any lap); runners 4, 5 by window_two.
  Fallbacks: F any 4-block fold (any laps), and the cluster box (0, m, m, m, m).
Measured on primitive §5/§6 sets <= 26 and on random §5/§6 sets with entries up to 400 (seeded): fraction closed by the
family alone, by family + fold, and the rest (listed)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s56_window_v1.py").read().split("sets = [")[0])
def r1_subwindows(v1, L, U):
    """maximal sub-intervals of [L, U] on which runner 1 is clear (exact)."""
    out = []
    for m in range(int(L * v1) - 1, int(U * v1) + 2):
        a = max(L, F(6 * m + 1, 6 * v1)); b = min(U, F(6 * m + 5, 6 * v1))
        if a <= b: out.append((a, b))
    return out
def fam(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; tmax = F(4, v1)
    wins = []
    if v3 % D == 0 and v1 % D != 0:
        for k in range(1, int(tmax * D) + 2):
            t0 = F(k, D)
            wins += [(t0 + F(1, 6 * v2), t0 + F(5, 6 * v3)), (t0 - F(5, 6 * v3), t0 - F(1, 6 * v2))]
    if v1 % D == 0:
        for j in range(0, int(tmax * v2) + 1):
            a, b = F(6 * j + 1, 6 * v2), F(6 * j + 5, 6 * v3)
            if a <= b: wins.append((a, b))
    for L, U in wins:
        if L <= 0: continue
        for a, b in r1_subwindows(v1, L, U):
            if sharp(b - a, v4, v5): return True
    return False
def fold(S):
    tmax = F(3, S[0])
    for blk in combinations(range(5), 4):
        r = [i for i in range(5) if i not in blk][0]
        for L, U, ms in windows([S[i] for i in blk], tmax):
            if S[r] * (U - L) >= F(1, 3): return True
    return False
def cluster(S):
    v1 = S[0]
    for m in range(0, 4 * S[4] // v1 + 2):
        k = (0, m, m, m, m)
        if all((6 * k[i] + 1) * S[j] <= (6 * k[j] + 5) * S[i] for i in range(5) for j in range(5)): return True
    return False
def run(sets, label):
    c = Counter(); rest = []
    for S in sets:
        if fam(S): c["family"] += 1
        elif fold(S): c["fold"] += 1
        elif cluster(S): c["cluster box"] += 1
        else: c["rest"] += 1; rest.append(S)
    print(f"{label}: {len(sets)} sets: {dict(c)}; rest examples {rest[:10]}")
small = [S for S in combinations(range(1, 27), 5) if math.gcd(*S) == 1 and case(S)]
run(small, "§5/§6 <= 26")
random.seed(5)
big = []
while len(big) < 1500:
    S = tuple(sorted(random.sample(range(1, 401), 5)))
    if math.gcd(*S) == 1 and case(S): big.append(S)
run(big, "random §5/§6 <= 400")
