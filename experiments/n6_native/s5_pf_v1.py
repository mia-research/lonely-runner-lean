#!/usr/bin/env python3
"""§5, k = v1/D >= 2, sets not closed by the uniform pair window at j0 (s5_obs_v4.uni_j0).
Simple pair-window fold at lap j: on P_j = [s0, s1] = [(j+1/6)/v2, (j+5/6)/v3] runner 1 reads p1 + v1 (t - s0),
p1 = v1 s0 (mod 1); clear across all of P_j when p1 in [1/6, 5/6 - v1 (s1 - s0)]. Runner 4's reading sweeps
[x, x + v4 (s1 - s0)], x = v4 s0 (mod 1); runner 5 is folded alone when that sweep meets a band [m+1/6, m+5/6] in a stretch of
length >= mu = v4/(3 v5). Also with 4 and 5 swapped (runner 5's sweep in band for a stretch >= v5/(3 v4)... i.e. runner 4
folded). Report: closes by simple fold (which j, p1, x), by exact pair fold (runner 1 only partly clear: s5_obs_v1 class C),
other; and v4 ell_j and mu at the closing j."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
exec(open("s5_obs_v4.py").read().split("\ndef run(sets")[0])
def frac(x): return x - math.floor(x)
def stretch(x, w):
    """longest stretch of [x, x+w] inside some band [m+1/6, m+5/6]"""
    best = F(0)
    for m in range(math.floor(x) - 1, math.floor(x + w) + 2):
        a, b = max(x, m + F(1, 6)), min(x + w, m + F(5, 6))
        if b > a: best = max(best, b - a)
    return best
def simple_fold(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    for j, s0, s1 in pair(S):
        p1 = frac(v1 * s0); sw1 = v1 * (s1 - s0)
        if not (F(1, 6) <= p1 and p1 + sw1 <= F(5, 6)): continue
        x = v4 * s0; w = v4 * (s1 - s0)
        if stretch(x, w) >= F(v4, 3 * v5): return ("fold5", j)
        y = v5 * s0; w5 = v5 * (s1 - s0)
        if stretch(y, w5) >= F(v5, 3 * v4): return ("fold4", j)
    return None
def run(sets, label):
    c = Counter(); ex = []
    for S in sets:
        v1, v2, v3 = S[:3]; D = v3 - v2
        if v1 // D < 2 or uni_j0(S): continue
        r = simple_fold(S)
        if r: c["simple pair fold, " + r[0]] += 1; continue
        how, _ = classify(S); c["not simple: " + how] += 1
        if len(ex) < 12: ex.append((S, how))
    print(f"== {label}: {dict(c)}"); print("   examples", ex)
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S)], f"primitive §5 k>=2 <= {H}, not uniform at j0")
random.seed(56); big = []
while len(big) < 3000:
    S = tuple(sorted(random.sample(range(1, 3001), 5)))
    if math.gcd(*S) == 1 and s5(S) and S[0] // (S[2] - S[1]) >= 2: big.append(S)
run(big, "random §5 k>=2 <= 3000, not uniform at j0")
