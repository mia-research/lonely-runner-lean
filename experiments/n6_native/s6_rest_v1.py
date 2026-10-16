#!/usr/bin/env python3
"""Observation. §6 sets the native branch leaves: D not | v1 and (D < 15 or g = gcd(v1, D) > 1).
Per set, the first of: uniform (s6_meeting_uniform, proved for any D not | v1); region (some k in Z/D with runner 1's
phase in [1/6,5/9] and runner 4 on the arc A after k/D, or the mirror before); sum lemma (v4 = v3 + v1, some k/D phase in
I); exact meeting fold (s6_near_v1's meet_fold); else rest. Recorded: D, g, D' = D/g, c, and for gcd > 1 whether the
region test still passes when runner 4's phases are restricted to one k per runner-1 phase (to see whether the extra
k's -- runner 4 moving by delta/g at fixed runner-1 phase -- are what makes it work)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
def frac(x): return x - (x.numerator // x.denominator)
def rest_region(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    if v3 <= 3 * v1 or v3 % D or v1 % D == 0: return False
    return D < 15 or math.gcd(v1, D) > 1
def uniform(S): v1, v2, v3, v4, v5 = S; return 4 * v2 * v3 <= v4 * (5 * v2 - v3)
def arcs(S):
    v1, v2, v3, v4, v5 = S
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); L4 = v4 * (s1 - s0); mu = F(v4, 3 * v5)
    return (F(1, 6) - L4 + mu - v4 * s0, F(5, 6) - mu - v4 * s0), (F(1, 6) - L4 + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
def on_arc(p, Ar): return (Ar[1] - Ar[0] >= 1) or (Ar[1] >= Ar[0] and frac(p - Ar[0]) <= Ar[1] - Ar[0])
def region_ks(S, ks):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; A, Ap = arcs(S); d = v4 - v3
    for k in ks:
        p1, p4 = F(k * v1 % D, D), F(k * d % D, D)
        if (F(1, 6) <= p1 <= F(5, 9) and on_arc(p4, A)) or (F(4, 9) <= p1 <= F(5, 6) and on_arc(p4, Ap)): return k
    return None
def sum_ok(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if v4 != v3 + v1: return False
    lo, hi = F(1, 3) + F(v3, 3 * v5), F(5, 6) * (1 - F(v1, v3))
    return any(lo <= F(k * v1 % D, D) <= hi for k in range(D))
def clear_sub(v, L, U):
    out = []
    for m in range(int(L * v) - 1, int(U * v) + 2):
        a = max(L, F(6 * m + 1, 6 * v)); b = min(U, F(6 * m + 5, 6 * v))
        if a <= b: out.append((a, b))
    return out
def meet_fold(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    for k in range(1, D + 1):
        t0 = F(k, D)
        for L, U in ((t0 + F(1, 6 * v2), t0 + F(5, 6 * v3)), (t0 - F(5, 6 * v3), t0 - F(1, 6 * v2))):
            for a1, b1 in clear_sub(v1, L, U):
                for a4, b4 in clear_sub(v4, a1, b1):
                    if v5 * (b4 - a4) >= F(1, 3): return k
    return None
def classify(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if uniform(S): return "uniform"
    if region_ks(S, range(D)) is not None: return "region"
    if sum_ok(S): return "sum lemma"
    if meet_fold(S): return "meeting fold"
    return "rest"
def run(sets, label):
    tot = Counter(); byD = defaultdict(Counter); byg = defaultdict(Counter); ex = defaultdict(list); coarse = Counter()
    for S in sets:
        v1, v2, v3 = S[:3]; D = v3 - v2; g = math.gcd(v1, D); k = classify(S)
        tot[k] += 1; byD[D][k] += 1; byg[(g, D // g)][k] += 1
        if len(ex[k]) < 6 and k in ("meeting fold", "rest"): ex[k].append(S)
        if g > 1 and k == "region":
            # one k per runner-1 phase: the smallest k giving that phase
            first = {}
            for kk in range(D): first.setdefault(kk * v1 % D, kk)
            coarse["region with one k per phase" if region_ks(S, sorted(first.values())) is not None else "needs the extra k's"] += 1
    print(f"== {label}: {len(sets)} sets: {dict(tot)}")
    print("   by D:", {D: dict(c) for D, c in sorted(byD.items())})
    print("   by (g, D/g), g > 1:", {gd: dict(c) for gd, c in sorted(byg.items()) if gd[0] > 1})
    print("   gcd > 1, region sets:", dict(coarse))
    for k, l in ex.items(): print(f"   examples {k}:", l)
if __name__ == "__main__":
  H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
  run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and rest_region(S)], f"primitive §6 rest <= {H}")
  random.seed(16); big = []
  while len(big) < 2000:
    S = tuple(sorted(random.sample(range(1, 2001), 5)))
    if len(set(S)) == 5 and math.gcd(*S) == 1 and rest_region(S): big.append(S)
  run(big, "random §6 rest <= 2000")
