#!/usr/bin/env python3
"""Observation: §6 sets with gcd(v1, D) = 1 and direction lam in {0, 1, -1} (v4 = lam v1 mod D), primitive <= 60, not
covered by s6_meeting_uniform. For each: the after region [1/6,5/9] x A and before region [4/9,5/6] x A' (E94) restricted
to the orbit (p1, p4) = (j/D, lam j/D); whether the orbit meets them; if not, whether the exact meeting-window fold
(runner 1 only partly clear, s6_near_v1.meet_fold) closes it, and with which phases."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s6_near_v1.py").read().split("H = int(")[0])
def frac(x): return x - (x.numerator // x.denominator)
def in_arc(p, a, b): return b - a >= 1 or frac(p - a) <= b - a
out = Counter(); ex = []
for S in combinations(range(1, 61), 5):
    if math.gcd(*S) != 1 or not s6(S) or uniform(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if math.gcd(v1, D) != 1: continue
    lam = v4 * pow(v1, -1, D) % D
    lam = lam - D if lam > D // 2 else lam
    if lam not in (0, 1, -1): continue
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); l = s1 - s0; L4 = v4 * l; mu = F(v4, 3 * v5)
    A = (F(1, 6) - L4 + mu - v4 * s0, F(5, 6) - mu - v4 * s0); Ap = (F(1, 6) - L4 + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
    hit = any((F(1, 6) <= F(j, D) <= F(5, 9) and in_arc(F(lam * j % D, D), *A)) or
              (F(4, 9) <= F(j, D) <= F(5, 6) and in_arc(F(lam * j % D, D), *Ap)) for j in range(D))
    key = (lam, "region met" if hit else ("exact fold" if meet_fold(S) else "neither"))
    out[key] += 1
    if not hit and len(ex) < 10: ex.append((S, D, lam))
print("directions 0, +-1 (gcd 1, not uniform), <= 60:", dict(sorted(out.items())))
print("examples not meeting the region:", ex)
# the lam = 1 sets that need the exact fold: their c (v3 = (c+1) D), delta = v4 - v3, v1, D
feat = Counter()
for S in combinations(range(1, 61), 5):
    if math.gcd(*S) != 1 or not s6(S) or uniform(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if math.gcd(v1, D) != 1: continue
    lam = v4 * pow(v1, -1, D) % D
    if lam != 1: continue
    s0, s1 = F(1, 6 * v2), F(5, 6 * v3); l = s1 - s0; L4 = v4 * l; mu = F(v4, 3 * v5)
    A = (F(1, 6) - L4 + mu - v4 * s0, F(5, 6) - mu - v4 * s0); Ap = (F(1, 6) - L4 + mu + v4 * s1, F(5, 6) - mu + v4 * s1)
    hit = any((F(1, 6) <= F(j, D) <= F(5, 9) and in_arc(F(j, D), *A)) or (F(4, 9) <= F(j, D) <= F(5, 6) and in_arc(F(j, D), *Ap)) for j in range(D))
    if not hit: feat[("c=%d" % (v3 // D - 1), "delta=v1" if v4 - v3 == v1 else "delta!=v1", "v1=%d" % v1)] += 1
print("lam = 1 needing the exact fold, by (c, delta vs v1, v1):", sorted(feat.items(), key=lambda z: -z[1])[:12])
