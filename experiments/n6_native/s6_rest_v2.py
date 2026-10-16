#!/usr/bin/env python3
"""Observation, compact. Non-uniform §6 sets the native branch leaves (D not | v1; D < 15 or g = gcd(v1, D) > 1), split:
  A: g = 1, D < 15;  B: g > 1 and g | v4 (then g divides v1..v4 and the meeting-window data at k/D are those of the reduced
  (v1..v4)/g at k/D', D' = D/g, with gcd(v1/g, D') = 1);  C: g > 1, g not | v4.
For each: closure (region / sum lemma / meeting fold / rest, as s6_rest_v1), and D' < 15 vs >= 15.
For B with D' >= 15: the reduced direction lam' = (delta/g) (v1/g)^-1 mod D' -- whether the proved branch's cases
(|lam'| >= 2 generic, lam' = +-1 certificate) would apply after reduction.
For C: runner 4's phases at the k with a fixed runner-1 phase form a coset of (delta/g) mod 1 -- whether the region
closes using only that freedom at the runner-1 phase j/D' nearest 1/3 (one runner-1 phase, all its k)."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from s6_rest_v1 import rest_region, uniform, region_ks, sum_ok, meet_fold
H = int(sys.argv[1]) if len(sys.argv) > 1 else 50
cnt = defaultdict(Counter); ex = defaultdict(list)
for S in combinations(range(1, H + 1), 5):
    if math.gcd(*S) != 1 or not rest_region(S) or uniform(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2; g = math.gcd(v1, D); Dp = D // g
    cls = "A g=1,D<15" if g == 1 else ("B g|v4" if v4 % g == 0 else "C g∤v4")
    big = "D'>=15" if Dp >= 15 else "D'<15"
    if region_ks(S, range(D)) is not None: how = "region"
    elif sum_ok(S): how = "sum"
    elif meet_fold(S): how = "meeting fold"
    else: how = "REST"
    cnt[(cls, big)][how] += 1
    if cls.startswith("B") and Dp >= 15:
        lp = ((v4 - v3) // g) * pow(v1 // g, -1, Dp) % Dp; lp = lp - Dp if lp > Dp // 2 else lp
        cnt[(cls, big, "lam'")]["|lam'|>=2" if abs(lp) >= 2 else f"lam'={lp}"] += 1
    if cls.startswith("C"):
        a = v1 // g; inv = pow(a, -1, Dp)
        j = min(range(Dp), key=lambda j: abs(F(j, Dp) - F(1, 3)))
        ks = [(j * inv) % Dp + Dp * i for i in range(g)]
        cnt[(cls, big, "one phase")]["closes" if region_ks(S, ks) is not None else "not"] += 1
    if how in ("meeting fold", "REST") and len(ex[(cls, how)]) < 8: ex[(cls, how)].append(S)
print(f"non-uniform §6 rest, primitive, <= {H}")
for k in sorted(cnt): print("  ", k, dict(cnt[k]))
for k, l in sorted(ex.items()): print("   examples", k, l)
