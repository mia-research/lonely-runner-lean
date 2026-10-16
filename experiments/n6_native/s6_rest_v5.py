#!/usr/bin/env python3
"""Observation. The failing classes of s6_rest_v4 (lam = 1 for each D < 15; (5,3), (7,5)): failure count by c, the Q and M
ranges of the failures, and for the actual primitive sets <= 60 in these classes that the region does not close,
which other window closes them (sum lemma v4 = v3 + v1; exact meeting fold) and whether v4 = v3 + v1."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from s6_rest_v4 import closed
from s6_rest_v1 import uniform, region_ks, sum_ok, meet_fold
fail = [(D, 1) for D in range(2, 15)] + [(5, 3), (7, 5)]
for D, lam in fail:
    byc = Counter(); Qr = defaultdict(lambda: [9, 0]); Mr = defaultdict(lambda: [9, 0])
    for c in list(range(1, 9)) + [20, 100, 1000]:
        U = F(c + 1, c); Qmax = 4 / (5 - U)
        for qi in range(80):
            Q = 1 + (Qmax - 1) * F(qi, 80)
            for mi in range(1, 41):
                M = F(mi, 120)
                if not closed(D, lam, U, Q, M):
                    byc[c] += 1; Qr[c] = [min(Qr[c][0], float(Q)), max(Qr[c][1], float(Q))]; Mr[c] = [min(Mr[c][0], float(M)), max(Mr[c][1], float(M))]
    print(f"({D},{lam}): failures by c {dict(byc)}; Q range {dict((c, [round(x, 3) for x in Qr[c]]) for c in byc)}; M range {dict((c, [round(x, 3) for x in Mr[c]]) for c in byc)}")
H = 60; res = Counter(); ex = defaultdict(list)
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if D >= 15 or v3 <= 3 * v1 or v3 % D or math.gcd(v1, D) != 1 or v1 % D == 0 or math.gcd(*S) != 1 or uniform(S): continue
    lam = (v4 - v3) * pow(v1, -1, D) % D
    if (D, lam) not in fail or region_ks(S, range(D)) is not None: continue
    key = (f"lam={lam}" if lam != 1 else "lam=1", "v4=v3+v1" if v4 == v3 + v1 else "other", "c=%d" % (v2 // D))
    how = "sum" if sum_ok(S) else ("meeting fold" if meet_fold(S) else "REST")
    res[key + (how,)] += 1
    if len(ex[key + (how,)]) < 5: ex[key + (how,)].append(S)
print(f"actual coprime D < 15 sets <= {H} in failing classes, region not closing:")
for k in sorted(res): print("  ", k, res[k], ex[k])
