#!/usr/bin/env python3
"""Exceptions of the order-seven map (o7_map_v1): sets not closed with four tracked runners (T5, T6), primitive <= H.
Groups them by the normalised prefix (v1..v5)/gcd(v1..v5) and by (v1..v4)/gcd, and reports, per prefix, the range of v6
(as a multiple of the prefix scale) -- to see the families. Also the order-six status of the prefix (v1..v5): its best
gap at 1/6 resolution (exact, from breakpoints), to test whether the exceptions sit over order-six tight or near-tight
prefixes."""
import math, sys
from itertools import combinations
from collections import Counter, defaultdict
from fractions import Fraction as F
exec(open("o7_map_v1.py").read().split("def run(")[0])
def best_gap(vs):
    best = 0.0
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            for s in (vs[i] + vs[j], vs[j] - vs[i]):
                for k in range(s + 1):
                    t = k / s
                    g = min(abs(v * t - round(v * t)) for v in vs)
                    best = max(best, g)
    return best
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
fam5 = defaultdict(list); kinds = Counter()
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    k, p = classify(S)
    if k in ("T5", "T6"):
        g = math.gcd(*S[:5]); pre = tuple(x // g for x in S[:5])
        fam5[(k, pre)].append(F(S[5], g))
rows = sorted(fam5.items(), key=lambda kv: -len(kv[1]))
print(f"exception families by (v1..v5)/g, primitive <= {H}: {len(rows)} prefixes")
for (k, pre), l in rows[:40]:
    print(f"  {k} prefix {pre} (order-6 best gap {best_gap(pre):.4f}): {len(l)} sets, v6/g in [{float(min(l)):.2f}, {float(max(l)):.2f}]")
small = Counter()
for (k, pre), l in rows: small["prefix max ratio v5/v1 <= 6" if pre[4] <= 6 * pre[0] else "prefix ratio > 6"] += len(l)
print("by prefix spread:", dict(small))
