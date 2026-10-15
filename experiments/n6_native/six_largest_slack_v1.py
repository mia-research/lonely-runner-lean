#!/usr/bin/env python3
"""Slack at the largest flank for primitive SixResidual sets: G = #{k < e : certificate (e,k)},
e = max S. Reports min G and min G/e per bucket of e, the sets attaining them, and the number of
openings blocked by each non-flank difference (exact). Integers only."""
import sys, math, importlib.util
from itertools import combinations
from collections import defaultdict
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def blocked(d, e):
    return {k for k in range(e) if not (e <= (d * (6 * k + 1)) % (6 * e) <= 5 * e)}
best = defaultdict(lambda: (10**9, None)); zeros = 0; sumblk_gt = 0; tot = 0
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    tot += 1
    e = S[-1]
    B = [blocked(d, e) for d in S[:-1]]
    G = e - len(set().union(*B))
    if G == 0: zeros += 1; continue
    if sum(len(b) for b in B) >= e: sumblk_gt += 1
    bucket = (e - 1) // 10
    ratio = G / e
    if ratio < best[bucket][0]: best[bucket] = (ratio, (S, G, [len(b) for b in B]))
print(f"HI={HI}: residual={tot}, largest-flank failures={zeros}, successes where blocked counts sum >= e: {sumblk_gt}")
for bk in sorted(best):
    ratio, (S, G, lens) = best[bk]
    print(f"  e in [{10*bk+1},{10*bk+10}]: min G/e = {ratio:.3f} at {S}, G={G}, blocked per d={lens}")
