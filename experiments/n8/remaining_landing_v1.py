# The remaining subject pairs of E633 (after ratio/unblocked, first-lap, no-multiple, one-free, block split): the cascade's first lonely instant T for each.
# Records: lap M = floor(T*d_min), moves, rank (in the sorted disparities) of the flank that sets T, and T*d_min exactly.  Exact Fractions.
import sys, math, collections
from fractions import Fraction as F
exec(open('admissible_free_block_count_v1.py').read().split("cnt = collections.Counter()")[0])
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def casc(S):
    t = F(1, 8 * min(S)); mv = 0; last = None
    while True:
        way = [d for d in S if dist(d * t) < E]
        if not way: return t, mv, last
        best = None
        for d in way:
            c = (F(round(d * t)) + E) / d
            if best is None or c > best[0]: best = (c, d)
        t, last = best[0], best[1]; mv += 1
cnt = collections.Counter(); laps = collections.Counter(); ranks = collections.Counter(); mvs = collections.Counter(); worst = (F(0), None); tot = 0
for dd, res in configs():
    sp = tuple(x + 1 for x in dd)
    isgrid = len({x % 8 for x in sp}) == 8
    for k in range(8):
        S = [abs(sp[j] - sp[k]) for j in range(8) if j != k]
        r, u, f, nm, of, bs = flags(S)
        if isgrid or r or u or f or nm or of or bs: continue
        S = sorted(set(S)); T, mv, last = casc(S); tot += 1
        M = math.floor(T * S[0]); laps[M] += 1; mvs[mv] += 1
        ranks[S.index(last) if last else -1] += 1
        if T * S[0] > worst[0]: worst = (T * S[0], S)
print('remaining', tot)
print('lap M = floor(T*d_min):', dict(sorted(laps.items())))
print('moves:', dict(sorted(mvs.items())))
print('rank of the setting flank (0 = d_min):', dict(sorted(ranks.items())))
print('max T*d_min', worst[0], float(worst[0]), 'at', worst[1])
