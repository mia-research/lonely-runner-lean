"""REDO item 3 (supersedes the pinned-frame separation evidence: fast_pair_window_v1, block_split_v1,
residual_members_v1-v4, robust_window_v1's framing): separation of scale on ARRANGEMENTS.

Families of 8 distinct positive speeds: uniform in [1, 10^6]; clustered (2-4 clusters at scales
10^0 ... 10^6, random sizes); slow-plus-fast (a slow group in [1,60], a fast cluster at 10^5 + [0,60]).
For EVERY runner: its readings; the largest ratio between consecutive readings; if >= 9 the readings
split into a core (below) and a block of f readings (above).  Which proved rule covers it:
  R8 (f = 1), fast pair (f = 2, min block >= 9 max core), block split (gcd(block) >= 28 max core).
Every runner's isolation event is read with the exact cascade map (cap 20,000 moves).
"""
import random
from collections import Counter
from math import gcd
from functools import reduce
from arrangement_lib import readings, F, tier
from isolated_persistence_v1 import cascade_cap
rnd = random.Random(52)
def family(name):
    if name == "uniform": return rnd.sample(range(1, 10**6), 8)
    if name == "clustered":
        c = rnd.choice((2, 3, 4)); sizes = [1] * c
        for _ in range(8 - c): sizes[rnd.randrange(c)] += 1
        V = set()
        for size, sc in zip(sizes, sorted(rnd.sample([10**i for i in range(7)], c))):
            base = rnd.randrange(sc, 2 * sc); pool = range(base, base + max(3 * size, sc // 10))
            V |= set(rnd.sample(pool, size))
        while len(V) < 8: V.add(rnd.randrange(1, 10**6))
        return sorted(V)[:8]
    slow = rnd.sample(range(1, 61), rnd.choice((1, 2, 3)))
    return slow + [10**5 + e for e in rnd.sample(range(0, 61), 8 - len(slow))]
for name in ("uniform", "clustered", "slow-plus-fast"):
    sep = Counter(); cov = Counter(); lonely = tot = 0; unc_tiers = Counter()
    for _ in range(400):
        V = sorted(set(family(name)))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k); tot += 1
            t, n = cascade_cap(ds); lonely += t is not None
            ratios = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]
            r, i = max(ratios)
            if r < 9: sep['scale-free'] += 1; continue
            core, block = ds[:i + 1], ds[i + 1:]; f = len(block); sep[f'separated, block {f}'] += 1
            if f == 1: cov['R8'] += 1
            elif f == 2 and block[0] >= 9 * core[-1]: cov['fast pair'] += 1
            elif reduce(gcd, block) >= 28 * core[-1]: cov['block split'] += 1
            else:
                cov[f'no proved rule (block {f})'] += 1; unc_tiers[tier(V, k)] += 1
    print(f"{name}: {tot} runners; cascade reaches the event {lonely}/{tot};  {dict(sorted(sep.items()))}")
    print(f"   separated runners covered: {dict(sorted(cov.items()))};  uncovered runners' cascade tier: {dict(unc_tiers)}")
