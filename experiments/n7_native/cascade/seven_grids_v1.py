#!/usr/bin/env python3
"""7-adic residue grids at order seven (EXACT), primitive six-sets <= HI.  Grid level a: instants k / 7^a with 7 not
dividing k; lonely iff every d k mod 7^a lies in [7^(a-1), 6 * 7^(a-1)].  Level a = 1 is t = k/7.  For each set: the
lowest level a <= 3 that closes it, against the 7-adic valuations of its speeds; then, for sets no grid level <= 3
closes, the closers A (first instant), C (7-divisible flank cell), or neither."""
import sys, math
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, ".")
from seven_core_v1 import closer
def v7(x):
    k = 0
    while x % 7 == 0: x //= 7; k += 1
    return k
def grid(S, a):
    M = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
    return any(all(lo <= (d * k) % M <= hi for d in S) for k in range(1, M) if k % 7)
def work(args):
    v1, HI = args; c = Counter(); rest_ = []
    for rest in combinations(range(v1 + 1, HI + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        vals = tuple(sorted(v7(d) for d in S))
        lvl = next((a for a in (1, 2, 3) if grid(S, a)), None)
        if lvl is not None: c[("grid", lvl, vals)] += 1; continue
        k = closer(S); c[("nogrid", k, vals)] += 1
        if k == "D": rest_.append(S)
    return c, rest_
if __name__ == "__main__":
    HI = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, HI) for v1 in range(1, HI - 4)], chunksize=1)
    c = Counter(); rest_ = []
    for r in res: c += r[0]; rest_ += r[1]
    tot = sum(c.values())
    g = Counter(); ng = Counter()
    for k, v in c.items():
        if k[0] == "grid": g[k[1]] += v
        else: ng[k[1]] += v
    print(f"HI={HI}: {tot} sets; closed by grid level 1/2/3: {dict(sorted(g.items()))}; not closed by any grid <= 3: {dict(ng)}")
    print("  grid level by valuation multiset (top):", sorted(((k[1], k[2]), v) for k, v in c.items() if k[0] == 'grid')[:12])
    print("  no grid, by valuation multiset:", sorted(((k[1], k[2]), v) for k, v in c.items() if k[0] == 'nogrid')[:12])
    print("  neither grid nor A nor C (first 20):", rest_[:20], len(rest_))
