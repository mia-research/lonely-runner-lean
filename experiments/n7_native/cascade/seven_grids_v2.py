#!/usr/bin/env python3
"""7-adic residue grids (EXACT), primitive six-sets <= HI: the lowest grid level a <= 5 with a lonely instant k / 7^a
(7 not dividing k; lonely iff every d k mod 7^a in [7^(a-1), 6 * 7^(a-1)]), tabulated against nu_max (largest 7-adic
valuation among the speeds).  Lists sets needing a > nu_max + 2 and sets no level <= 5 closes."""
import sys, math
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def v7(x):
    k = 0
    while x % 7 == 0: x //= 7; k += 1
    return k
def grid(S, a):
    M = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
    R = [d % M for d in S]
    for k in range(1, M):
        if k % 7 and all(lo <= (r * k) % M <= hi for r in R): return True
    return False
def work(args):
    v1, HI = args; c = Counter(); odd = []
    for rest in combinations(range(v1 + 1, HI + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        nm = max(v7(d) for d in S)
        lvl = next((a for a in range(nm + 1, 6) if grid(S, a)), None)
        c[(nm, lvl)] += 1
        if lvl is None or lvl > nm + 2: odd.append((S, lvl))
    return c, odd
if __name__ == "__main__":
    HI = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, HI) for v1 in range(1, HI - 4)], chunksize=1)
    c = Counter(); odd = []
    for r in res: c += r[0]; odd += r[1]
    print(f"HI={HI}: {sum(c.values())} primitive six-sets; (nu_max, lowest grid level):", sorted(c.items(), key=str))
    print(f"  needing a > nu_max + 2 or no level <= 5: {len(odd)}", odd[:20])
