import random, sys
from math import gcd
from functools import reduce
from itertools import combinations
from fractions import Fraction as F
from multiprocessing import Pool
def G(V): return reduce(gcd, [b-a for a, b in combinations(V, 2)])
def check(V):
    V = sorted(V); S = V[-1] - V[0]; g = G(V)
    D = F(S, 7)                                   # the spread-determined AP gap
    dev = [V[k] - (V[0] + k*D) for k in range(8)] # deviation from the AP anchored at both ends
    fits = all(abs(e) < D for e in dev)
    # AP times t = r/(8D) = 7r/(8S), r odd; lonely test exact: N <= 8*(7 e r mod N) <= 7N with N = 8S
    N = 8*S; rmax = (16*S)//(7*g) + 2
    miss = []
    for i, v in enumerate(V):
        ds = [abs(v - w) for w in V if w != v]
        if not any(all(N <= 8*((7*e*r) % N) <= 7*N for e in ds) for r in range(1, rmax, 2)):
            miss.append(v)
    return tuple(V), fits, miss, [str(e) for e in dev]
if __name__ == "__main__":
    for V in [(1,31,75,97,128,160,176,225), (1,2,3,4,5,6,7,9), (1,3,5,9,12,14,16,18), (1,2,3,4,5,6,7,8), (1,2,3,4,5,6,7,100)]:
        V_, fits, miss, dev = check(V)
        print(f"{V}: gap S/7 = {F(max(V)-min(V),7)}, deviations {dev}, fits {fits}, runners without a time on r/(8D): {miss or 'none'}")
    rng = random.Random(31)
    fams = {"all 8-subsets of [1,20], gcd 1": [c for c in combinations(range(1, 21), 8) if reduce(gcd, c) == 1],
            "random [1,300]": [tuple(sorted(rng.sample(range(1, 301), 8))) for _ in range(3000)],
            "random [1,3000]": [tuple(sorted(rng.sample(range(1, 3001), 8))) for _ in range(600)]}
    with Pool(8) as pool:
        for name, arrs in fams.items():
            res = pool.map(check, arrs, chunksize=64)
            nf = sum(1 for r in res if r[1]); f_ok = sum(1 for r in res if r[1] and not r[2]); nf_ok = sum(1 for r in res if not r[1] and not r[2])
            print(f"\n{name}: {len(res)} arrangements")
            print(f"   fit the spread AP (every |deviation| < S/7): {nf};  of those, every runner has a time on r/(8D): {f_ok}")
            print(f"   do not fit: {len(res)-nf};  of those, every runner has a time on r/(8D): {nf_ok}")
            ex = [r for r in res if r[1] and r[2]][:3]
            for r in ex: print("     fits but some runner has no time:", r[0], "deviations", r[3], "no time:", r[2])
            sys.stdout.flush()
