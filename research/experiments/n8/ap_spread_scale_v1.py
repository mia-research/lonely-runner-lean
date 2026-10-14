import random, sys
from math import gcd, floor
from functools import reduce
from itertools import combinations
from fractions import Fraction as F
from multiprocessing import Pool
def G(V): return reduce(gcd, [b-a for a, b in combinations(V, 2)])
def first_free(ds, s):
    N = 8*s
    for r in range(1, N, 2):
        if all(N <= 8*((e*r) % N) <= 7*N for e in ds): return r
    return None
def dist(x): x = x - floor(x); return min(x, 1-x)
def check(V):
    g = G(V); S = max(V) - min(V); runners = [[abs(v-w)//g for w in V if w != v] for v in V]
    s8 = S//(8*g) + 1                       # 8·s·g > spread
    s7 = -(-S//(7*g))                        # 7·s·g >= spread
    m8 = [V[i] for i, ds in enumerate(runners) if first_free(ds, s8) is None]
    m7 = [V[i] for i, ds in enumerate(runners) if first_free(ds, s7) is None]
    return V, g, S, s8, m8, s7, m7
if __name__ == "__main__":
    rng = random.Random(29)
    fams = {"all 8-subsets of [1,20], gcd 1": [c for c in combinations(range(1, 21), 8) if reduce(gcd, c) == 1],
            "random [1,300]": [tuple(sorted(rng.sample(range(1, 301), 8))) for _ in range(3000)],
            "random [1,3000]": [tuple(sorted(rng.sample(range(1, 3001), 8))) for _ in range(1000)],
            "gap-scaled 7+g*W, W in [1,60], g in [2,40]": [tuple(7 + g*w for w in sorted(rng.sample(range(1, 61), 8))) for g in [rng.randint(2, 40) for _ in range(1500)]]}
    shown = False
    with Pool(8) as pool:
        for name, arrs in fams.items():
            res = pool.map(check, arrs, chunksize=32)
            f8 = [x for x in res if x[4]]; f7 = [x for x in res if x[6]]
            print(f"{name}: {len(arrs)} arrangements | fail at s8 (8sg > spread): {len(f8)} | fail at s7 (7sg >= spread): {len(f7)}")
            for V, g, S, s8, m8, s7, m7 in f8[:3]: print(f"     s8 e.g. {V} g={g} spread={S} scale {s8}: no time for {m8}")
            for V, g, S, s7_, m7_, s7, m7 in f7[:3]: print(f"     s7 e.g. {V} g={g} spread={S} scale {s7}: no time for {m7}")
            if f8 and not shown:
                V, g, S, s8, m8, *_ = f8[0]; i = V.index(m8[0]); ds = [abs(V[i]-w) for w in V if w != V[i]]
                hits = [F(r, 8*s8*g) for r in range(1, 8*s8, 2) if all(dist(e*F(r, 8*s8*g)) >= F(1, 8) for e in ds)]
                print(f"     exact check, runner {V[i]} of {V} at t = r/{8*s8*g}: lonely AP times = {hits}")
                shown = True
            sys.stdout.flush()
