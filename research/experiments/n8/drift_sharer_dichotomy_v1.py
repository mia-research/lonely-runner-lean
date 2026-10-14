"""Test: a runner has NO lonely own-AP instant (u = n/8, n odd, over one period of its reading, or a stated cap for
irrationals-free rationals) iff some other runner is an exact slot-sharer: deviation e = 0 and AP index a = 0 (mod 8).
AP frame of the subject: m = d_min, reading s = d/m = a + e, a = round(s).  Exact Fractions.
Also, for runners with no sharer: the first lonely n, and whether the small-drift rule names it
(c = r*a mod 8 != 0; c = 1 -> n*e >= 0; c = 7 -> n*e <= 0; |n*e| < 1 for all)."""
import sys, os, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def fr(x): return x - floor(x)
def rnd(x): return floor(x + F(1, 2))
def dist8(x):                       # distance from x to 8Z
    y = x - 8 * floor(x / 8); return min(y, 8 - y)
def analyse(V):
    out = []
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        S = [d / m for d in ds]; A = [rnd(s) for s in S]; E = [s - a for s, a in zip(S, A)]
        den = reduce(lambda x, y: x * y // gcd(x, y), [s.denominator for s in S])
        period = 8 * den                          # n -> n + period leaves every n*s mod 8 unchanged
        sharer = any(e == 0 and a % 8 == 0 for a, e in zip(A, E))
        first = None
        for n in range(1, period + 1, 2):
            if all(dist8(n * s) >= 1 for s in S): first = n; break
        rule = None
        if first is not None:
            r = first % 8
            ok = True
            for a, e in zip(A, E):
                c = (r * a) % 8; dr = first * e
                if abs(dr) >= 1 or c == 0 or (c == 1 and dr < 0) or (c == 7 and dr > 0): ok = False
            rule = ok
        out.append(dict(sharer=sharer, has=first is not None, first=first, rule=rule,
                        profile=None if first is not None else tuple(sorted((a % 8, str(e)) for a, e in zip(A, E)))))
    return out
def run(name, arrs, pool):
    R = [x for r in pool.map(analyse, arrs, chunksize=16) for x in r]
    c = Counter((x["sharer"], x["has"]) for x in R)
    print(f"\n{name}: {len(R)} runners")
    print(f"   exact slot-sharer present & no lonely AP instant : {c[(True, False)]}")
    print(f"   exact slot-sharer present & lonely AP instant    : {c[(True, True)]}")
    print(f"   no sharer & no lonely AP instant                 : {c[(False, False)]}")
    print(f"   no sharer & lonely AP instant                    : {c[(False, True)]}")
    rows = [x for x in R if x["has"]]
    print(f"   runners with a lonely AP instant whose first one is named by the small-drift rule: {sum(1 for x in rows if x['rule'])} of {len(rows)}")
    bad = [x["profile"] for x in R if not x["sharer"] and not x["has"]][:4]
    if bad: print("   no-sharer, no-instant profiles (a mod 8, e):", bad)
if __name__ == "__main__":
    rng = random.Random(29); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = [("one runner moved, step 0.05", [V for V in (ok([AP[j] + (F(x, 20) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(20 * k + 1, 20 * (k + 2))) if V])]
    L = []
    while len(L) < 400:
        V = ok([AP[j] + F(rng.randint(-45, 45), 50) for j in range(8)])
        if V: L.append(V)
    fams.append(("every runner moved, deviations in fiftieths", L))
    fams.append(("all 8-subsets of [1,16], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]))
    fams.append(("random integers [1,300]", [[F(v) for v in sorted(rng.sample(range(1, 301), 8))] for _ in range(600)]))
    with Pool(8) as pool:
        for n, a in fams: run(n, a, pool); sys.stdout.flush()
