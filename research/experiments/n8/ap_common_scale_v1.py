import random, sys
from math import gcd
from functools import reduce
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0, '.')
from ap_scale_mechanism_v1 import blocked_formula
def G(V): return reduce(gcd, [b-a for a, b in combinations(V, 2)])
def free_r(ds, s):
    taken = set()
    for e in ds: taken |= blocked_formula(e, s)[0]
    return sorted(set(range(1, 8*s, 2)) - taken)
def analyse(V, smax=400):
    g = G(V); runners = [[abs(v-w)//g for w in V if w != v] for v in V]
    mults = sorted({(b-a)//(8*g) for a, b in combinations(V, 2) if (b-a) % (8*g) == 0})
    live = lambda s: not any(k % s == 0 for k in mults)
    first_live = next(s for s in range(1, smax) if live(s))
    works = lambda s: all(free_r(ds, s) for ds in runners)
    least = next((s for s in range(1, smax) if works(s)), None)
    return g, mults, first_live, least, runners, live, works

V = (1,31,75,97,128,160,176,225)
g, mults, fl, least, runners, live, works = analyse(V)
print("slot multiples of sharing pairs:", mults, " dead scales:", [s for s in range(1, 30) if not live(s)])
print("first common live scale:", fl, " least scale working for all eight:", least)
for s in [fl] + [s for s in range(fl+1, least+1) if live(s)] + [150]:
    print(f"\n scale {s} (AP times r/{8*s*g}): {'live' if live(s) else 'dead'}")
    for v, ds in zip(V, runners):
        fr = free_r(ds, s)
        print(f"   runner {v:>3}: " + (f"first time {F(fr[0], 8*s*g)}  ({len(fr)} of {4*s} AP times free)" if fr else "NO free AP time"))

print("\nacross arrangements: first common live scale vs least scale working for all eight")
rng = random.Random(1409)
fams = {"all 8-subsets of [1,16], gcd 1": [c for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1],
        "random [1,200]": [tuple(sorted(rng.sample(range(1, 201), 8))) for _ in range(2000)],
        "random [1,5000]": [tuple(sorted(rng.sample(range(1, 5001), 8))) for _ in range(1000)]}
for name, arrs in fams.items():
    c = Counter(); exc = []
    for W in arrs:
        g, mults, fl, least, *_ = analyse(W)
        c[least - fl] += 1
        if least != fl and len(exc) < 3: exc.append((W, mults, fl, least))
    print(f"  {name}: {len(arrs)} arrangements; least working minus first live: {dict(sorted(c.items()))}")
    for e in exc: print("     e.g.", e)
