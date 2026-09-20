import random
from math import gcd
from functools import reduce
from itertools import combinations
from collections import Counter

def clear_int(e, r, N):
    R = (e*r) % N
    return N <= 8*R <= 7*N

def analyse(V):
    g = reduce(gcd, [b-a for a, b in combinations(V, 2)])
    out = []
    for i in range(8):
        ds = [abs(v-V[i]) for j, v in enumerate(V) if j != i]
        def works(s):
            N = 8*s*g
            return any(all(clear_int(e, r, N) for e in ds) for r in range(1, 8*s, 2))
        if works(1):
            out.append(None); continue
        dead = lambda s: any(e % (8*s*g) == 0 for e in ds)
        L0 = next(s for s in range(1, 10**6) if not dead(s))
        least = next(s for s in range(1, 10**6) if works(s))
        rec = dict(V=V, i=i, g=g, L0=L0, least=least, mult=sorted({e//(8*g) for e in ds if e % (8*g) == 0}))
        if least != L0:
            # at L0: which differences block which odd r (exact); how many differences are needed jointly
            N = 8*L0*g
            blockers = {r: [e for e in ds if not clear_int(e, r, N)] for r in range(1, 8*L0, 2)}
            rec['min_blockers'] = min(len(b) for b in blockers.values())
            rec['blockers'] = blockers
        out.append(rec)
    return out

def survey(name, arrs):
    need = 0; runners = 0; agree = 0; mism = []; gap = Counter(); arr_need = 0
    for V in arrs:
        res = analyse(V); runners += 8
        if any(res): arr_need += 1
        for rec in res:
            if rec is None: continue
            need += 1
            if rec['least'] == rec['L0']: agree += 1
            else: mism.append(rec); gap[rec['least'] - rec['L0']] += 1
    print(f"{name}: arrangements {len(arrs)}, needing scaling {arr_need}; runners {runners}, needing scaling {need}; "
          f"least working scale = first live scale for {agree}, not for {len(mism)}; excess {dict(sorted(gap.items()))}")
    return mism

rng = random.Random(14092026)
fam = {
 "exhaustive 8-subsets of [1,20], gcd 1": [c for c in combinations(range(1, 21), 8) if reduce(gcd, c) == 1],
 "random [1,100]": [tuple(sorted(rng.sample(range(1, 101), 8))) for _ in range(3000)],
 "random [1,1000]": [tuple(sorted(rng.sample(range(1, 1001), 8))) for _ in range(3000)],
 "random [1,10000]": [tuple(sorted(rng.sample(range(1, 10001), 8))) for _ in range(1500)],
}
allm = []
for k, arrs in fam.items():
    allm += survey(k, arrs)
print("\nexamples where the first live scale is blocked (first 6):")
for rec in allm[:6]:
    b = rec['blockers']; r = min(b, key=lambda r: len(b[r]))
    print(f"  V={rec['V']} runner r{rec['i']+1} g={rec['g']} slot multiples {rec['mult']} first live {rec['L0']} works at {rec['least']}; "
          f"every r blocked; fewest blockers at one r = {rec['min_blockers']} (r={r}: {b[r]})")
print("fewest-blockers distribution over all such runners:", Counter(rec['min_blockers'] for rec in allm))
