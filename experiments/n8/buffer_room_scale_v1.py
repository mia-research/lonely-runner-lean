import random, math
from math import gcd, floor
from functools import reduce
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def frac(x): return x - floor(x)
def move(s_list, u0):
    """requirement / room at base u0, moving right; returns (eps, min_room) exactly"""
    req = F(0); room = None
    for s in s_list:
        ph = frac(s*u0)
        if ph < E:      q, R = (E - ph)/s, (1 - E - ph)/s
        elif ph > 1-E:  q, R = (1 + E - ph)/s, (2 - E - ph)/s
        else:           q, R = F(0), (1 - E - ph)/s
        req = max(req, q); room = R if room is None else min(room, R)
    return req, room
def lonely(ds, t): return all(min(frac(d*t), 1-frac(d*t)) >= E for d in ds)
def study(V, i, Lmax=12):
    v = V[i]; ds = [abs(v-w) for w in V if w != v]; m = min(ds); s_list = [F(d, m) for d in ds]
    first = None; ratio1 = None
    for L in range(1, Lmax+1):
        best = None
        for p in range(L, 7*L+1):
            if p % 2 == 0: continue
            u0 = F(p, 8*L); eps, room = move(s_list, u0)
            r = F(0) if eps == 0 else (eps/room if room > 0 else math.inf)
            if best is None or r < best: best = r
            if eps <= room:
                assert lonely(ds, (u0+eps)/m)
                if first is None: first = (L, p, u0+eps)
        if L == 1: ratio1 = best
        if first: break
    return ratio1, first
V = (1,2,3,4,5,6,7,9)
print("(1..7,9) runner 1:", study(V, 0))
C = (1,31,75,97,128,160,176,225)
for i in range(8): print("counterexample runner", C[i], study(C, i))
rng = random.Random(5)
rows = []
for _ in range(1500):
    W = tuple(sorted(rng.sample(range(1, 400), 8)))
    for i in range(8):
        r1, first = study(W, i)
        rows.append((r1, first[0] if first else None))
c = Counter((min(math.ceil(r), 20) if r != math.inf else 'inf', L) for r, L in rows)
print("\n(ceil of best requirement/room ratio at L=1, least lattice L with a fitting move) -> count")
for k in sorted(c, key=lambda x: (str(x[0]), str(x[1]))): print("  ", k, c[k])
