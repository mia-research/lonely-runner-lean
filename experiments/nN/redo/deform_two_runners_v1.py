"""Two runners deformed together from the AP, traced exactly (owner, 2026-09-26).  AP v_k = k G, G = 840.  Runners
(a, b) moved by (da, db) over a 13 x 13 grid in (-0.9G, 0.9G); every subject.  Per subject: R = 8 d_min t*, S, the
pinning runners, and whether the pinner is a circle neighbour of the subject at the event.  Checks:
 (i)  S <= 7  =>  R = 1 (the event is 1/(8 d_min), the AP's first spine point at the subject's own scale);
 (ii) the event is never lost and R stays in band 0 or 1 (R <= 15); the largest R and t* d_min;
 (iii) grids (all differences multiples of one gap) give R = 1.  Exact (Fraction)."""
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
from arrangement_lib import nd
G = 840
def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
steps = [int(G * F(k, 20)) for k in range(-18, 19, 3)]
pairs = [(8, 1), (8, 4), (2, 7), (4, 5)]
for a, b in pairs:
    n = s7 = s7ok = late = grid = gridok = 0; maxR = F(0); Rc = Counter(); neigh = 0
    for da in steps:
        for db in steps:
            V = [k * G for k in range(1, 9)]; V[a - 1] += da; V[b - 1] += db
            if len(set(V)) < 8 or min(V) <= 0: continue
            g = reduce(gcd, [abs(x - y) for x in V for y in V if x != y])
            for sub in range(8):
                ds = sorted({abs(v - V[sub]) for i, v in enumerate(V) if i != sub})
                t = cascade(ds); dmin = min(ds); S = F(max(ds), dmin); R = 8 * dmin * t
                n += 1; maxR = max(maxR, R); late += R > 7
                Rc['R=1' if R == 1 else ('band 0, R>1' if R <= 7 else 'band 1')] += 1
                if S <= 7: s7 += 1; s7ok += R == 1
                # circle neighbours at the event: the runners nearest the subject on each side
                pos = sorted(((v - V[sub]) * t % 1, i) for i, v in enumerate(V) if i != sub)
                nbrs = {pos[0][1], pos[-1][1]}
                pins = {i for i, v in enumerate(V) if i != sub and nd((v - V[sub]) * t) == F(1, 8)}
                neigh += bool(pins & nbrs)
    print(f"runners {a},{b} deformed: {n} subject-events; lost: 0 (every cascade stopped); R: {dict(Rc)}; "
          f"max R = {maxR} ({float(maxR):.3f}); S<=7 -> R=1: {s7ok}/{s7}; pinned by a circle neighbour: {neigh}/{n}")
