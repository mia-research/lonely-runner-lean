"""Owner: check arrangements through the cascade and design the test from how the isolation occurs.  Case C (the
subject is the slowest runner, g_1 < W/22): the cascade starts at the bound 1/(8 g_1), where runner 2 reads exactly 1/8,
and relays through the other six until all are clear.  Recorded per arrangement, exact:
  moves; the most times any one runner sets a move; the runners that set; WAIT (laps of d_2 from the bound to the
  event); and the designed hypothesis H: every runner sets at most once, so WAIT <= sum over the six of one zone
  width = sum 1/(4 d_j) * d_2 < 6/4 laps of d_2.
Families as in case_c_map_v1 (even; clumped with outliers; even with a clump; g_1 ~ W/30, W/100, W/1000)."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import nd
from case_c_map_v1 import rest, arrangement
def path(V):
    ds = sorted(v - V[0] for v in V[1:]); g1 = ds[0]; d2 = ds[1]
    t = F(1, 8 * g1); setters = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: break
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); setters.append(d); t = cand[d]
    wait = d2 * (t - F(1, 8 * g1))
    bound = sum(F(d2, 4 * d) for d in ds[1:])
    return len(setters), max(Counter(setters).values(), default=0), wait, bound, g1 in setters
import case_c_map_v1 as cm
cm.rnd.seed(26)
tot = 0; H = 0; maxsets = Counter(); maxmoves = 0; worst = F(0); g1set = 0
for shape in ('even', 'clumped+outliers', 'even+clump'):
    for g1div in (30, 100, 1000):
        n = 0
        while n < 150:
            g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
            if g1 + W6 <= 22 * g1: continue
            V = arrangement([g1] + g)
            if len(set(V)) < 8: continue
            n += 1; tot += 1
            mv, ms, wait, bnd, g1s = path(V)
            maxsets[ms] += 1; maxmoves = max(maxmoves, mv); worst = max(worst, wait); g1set += g1s
            H += (ms <= 1)
print(f"Case C arrangements: {tot}")
print(f"  most times one runner sets a move: {dict(sorted(maxsets.items()))}")
print(f"  hypothesis H (every runner sets at most once): holds in {H} of {tot}")
print(f"  moves at most {maxmoves}; WAIT at most {float(worst):.4f} laps of d_2; runner 2 (g_1) ever sets: {g1set}")
