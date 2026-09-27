"""Class C across lap sizes: the event's flank distance d relative to the subject's nearest distance d_min, its lap N,
and whether the event is the FIRST opening (smallest lap) of its flank that comes after the grid instant 1/8, i.e.
N = floor(d/8) or floor(d/8)+1.  Also R = 8t*, and R against the separation m."""
import random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from doubled_slot_grid_v1 import event, nd
for Q in (1, 3, 10, 50):
    rnd = random.Random(44); rows = []
    for trial in range(6000 if Q < 50 else 20000):
        s, r = rnd.sample(range(8), 2); res = [x for x in range(8) if x != r] + [s]
        while True:
            laps = [rnd.randint(0, Q) for _ in range(8)]; u = [res[i] + 8 * laps[i] for i in range(8)]
            if len(set(u)) == 8: break
        v = [100 + x for x in u]; pair = [i for i in range(8) if res[i] == s]
        for k in pair:
            t = event(v, k); p = [i for i in pair if i != k][0]; m = abs(v[p] - v[k]) // 8
            if t <= F(1, 8): continue
            tm = F(1, 8) + F(1, 64 * m)
            if not [i for i in range(8) if i != k and nd((v[i] - v[k]) * tm) < F(1, 8)]: continue
            fl = [i for i in range(8) if i != k and (abs(v[i] - v[k]) * t) % 1 == F(1, 8)]
            d = min(abs(v[i] - v[k]) for i in fl); N = floor(d * t)
            dmin = min(abs(v[i] - v[k]) for i in range(8) if i != k)
            first_after = floor(F(d, 8) - F(1, 8)) + 1   # smallest N with (N + 1/8)/d > 1/8
            rows.append((8 * t, d, N, dmin, m, N - first_after))
    R = sorted(x[0] for x in rows)
    print(f"\nQ = {Q}: {len(rows)} class-C cases; R = 8t*: median {float(R[len(R)//2]):.3f}, max {float(R[-1]):.3f}")
    print("   laps past the flank's first opening after the grid instant:", dict(sorted(Counter(x[5] for x in rows).items())))
    print("   flank distance d / subject's nearest d_min:", dict(Counter(min(int(x[1] / x[3]), 20) for x in rows).most_common(8)))
    print("   R by separation m (max):", {m: float(max(x[0] for x in rows if x[4] == m)) for m in sorted({x[4] for x in rows})[:8]})
