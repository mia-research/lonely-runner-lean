"""The long cascades in sync_arrangements_v1 (191 and 688 moves): which runner, what its readings are,
where the isolation event lands and what scale, and which runners set the moves.  Same generator and
seed as sync_arrangements_v1; exact."""
import random
from collections import Counter
from arrangement_lib import *
def cascade_trace(ds):
    t = F(1, 8 * min(ds)); setters = Counter(); n = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, n, setters
        opens = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        mover = max(way, key=lambda d: opens[d]); setters[mover] += 1
        t = opens[mover]; n += 1
rnd = random.Random(49); N = 10**5
for fam in ("random slow", "slow multiples of 7", "slow multiples of 42"):
    for _ in range(300):
        s = rnd.choice((1, 2, 3))
        if fam == "random slow": slow = rnd.sample(range(1, 61), s)
        elif fam == "slow multiples of 7": slow = [7 * x for x in rnd.sample(range(1, 9), s)]
        else: slow = [42 * x for x in rnd.sample(range(1, 4), s)]
        fast = [N + e for e in rnd.sample(range(0, 61), 8 - s)]
        V = sorted(set(slow + fast))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k)
            t, n, setters = cascade_trace(ds)
            if n > 20:
                print(f"{fam}: arrangement {V}, runner at speed {V[k]}: readings {ds}")
                print(f"   {n} moves; isolation t = {float(t):.6f} (scale D = {float(1 / (8 * t)):.4f}, = {float(t * min(ds)):.3f} laps of d_min); moves set by {dict(setters.most_common(4))}")
