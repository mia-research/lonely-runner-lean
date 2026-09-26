"""The owner's ratio on the wide sample: for random reading sets (d_min 1..20, readings to 2000; the slowest runner of
eight moving runners) whose bound is not lonely, the collider b (the first move's setter), its lap k = round(b/(8 d_min))
at the bound, the final R, and the displacement in the collider's own laps, b*(t* - t0).  Ceilings by k.  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import defaultdict
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def job(seed):
    rnd = random.Random(seed); env = defaultdict(lambda: [F(0), F(0), 0])
    for _ in range(3000):
        m = rnd.randint(1, 20); T = sorted({m} | set(rnd.sample(range(m + 1, 2001), 6)))
        if len(T) != 7: continue
        t0 = F(1, 8 * m); t = t0; b = None
        while True:
            way = [d for d in T if nd(d * t) < E8]
            if not way: break
            ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
            s = max(ex, key=lambda x: ex[x])
            if b is None: b = s
            t = ex[s]
        if b is None: continue
        k = floor(F(b, 8 * m) + F(1, 2))
        R = 8 * m * t; laps = b * (t - t0)
        kk = k if k <= 10 else (20 if k <= 20 else (50 if k <= 50 else 250))
        e = env[kk]; e[0] = max(e[0], R); e[1] = max(e[1], laps); e[2] += 1
    return {k: v for k, v in env.items()}

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(job, range(16))
    env = defaultdict(lambda: [F(0), F(0), 0])
    for p in parts:
        for k, v in p.items():
            e = env[k]; e[0] = max(e[0], v[0]); e[1] = max(e[1], v[1]); e[2] += v[2]
    print("collider lap k (bucketed: <=10 exact, then <=20, <=50, <=250): relays, largest final R, largest displacement in the collider's laps")
    for k in sorted(env): print(f"  k {k:3d}: {env[k][2]:6d} relays; R up to {float(env[k][0]):.3f}; collider laps up to {float(env[k][1]):.3f}")
