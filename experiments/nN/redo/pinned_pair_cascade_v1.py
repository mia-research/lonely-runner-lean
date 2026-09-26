"""Follow the cascade where the grid nudge cannot work: residual sets (every q = 2..8 divides a reading), readings <= 32,
exactly one multiple of 8, and readings at both grid edges (some d = 1 mod 8 and some d = 7 mod 8: the pinned pair).
At the cascade isolation t* = (8k+1)/(8e): which reading e becomes the scale (the multiple of 8, an edge reading
(= 1 or 7 mod 8), or an interior one), the lap k, and each reading's position in eighths.  Exact."""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from residual_cascade_v1 import residual, cascade_flank

def chunk(first):
    c = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if not residual(T): continue
        m8 = [d for d in T if d % 8 == 0]
        if len(m8) != 1 or not any(d % 8 == 1 for d in T) or not any(d % 8 == 7 for d in T): continue
        t, e, k, mv = cascade_flank(list(T))
        role = 'bound (smallest reading, k = 0)' if (k == 0 and e == T[0]) else (
            'multiple of 8' if e % 8 == 0 else ('edge 1 mod 8' if e % 8 == 1 else ('edge 7 mod 8' if e % 8 == 7 else f'interior {e % 8} mod 8')))
        c[(role, min(k, 4))] += 1
        if len(ex) < 3 and role != 'bound (smallest reading, k = 0)':
            ex.append((T, e, k, [round(float((8 * d * t) % 8), 2) for d in T]))
    return c, ex

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    tot = Counter(); exs = []
    for c, ex in parts: tot.update(c); exs += ex
    print(f"residual sets <= 32 with one multiple of 8 and both edges occupied: {sum(tot.values())}")
    for k, v in sorted(tot.items(), key=lambda x: -x[1])[:16]: print(f"  {k}: {v}")
    for T, e, k, pos in exs[:10]:
        print(f"  T {T}: scale reading e = {e} (k = {k}); positions at the isolation (eighths) {pos}")
