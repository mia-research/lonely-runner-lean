"""nearest_nudge_v1 on widely spread readings, where the range no longer forces small shifts: random sets of 7 distinct
whole-number readings with d_min in 1..20 and the rest up to 2000 (the slowest runner; all runners moving).  Same
classification of first-move failures: edge (shift < 3/4, pushed across 7/8), wrap (shift >= 3/4), back (a collider in
the slot again).  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def job(seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(4000):
        m = rnd.randint(1, 20); T = sorted({m} | set(rnd.sample(range(m + 1, 2001), 6)))
        if len(T) != 7: continue
        T = tuple(T); t0 = F(1, 8 * m)
        col = [d for d in T if nd(d * t0) < E8]
        if not col: continue
        c['bound not lonely'] += 1
        ex = {d: (F(floor(d * t0 - E8) + 1) + E8) / d for d in col}
        b = max(ex, key=lambda x: ex[x]); t1 = ex[b]
        slot = [d for d in T if nd(d * t1) < E8]
        if not slot: c['first move isolates'] += 1; continue
        kinds = set()
        for d in slot:
            D = d * (t1 - t0)
            kinds.add('back' if d in col else ('edge' if D < F(3, 4) else 'wrap'))
        c[tuple(sorted(kinds))] += 1
    return c

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(job, range(16))
    c = Counter()
    for p in parts: c.update(p)
    print(f"bound not lonely: {c['bound not lonely']}; the first move isolates: {c['first move isolates']}")
    for k, v in sorted(c.items(), key=lambda x: -x[1]):
        if isinstance(k, tuple): print(f"  failure kinds {k}: {v}")
