"""residual_cascade_v1 follow-up.  For residual sets (every modulus 2..8 divides some reading), readings <= 32, the
cascade's isolation t* = (8k+1)/(8e) away from the bound: is the new scale's reading e one that the grid at t = 1/8
left blocked (a multiple of 8), and is the multiplier 8k+1 the smallest one past e/... ; tallied by exact situation."""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from residual_cascade_v1 import residual, cascade_flank

def chunk(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if not residual(T): continue
        t, e, k, mv = cascade_flank(list(T))
        if k == 0 and e == T[0]: c['bound'] += 1; continue
        m8 = [d for d in T if d % 8 == 0]
        c[('e multiple of 8' if e % 8 == 0 else 'e not a multiple of 8',
           'd_min = 1' if T[0] == 1 else 'd_min > 1',
           'k = e/8' if 8 * k == e else ('8k+1 < e' if 8 * k + 1 < e else '8k+1 > e'))] += 1
    return c

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    tot = Counter()
    for p in parts: tot.update(p)
    n = sum(tot.values())
    print(f"residual sets, readings <= 32: {n}")
    for k, v in sorted(tot.items(), key=lambda x: -x[1]): print(f"  {k}: {v}")
