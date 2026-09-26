"""Checks on E102b/c: (1) do all 232 stuck sets contain two readings on multiples of 8*d_min (a double grid collision at
the bound)?  (2) the displacement R* = 8 d_min t* of all 35,215 non-view landings, against the setter's lap K.
Exact (Fraction)."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from cascade_vs_menu_v1 import views
from lap1_reopen_v1 import cascade, landing
from lap1_stuck_v1 import stuck

def chunk(first):
    c = Counter(); rk = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; ts = cascade(T)
        if any(t == ts for t in views(T).values()): continue
        m = T[0]; R = 8 * m * ts; e, K = landing(T, ts)
        rk[(K, floor(4 * R) / 4)] += 1
        if stuck(T):
            n8 = sum(1 for d in T if d % (8 * m) == 0)
            c[f'stuck, readings on multiples of 8 d_min: {n8}'] += 1
    return c, rk

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); rk = Counter()
    for a, b in parts: c.update(a); rk.update(b)
    print(sorted(c.items()))
    Ks = sorted({k for k, _ in rk})
    for K in Ks:
        print(f"setter lap K={K}: R* (quarter bins) {sorted((r, v) for (k, r), v in rk.items() if k == K)}")
