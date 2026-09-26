"""The sets (readings <= 24) that exactly ONE menu family isolates (menu_forcing_v1): examples per family, with the
instant(s) that work and each reading's position there in eighths, and the cascade's own isolation.  Exact."""
import itertools
from fractions import Fraction as F
from math import gcd
from collections import defaultdict
from multiprocessing import Pool
from arrangement_lib import nd
from menu_forcing_v1 import families, lonely
from residual_cascade_v1 import cascade_flank

def chunk(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        f = families(T)
        if len(f) == 1: out.append((T, next(iter(f))))
    return out

if __name__ == '__main__':
    with Pool() as pool: res = [x for p in pool.map(chunk, range(1, 19)) for x in p]
    by = defaultdict(list)
    for T, f in res: by[f].append(T)
    for f, Ts in sorted(by.items()):
        print(f"{f}: {len(Ts)} sets; e.g.")
        for T in Ts[:4]:
            t, e, k, mv = cascade_flank(list(T))
            print(f"   T {T}: cascade isolation t = {t} (reading {e}, lap {k}); positions (eighths) {[round(float((8 * d * t) % 8), 2) for d in T]}")
