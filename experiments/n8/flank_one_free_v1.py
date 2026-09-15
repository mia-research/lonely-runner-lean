"""The order-8 runners (every 8-subset of [1,20]) with exactly one unshadowed flank, in detail: the subject's differences; for
each flank its kind and smallest blocking set; the free flank, its ratios, and its first lonely opening."""
import itertools, math
from flank_near_extreme_v1 import analyse, blocks_all
n = 8
for v in itertools.combinations(range(1, 21), 8):
    for i in range(8):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        free, shad = analyse(ds, n)
        if len(free) != 1: continue
        e = free[0]; M = n * e
        k = next(k for k in range(e) if all(e <= (d * (n * k + 1)) % M <= (n - 1) * e for d in ds if d != e))
        ratios = [f'{d // math.gcd(d, e)}/{e // math.gcd(d, e)}' for d in sorted(ds) if d != e]
        print(f'speeds {v} subject {v[i]}: differences {sorted(ds)}')
        print(f'   free flank {e}: ratios {ratios}; first lonely opening k={k}, t = {n*k+1}/{n*e}')
        print(f'   shadowed: {[(f, kind, dens) for f, kind, size, dens in shad]}')
