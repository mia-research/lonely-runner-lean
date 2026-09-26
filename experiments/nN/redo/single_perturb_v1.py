"""Perturb the 375 reading sets (<= 24) that exactly one menu view isolates (menu_single_v1): each reading moved by
+-1, +-2 (one runner's speed changed; readings kept positive and distinct).  For each perturbed set: the views that
isolate it (menu_forcing_v1.families) and the cascade's isolation R.  Summaries: does the single view survive the
perturbation, how many views open, how far the cascade's isolation moves.  Exact."""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from menu_forcing_v1 import families
from residual_cascade_v1 import cascade_flank

def singles(first):
    return [((first,) + r, next(iter(families((first,) + r)))) for r in itertools.combinations(range(first + 1, 25), 6)
            if len(families((first,) + r)) == 1]

def perturb(args):
    T, f0 = args
    t0, e0, k0, _ = cascade_flank(list(T)); R0 = 8 * T[0] * t0
    rows = []
    for i in range(7):
        for sh in (-2, -1, 1, 2):
            U = list(T); U[i] += sh
            if U[i] <= 0 or len(set(U)) < 7: continue
            U = tuple(sorted(U)); fs = families(U)
            t, e, k, _ = cascade_flank(list(U)); R = 8 * U[0] * t
            rows.append((f0 in fs, len(fs), float(R / R0), len(fs) == 0))
    return f0, rows

if __name__ == '__main__':
    with Pool() as pool:
        S = [x for p in pool.map(singles, range(1, 19)) for x in p]
        res = pool.map(perturb, S)
    print(f"single-view sets: {len(S)}")
    by = {}
    for f0, rows in res:
        a = by.setdefault(f0, Counter())
        for keep, nv, rr, none in rows:
            a['moves'] += 1; a['view survives'] += keep; a['views open (sum)'] += nv; a['no view'] += none
            a['R ratio > 1.5'] += rr > 1.5
    for f0, a in sorted(by.items()):
        print(f"  {f0:3s}: perturbed sets {a['moves']}; its view still works {a['view survives']}; mean views open {a['views open (sum)'] / a['moves']:.2f}; "
              f"no view {a['no view']}; cascade isolation moved by a factor > 1.5 in {a['R ratio > 1.5']}")
