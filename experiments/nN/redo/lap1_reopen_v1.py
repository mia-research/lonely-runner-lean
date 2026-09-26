"""E100's next step.  The sets whose cascade isolation is not an explicit view (35,215 of the 346,104 sets of seven
distinct whole-number readings in 1..24 of the slowest runner; every runner moving, none at rest) land at a later
opening (8K+1)/(8e) with K >= 2.  Two questions, answered with the cascade, exact (Fraction), BSM (clear at 1/8
closed):

 (a) What closes the lap-1 scales there: at every lap-0/lap-1 opening (8k+1)/(8e), k in {0, 1}, at or after the bound,
     which runners are in the slot.  Is one runner in the slot at all of them?  The fewest runners that between them
     block every one (exact hitting set, by size).
 (b) Does a lap-1 scale reopen once one runner's speed moves: each reading moved by -2, -1, +1, +2 (kept positive and
     distinct), the cascade rerun; does it now land at a lap <= 1 opening, and is the runner moved one of the blockers?
"""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from cascade_vs_menu_v1 import views

E8 = F(1, 8)

def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)

def landing(T, t):
    for e in T:
        x = e * t - E8
        if x.denominator == 1: return e, int(x)

def blockers_of_lap1(T):
    b0 = F(1, 8 * T[0])
    cands = sorted({F(8 * k + 1, 8 * e) for e in T for k in (0, 1) if F(8 * k + 1, 8 * e) >= b0})
    return [frozenset(d for d in T if nd(d * t) < E8) for t in cands]

def hitting(T, blk):
    for r in range(1, 8):
        for S in itertools.combinations(T, r):
            s = set(S)
            if all(b & s for b in blk): return r, [c for c in itertools.combinations(T, r) if all(b & set(c) for b in blk)]
    return None, []

def chunk(first):
    c = Counter(); hs = Counter(); common = Counter(); hitrank = Counter(); reopen_by = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; ts = cascade(T)
        if any(t == ts for t in views(T).values()): continue
        c['exceptions'] += 1
        e, K = landing(T, ts); c[f'landing lap K={K}'] += 1
        blk = blockers_of_lap1(T)
        if any(not b for b in blk):
            c['a lap-0/1 opening after t* is lonely'] += 1
            blk = [b for b in blk if b]
        else:
            c['every lap-0/1 opening blocked'] += 1
        allb = frozenset.intersection(*blk)
        common['one runner blocks every lap-1 opening' if allb else 'no single common blocker'] += 1
        r, sols = hitting(T, blk); hs[r] += 1
        inall = set.intersection(*[set(s) for s in sols])      # runners in every minimal hitting set
        for d in inall: hitrank[T.index(d) + 1] += 1
        any_re = False; re_runners = set()
        for j, d in enumerate(T):
            for dl in (-2, -1, 1, 2):
                nd_ = d + dl
                if nd_ <= 0 or nd_ in T: continue
                U = tuple(sorted(T[:j] + (nd_,) + T[j + 1:]))
                e2, K2 = landing(U, cascade(U))
                if K2 <= 1:
                    any_re = True; re_runners.add(d)
        c['some single move reopens lap <= 1' if any_re else 'no single move reopens'] += 1
        if any_re:
            reopen_by['a reopening move is on a runner in every minimal blocking set' if re_runners & inall else
                      'no reopening move is on such a runner'] += 1
    return c, hs, common, hitrank, reopen_by

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    acc = [Counter() for _ in range(5)]
    for p in parts:
        for a, b in zip(acc, p): a.update(b)
    names = ['counts', 'fewest runners blocking every lap-0/1 opening', 'common blocker',
             'rank (1 = d_min) of runners in every minimal blocking set', 'reopening move and blockers']
    for n, a in zip(names, acc): print(f"{n}: {sorted(a.items(), key=lambda x: str(x[0]))}")
