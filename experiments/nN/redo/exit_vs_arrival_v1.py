"""Owner: measure over all arrangements with the cascade: at each move, the setter's time to leave the slot (J) against
the time until the next runner arrives at the slot (A).  The cascade continues while someone arrives before the setter
leaves (A < J) and stops at the first move with J < A.  Exhaustive: every set of 7 distinct whole-number readings in
1..24 of the slowest runner (C(24,7) = 346,104; every runner moving: subject at c > 0, others at c + reading).  Exact.
Recorded per arrangement: moves; for the final move the setter's rank (0 = nearest) and J; the smallest A/J seen at a
continuing move and the largest A/J... ; and whether the stop comes at the first move whose setter is the fastest
runner in the slot, etc. (summaries below)."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool

E8 = F(1, 8)

def nd(x):
    x = x % 1; return min(x, 1 - x)

def run(ds):
    t = F(1, 8 * ds[0]); moves = 0; last = None; lastJ = None; lastA = None
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < E8]
        if not way: break
        cand = {i: (F(floor(ds[i] * t - E8) + 1) + E8) / ds[i] for i in way}
        s = max(cand, key=lambda x: cand[x]); t2 = cand[s]
        # next arrival after t among runners not in the slot
        A = min(((floor(d * t + E8) + 1) - E8) / d - t for i, d in enumerate(ds) if i not in way)
        last, lastJ, lastA = s, t2 - t, A; moves += 1; t = t2
    return moves, last, (lastA / lastJ if lastJ else None), 8 * ds[0] * t

def chunk(first):
    out = Counter(); lastrank = Counter(); ratio_min = None; Rmax = F(0); ex = None
    for rest in itertools.combinations(range(first + 1, 25), 6):
        ds = (first,) + rest
        mv, s, r, R = run(ds)
        out[mv] += 1
        if s is not None: lastrank[s] += 1
        if R > Rmax: Rmax, ex = R, ds
    return out, lastrank, Rmax, ex

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    moves = Counter(); last = Counter(); Rmax = F(0); ex = None
    for o, l, R, e in parts:
        moves.update(o); last.update(l)
        if R > Rmax: Rmax, ex = R, e
    tot = sum(moves.values())
    print(f"reading sets {tot}")
    print(f"  cascade moves: {sorted(moves.items())}")
    print(f"  rank (0 = nearest) of the runner that sets the final move: {sorted(last.items())}")
    print(f"  largest R at the isolation: {float(Rmax):.4f} at readings {ex}")
