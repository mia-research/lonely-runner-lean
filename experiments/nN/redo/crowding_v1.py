"""Owner: runners are bounded by their neighbours; crowd them too evenly and you have an AP again.  Test with the
cascade, exactly, on every set of 7 distinct whole-number readings in 1..24 where the bound 1/(8 d_min) is NOT lonely
(the cascade had to move).  Gaps: g_1 = d_1 (subject to its nearest), g_j = d_j - d_(j-1) (the other runners' own
neighbour separations).
  crowding     : g_min = the smallest of g_2..g_7, against d_1
  blockers     : the readings in the slot at the bound; is each one in a crowded run (a neighbour gap < d_1)?
  at t*        : the cascade's isolation; how far apart the tightest pair sits there, 8 g_min t* in eighths; and for the
                 maximal run of equal smallest gaps (an evenly crowded group), whether its members sit at consecutive
                 AP positions (every step 8 g t* mod 8 the same and the group clear): AP again at the group's scale."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from residual_cascade_v1 import cascade_flank

def chunk(first):
    c = Counter(); ratio = Counter(); step = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        t0 = F(1, 8 * T[0])
        if all(nd(d * t0) >= F(1, 8) for d in T): continue
        gaps = [T[0]] + [T[j] - T[j - 1] for j in range(1, 7)]
        gmin = min(gaps[1:])
        blockers = [j for j, d in enumerate(T) if nd(d * t0) < F(1, 8)]
        crowded = lambda j: (j >= 1 and gaps[j] < T[0]) or (j + 1 <= 6 and gaps[j + 1] < T[0])
        c['sets'] += 1
        c['smallest other gap < d_1'] += gmin < T[0]
        c['every blocker in a crowded pair'] += all(crowded(j) for j in blockers)
        c['some blocker in a crowded pair'] += any(crowded(j) for j in blockers)
        t, e, k, mv = cascade_flank(list(T))
        x = 8 * gmin * t
        ratio[min(int(x), 8)] += 1
        c['tightest pair at least one eighth apart at t*'] += x >= 1
        # the scale reading e at the isolation: is it a reading adjacent to a smallest gap (in the crowded group)?
        ie = T.index(e)
        c['scale reading sits next to a smallest gap'] += (ie >= 1 and gaps[ie] == gmin) or (ie + 1 <= 6 and gaps[ie + 1] == gmin)
    return c, ratio

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); ratio = Counter()
    for a, b in parts: c.update(a); ratio.update(b)
    n = c['sets']
    print(f"sets where the bound is not lonely: {n}")
    for k in ['smallest other gap < d_1', 'some blocker in a crowded pair', 'every blocker in a crowded pair',
              'tightest pair at least one eighth apart at t*', 'scale reading sits next to a smallest gap']:
        print(f"  {k}: {c[k]}")
    print(f"  tightest pair's separation at t*, in eighths (floor, capped at 8): {sorted(ratio.items())}")
