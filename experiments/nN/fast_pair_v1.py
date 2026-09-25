"""The top pair as one runner: the fast-pair reduction, tested at three levels.

At the mirror meetings K/m of a pair {d, d'} (m = d + d') the pair reads x and 1 - x, so it acts as
one runner: S is lonely at K/m iff the core C = S - {d, d'} is lonely there and ||x|| >= 1/8.  SC:
ratio d'/d <= 3 and a lonely cell of C (at 1/8) containing two consecutive meetings; consecutive x
differ by d/m in [1/4, 3/4], so one of the two is clear.  Levels: exact; SC; SC from order six's
margin alone (m >= 24 max C).  Then the core's longest lonely cell at 1/8, in units of 1/max C: on
the hard sets, and on 20,000 random 5-sets (minimum 1/4, at the progressions (1..5)k).
"""
import itertools, random
from fractions import Fraction as Fr
from math import ceil, floor
from collections import Counter
__file__ = __file__.replace('fast_pair_v1.py', 'player_census_v1.py')
src = open(__file__).read(); exec(src[:src.index("R40 = [S")])
def cells_of(C, n=8):
    z = sorted((Fr(n * k - 1, n * d), Fr(n * k + 1, n * d)) for d in C for k in range(0, d + 1))
    out = []; hi = None
    for lo, h in z:
        if hi is not None and lo >= hi and hi < 1: out.append((hi, lo))
        if hi is None or h > hi: hi = h
    return out
def levels(S):
    res = {'exact': None, 'SC': None, 'order6': None}
    for d, d2 in itertools.combinations(sorted(S), 2):
        C = [x for x in S if x not in (d, d2)]; m = d + d2
        ratio_ok = 3 * d >= d2
        cells = cells_of(C)
        for a, b in cells:
            Ks = list(range(ceil(a * m), floor(b * m) + 1))
            if not res['exact'] and any(Fr(1, 8) <= (d * Fr(K, m)) % 1 <= Fr(7, 8) for K in Ks): res['exact'] = (d, d2)
            if ratio_ok and len(Ks) >= 2 and not res['SC']: res['SC'] = (d, d2)
        if ratio_ok and m >= 24 * max(C) and not res['order6']: res['order6'] = (d, d2)
    return res
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
random.seed(16); easy = random.sample([S for S in R40 if S not in set(f25)], 400)
for label, sets in (("28 hard", hard), ("400 ordinary", easy)):
    c = Counter(); pairs = Counter()
    for S in sets:
        r = levels(S)
        for k, v in r.items(): c[k] += bool(v)
        if r['SC']: s = sorted(S); pairs[(s.index(r['SC'][0]) + 1, s.index(r['SC'][1]) + 1)] += 1
    print(f"{label}: exact {c['exact']}/{len(sets)};  structural SC (ratio <= 3, two consecutive meetings in a core cell) {c['SC']}/{len(sets)};  from order 6's margin alone {c['order6']}/{len(sets)}")
    print(f"   first SC pair by rank: {pairs.most_common(8)}")

def longest(C): return max((b - a for a, b in cells_of(C)), default=Fr(0))
def best_pair_margin(S):
    """over pairs with ratio <= 3: max of (longest core cell) * m  -- SC needs about 2"""
    best = None
    for d, d2 in itertools.combinations(sorted(S), 2):
        if 3 * d < d2: continue
        C = [x for x in S if x not in (d, d2)]
        v = longest(C) * (d + d2)
        if best is None or v > best[0]: best = (v, longest(C) * max(C), (d, d2))
    return best
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
for label, sets in (("28 hard", hard), ("1,586 failing q = 2..5", f25)):
    vals = sorted(best_pair_margin(S) for S in sets)
    print(f"{label}: best pair's (longest core cell) x (d + d'): min {float(vals[0][0]):.2f} median {float(vals[len(vals)//2][0]):.2f};  core cell x max(core): min {float(min(v[1] for v in vals)):.3f}")
random.seed(17)
five = [tuple(sorted(random.sample(range(1, 41), 5))) for _ in range(20000)]
L = sorted((float(longest(C) * max(C)), C) for C in five)
print(f"20,000 random 5-sets from [1,40]: longest lonely cell at 1/8, x max: min {L[0][0]:.4f} at {L[0][1]}, 1% {L[200][0]:.4f}, median {L[10000][0]:.3f}")
ap = [tuple(k * j for j in range(1, 6)) for k in (1, 2, 3)]
print("   the progression cores:", [(C, round(float(longest(C) * max(C)), 4)) for C in ap])
