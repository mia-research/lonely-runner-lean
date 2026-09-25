"""Core against pair: a pigeonhole between the core's lonely set and the pair's blocked meetings.

For a pair {d, d'} (m = d + d'), the meetings K/m inside the core's lonely cells (at 1/8) against the
meetings the pair blocks: if the first exceeds the second, some meeting is lonely.  Then the
enrichment (fraction of meetings in the core's lonely set / its measure), all pairs and best pair,
against random moduli of the same size and the best of 21 such.  RESULT: no interaction signal; the
best pair's enrichment is below the best of 21 random moduli, and the mean over pairs is 1.
"""
import itertools, random
from fractions import Fraction as Fr
from math import ceil, floor
from collections import Counter
_fp = __file__.replace('pair_interplay_v1.py', 'fast_pair_v1.py'); __file__ = _fp
exec(open(_fp).read().split('def levels(S):')[0])
def meet_counts(S, d, d2):
    C = [x for x in S if x not in (d, d2)]; m = d + d2
    cells = cells_of(C)
    inside = set()
    for a, b in cells:
        for K in range(ceil(a * m), floor(b * m) + 1):
            if 0 < K < m: inside.add(K)
    blocked = {K for K in range(1, m) if not (Fr(1, 8) <= (d * Fr(K, m)) % 1 <= Fr(7, 8))}
    mu = sum(b - a for a, b in cells)
    return len(inside), len(blocked), mu, len(cells), m
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
random.seed(18); easy = random.sample([S for S in R40 if S not in set(f25)], 400)
for label, sets in (("28 hard", hard), ("1,586 failing q = 2..5", f25), ("400 ordinary", easy)):
    ex = bnd = 0
    for S in sets:
        e1 = b1 = False
        for d, d2 in itertools.combinations(sorted(S), 2):
            ni, nb, mu, nc, m = meet_counts(S, d, d2)
            if ni > nb: e1 = True
            if mu * m - nc - 1 > nb: b1 = True          # guaranteed meetings inside >= mu*m - (#cells) - 1
        ex += e1; bnd += b1
    print(f"{label}: pigeonhole, meetings in core cells > blocked meetings: {ex}/{len(sets)};  from the core's measure and cell count alone: {bnd}/{len(sets)}")
random.seed(19)
five = [tuple(sorted(random.sample(range(1, 41), 5))) for _ in range(20000)]
M = sorted((float(sum(b - a for a, b in cells_of(C))), C) for C in five)
print(f"20,000 random 5-sets: lonely measure at 1/8: min {M[0][0]:.4f} at {M[0][1]}, 1% {M[200][0]:.4f}, median {M[10000][0]:.3f};  (1,2,3,4,5): {float(sum(b - a for a, b in cells_of((1,2,3,4,5)))):.4f}")

def frac_inside(C, m):
    inside = 0
    for a, b in cells_of(C):
        inside += len([K for K in range(ceil(a * m), floor(b * m) + 1) if 0 < K < m])
    return inside / (m - 1)
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
random.seed(20); easy = random.sample([S for S in R40 if S not in set(f25)], 300)
for label, sets in (("28 hard", hard), ("300 ordinary", easy)):
    allr = []; nullr = []; bestr = []; nullbest = []
    for S in sets:
        rs = []; nb = []
        for d, d2 in itertools.combinations(sorted(S), 2):
            C = [x for x in S if x not in (d, d2)]; m = d + d2
            mu = sum(b - a for a, b in cells_of(C))
            if mu == 0: continue
            r = frac_inside(C, m) / float(mu); rs.append(r); allr.append(r)
            mr = random.randrange(max(9, m - 5), max(10, m + 6))                 # null: a random modulus of the same size
            nullr.append(frac_inside(C, mr) / float(mu)); nb.append(frac_inside(C, mr) / float(mu))
        bestr.append(max(rs)); nullbest.append(max(nb))
    avg = lambda v: sum(v) / len(v)
    print(f"{label}: enrichment (meeting fraction in core-lonely set / core measure): all pairs mean {avg(allr):.2f};  best pair mean {avg(bestr):.2f};  null (random modulus of the same size) mean {avg(nullr):.2f}, null best of 21 {avg(nullbest):.2f}")
