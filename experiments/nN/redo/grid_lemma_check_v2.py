"""E403 (2026-10-05), grid_lemma_check_v2: as grid_lemma_check_v1, adding the reduction points of the readings
= 2 mod 4.  A reading 2v (v odd) blocks no shift at tau = (2m+1)/(2v) (its offset is an odd whole number); an odd
reading w blocks one shift at tau = m/w.  In a cost-exactly-8 pattern either leaves a shift free at any such tau
clear for the cofactors [PROVISIONAL: counting tool; supports: the free shift].  Population and pass condition as v1;
the remainder is now the sets whose cofactors block every reduction point of every non-multiple.
"""
import itertools, math, sys, collections
from fractions import Fraction as F
sys.path.insert(0, '.')
from grid_lemma_check_v1 import cd, E8, lonely, cascade, typ

def reduction_points(d):
    if d % 2: return [F(m, d) for m in range(1, d)]
    if d % 4 == 2: return [F(2 * m + 1, d) for m in range(d // 2)]
    return []

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 48
    out = open('grid_lemma_check_v2.out', 'w'); out.write(__doc__ + "\n")
    stats = collections.Counter(); fails = []; remex = []
    mults = [x for x in range(8, N + 1, 8)]; nonm = [x for x in range(1, N + 1) if x % 8]
    for M in itertools.combinations(mults, 3):
        C = [x // 8 for x in M]
        for NM in itertools.combinations(nonm, 4):
            ty = ''.join(sorted(typ(d) for d in NM))
            if ty not in ('oooo', 'oott'): continue
            S = M + NM
            if math.gcd(*S) != 1: continue
            stats[ty] += 1
            tau = None
            for d in NM:
                for p in reduction_points(d):
                    if all(cd(c * p) >= E8 for c in C): tau = p; break
                if tau is not None: break
            if tau is not None:
                stats[(ty, 'reduction point')] += 1
                if not any(lonely(S, (tau + k) / 8) for k in range(8)): fails.append(S)
            else:
                stats[(ty, 'remainder')] += 1
                if len(remex) < 10: remex.append((S, cascade(list(S))))
    out.write("7-subsets of [1,%d], three multiples of 8, gcd 1: %s\n" % (N, dict(stats)))
    out.write("failures: %d %s\n" % (len(fails), fails[:5]))
    for e in remex: out.write("  remainder %s landing %s\n" % e)
    out.close(); print(open('grid_lemma_check_v2.out').read()[len(__doc__):])
