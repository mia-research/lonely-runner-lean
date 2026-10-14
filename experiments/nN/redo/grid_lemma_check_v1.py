"""E403 (2026-10-05), grid_lemma_check_v1: derivation check of the grid argument on shape (3,4) sets of types
(o,o,o,o) and (o,o,t,t), and the divisible remainder read through the cascade.  Exact (Fractions).

Argument (by hand): three cofactors c (multiples 8c) and an odd non-multiple w with w dividing no cofactor: some m in
[1, w-1] has ||c*m/w|| >= 1/8 for all three [PROVISIONAL: counting tool; supports: the grid point] (each cofactor blocks
at most w/3 grid points, all three block m = 0); at tau = m/w the reading w blocks one shift and the other three
non-multiples at most two each, so some k leaves (tau + k)/8 lonely [PROVISIONAL: counting tool; supports: the free
shift].  Divisible remainder: every odd non-multiple divides some cofactor.
Population: every 7-subset of [1, N] with exactly three multiples of 8, non-multiples of type (o,o,o,o) or (o,o,t,t),
gcd 1 (no field filtering beyond that; these are not EightResidual members).
Pass condition: for every set with an odd reading dividing no cofactor, the constructed (m, k) gives an exactly lonely
instant; failures listed.  For the divisible remainder: the cascade's landing and the opener's class.
"""
import itertools, math, sys, collections
from fractions import Fraction as F

def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
E8 = F(1, 8)
def lonely(S, t): return all(cd(d * t) >= E8 for d in S)
def cascade(S):
    t = F(1, 8 * min(S))
    while True:
        bl = [d for d in S if cd(d * t) < E8]
        if not bl: return t
        t = max(F(8 * round(d * t) + 1, 8 * d) for d in bl)
def typ(d): return 'o' if d % 2 else ('t' if d % 4 == 2 else ('f' if d % 8 == 4 else 'm'))

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 48
    out = open('grid_lemma_check_v1.out', 'w'); out.write(__doc__ + "\n")
    stats = collections.Counter(); fails = []; rem = collections.Counter(); remex = []
    mults = [x for x in range(8, N + 1, 8)]; nonm = [x for x in range(1, N + 1) if x % 8]
    for M in itertools.combinations(mults, 3):
        C = [x // 8 for x in M]
        for NM in itertools.combinations(nonm, 4):
            ty = ''.join(sorted(typ(d) for d in NM))
            if ty not in ('oooo', 'oott'): continue
            S = M + NM
            if math.gcd(*S) != 1: continue
            stats[ty] += 1
            odds = [d for d in NM if d % 2]
            free = [w for w in odds if all(c % w for c in C)]
            if free:
                w = free[0]
                ms = [m for m in range(1, w) if all(cd(F(c * m, w)) >= E8 for c in C)]
                ok = False
                if ms:
                    tau = F(ms[0], w)
                    ok = any(lonely(S, (tau + k) / 8) for k in range(8))
                stats[(ty, 'grid argument applies')] += 1
                if not ok: fails.append(S)
            else:
                t = cascade(list(S))
                opener = [d for d in S if (d * t - math.floor(d * t)) == E8]
                rem[(ty, ','.join(sorted(set(typ(d) for d in opener))))] += 1
                if len(remex) < 8: remex.append((S, t, opener))
    out.write("7-subsets of [1,%d], three multiples of 8, gcd 1: %s\n" % (N, dict(stats)))
    out.write("grid-argument failures: %d %s\n" % (len(fails), fails[:5]))
    out.write("divisible remainder (every odd non-multiple divides a cofactor), by type and opener class: %s\n" % dict(rem))
    for e in remex: out.write("  remainder example %s landing %s opener %s\n" % e)
    out.close(); print(open('grid_lemma_check_v1.out').read()[len(__doc__):])
