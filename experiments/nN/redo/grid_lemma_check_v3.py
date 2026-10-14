"""E403 (2026-10-05), grid_lemma_check_v3: the full remainder of grid_lemma_check_v2 (v2 printed only its first 10),
with a divisibility record for every non-multiple.  Exact (Fractions), same population as v1/v2: every 7-subset of
[1, N] with exactly three multiples of 8, non-multiples of type (o,o,o,o) or (o,o,t,t), gcd 1.
Recorded for every remainder set S (cofactors block every reduction point of every non-multiple):
 for each odd non-multiple w, the cofactors c with w | c;
 for each non-multiple 2v (v odd), the cofactors c with v | c, and with 2v | c;
 the cascade's landing.  No pass condition: this is a listing.
"""
import itertools, math, sys, collections
from fractions import Fraction as F
sys.path.insert(0, '.')
from grid_lemma_check_v1 import cd, E8, cascade, typ
from grid_lemma_check_v2 import reduction_points

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 48
    out = open('grid_lemma_check_v3.out', 'w'); out.write(__doc__ + "\n")
    rem = []; summary = collections.Counter()
    mults = [x for x in range(8, N + 1, 8)]; nonm = [x for x in range(1, N + 1) if x % 8]
    for M in itertools.combinations(mults, 3):
        C = [x // 8 for x in M]
        for NM in itertools.combinations(nonm, 4):
            ty = ''.join(sorted(typ(d) for d in NM))
            if ty not in ('oooo', 'oott'): continue
            S = M + NM
            if math.gcd(*S) != 1: continue
            if any(all(cd(c * p) >= E8 for c in C) for d in NM for p in reduction_points(d)): continue
            rec = []
            for d in NM:
                if d % 2: rec.append((d, 'odd', [c for c in C if c % d == 0]))
                else:
                    v = d // 2
                    rec.append((d, 'v=%d' % v, [c for c in C if c % v == 0], [c for c in C if c % d == 0]))
            odd_all = all(r[2] for r in rec if r[1] == 'odd')
            t_v = all(r[2] for r in rec if r[1] != 'odd')
            t_2v = all(r[3] for r in rec if r[1] != 'odd')
            summary[(ty, 'every odd divides a cofactor', odd_all, 'every v divides a cofactor', t_v,
                     'every 2v divides a cofactor', t_2v)] += 1
            rem.append((S, C, rec, cascade(list(S))))
    out.write("remainder sets: %d\n" % len(rem))
    for k, v in summary.items(): out.write("summary %s: %d\n" % (k, v))
    for S, C, rec, t in rem: out.write("  %s cofactors %s; %s; landing %s\n" % (S, C, rec, t))
    out.close(); print(open('grid_lemma_check_v3.out').read()[len(__doc__):])
