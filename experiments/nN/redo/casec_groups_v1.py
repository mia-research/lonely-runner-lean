"""E152 v2: recursive decomposition.  Split the readings at the largest consecutive gap, recursively, until every group
has spread <= 7 (an R1 group).  At the cascade's landing: is every group on one lap?  Which group holds the flank (the
fastest group, or another)?  Populations as casec_regime_v1: P1 (d_min = 1, readings <= 32, spread > 24), P2 random wide,
P3 constructed members.  Exact."""
import itertools, random, io, contextlib, os
from fractions import Fraction as F
from math import floor, exp, log
from collections import Counter
from multiprocessing import Pool
from casec_regime_v1 import casc
def groups(T):
    if F(T[-1], T[0]) <= 7: return [T]
    gi = max(range(1, len(T)), key=lambda i: F(T[i], T[i - 1]))
    return groups(T[:gi]) + groups(T[gi:])
def analyse(T):
    T = tuple(sorted(T)); t0 = F(1, 8 * T[0]); ts = casc(T, t0)
    if ts == t0: return ('at the bound',)
    gs = groups(T)
    one = all(len({floor(d * ts) for d in g}) == 1 for g in gs)
    f = next(d for d in T if (8 * d * ts) % 8 == 1)
    fg = next(i for i, g in enumerate(gs) if f in g)
    return ('%d R1 groups' % len(gs), 'every group on one lap' if one else 'some group split over laps',
            'flank in the fastest group' if fg == len(gs) - 1 else 'flank in group %d of %d' % (fg + 1, len(gs)))
def chunk1(second):
    C = Counter()
    for rest in itertools.combinations(range(second + 1, 33), 5):
        T = (1, second) + rest
        if T[-1] > 24: C[analyse(T)] += 1
    return C
def p2(seed):
    rng = random.Random(seed); C = Counter()
    for _ in range(2500):
        dmin = rng.randrange(1, 60); S = rng.uniform(25, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) == 7: C[analyse(tuple(xs))] += 1
    return C
if __name__ == '__main__':
    here = os.getcwd(); os.chdir('..')
    with contextlib.redirect_stdout(io.StringIO()):
        g = {}; exec(open('residual_members_C_v1.py').read(), g)
    os.chdir(here)
    with Pool(8) as p:
        C1 = Counter(); [C1.update(c) for c in p.imap_unordered(chunk1, range(2, 28))]
        C2 = Counter(); [C2.update(c) for c in p.imap_unordered(p2, range(8))]
    C3 = Counter(analyse(S) for m in 'AB' for S in g['found'][m])
    for name, C in (('P1', C1), ('P2 random wide', C2), ('P3 constructed', C3)):
        print("==", name, "(%d sets)" % sum(C.values()))
        for k, v in sorted(C.items(), key=lambda kv: -kv[1]): print("  %7d  %s" % (v, k))
