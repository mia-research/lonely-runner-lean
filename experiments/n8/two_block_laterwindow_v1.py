"""E648: the records whose landing is in a later component of N's clear set (two_block_nearest_block_test_v2):
tabulate by p, regime, which block is N, the size of N and of the other block O, the step ratio of O to N, and whether
O's zones cover N's first component entirely (the reason the first component fails). Exact."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
def comps(ds, T):
    zones = sorted(((m - E) / d, (m + E) / d) for d in ds for m in range(0, int(d * T) + 2))
    out = []; cur = F(0)
    for a, b in zones:
        if a >= cur: out.append((cur, a))
        cur = max(cur, b)
    return out
tab = Counter(); ratio = Counter(); tot = Counter()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    A = G + (p - 1); v = sp(p, A, b)
    ownb = list(range(p)) if k < p else list(range(p, 8))
    own = [i for i in ownb if i != k]; oth = [i for i in range(8) if i not in ownb]
    do = [abs(v[i] - v[k]) for i in own]; dx = [abs(v[i] - v[k]) for i in oth]
    Nown = min(do) <= min(dx)
    N, O = (do, dx) if Nown else (dx, do)
    nsize = len(ownb) if Nown else len(oth)   # runners in N's block (the subject counted when N is own)
    stepN = (F(1) if k < p else b) if Nown else (b if k < p else F(1))
    stepO = (b if k < p else F(1)) if Nown else (F(1) if k < p else b)
    reg = 'interleaved' if G <= 0 else 'gap'
    key0 = (reg, 'N block size %d' % nsize, 'O/N step %s' % ('<1' if stepO < stepN else '>1'))
    tot[key0] += 1
    c1 = comps(N, t + 2)[0]
    if c1[0] <= t <= c1[1]: continue
    tab[key0] += 1
for kk in sorted(tot): print("%6d of %7d later-window  %s" % (tab[kk], tot[kk], kk))
