"""E258 (2026-10-01): the hand-offs' alternating occupants (hole6_handoff_v1.out): how near is each to a small-denominator
ratio?  For every segment of one or two openings (an occupant that does not persist), the walker's fractional ratio
f = frac(x_j / e) and the nearest fraction p/q with q <= 8, with |f - p/q|; also, for persistent segments (three or more
openings), the same.  The record's exact shadowing families are lattice walkers with small denominators (the 1/2 pair
family; triples (2,4,4), (3,3,3), (3,6,6), (5,5,5); v21 6.9, 6.11).  A walker at f = p/q + delta has its verdict repeat
with period q up to the drift q*delta per period."""
import sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import holef_cascade_v1 as HF, hole6_wide_v1 as W
from hole6_shadow_v2 import read as read_shadows
from hole6_handoff_v1 import study

def nearest(f):
    best = None
    for q in range(1, 9):
        p = round(f * q)
        d = abs(f - F(p, q))
        if best is None or d < best[2]:
            best = (p % q if q > 1 else p, q, d)
    return best

def null_by_q():
    """Exact: the measure of f in [0, 1) whose nearest fraction p/q (q <= 8) has each denominator (uniform f), and the
    measure within 0.01 of its nearest fraction."""
    fr = sorted({F(p, q) for q in range(1, 9) for p in range(0, q + 1)})
    meas = Counter(); near = F(0)
    for i, x in enumerate(fr):
        lo = (fr[i - 1] + x) / 2 if i > 0 else x
        hi = (x + fr[i + 1]) / 2 if i + 1 < len(fr) else x
        meas[x.denominator] += hi - lo
        near += min(hi, x + F(1, 100)) - max(lo, x - F(1, 100))
    return meas, near


if __name__ == '__main__':
    pops = [HF.gen(6, 240, 1000)[0], W.gen(242, 1000)[0]]
    items = []
    for pop in pops:
        with Pool(8) as pool:
            items += [x for part in pool.map(read_shadows, pop, chunksize=10) for x in part if not x['common']]
    with Pool(8) as pool:
        res = pool.map(study, items)
    out = open('hole6_handoff_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for label, sel in (('alternating occupants (segments of 1-2 openings)', lambda L: L <= 2), ('persistent occupants (3 or more)', lambda L: L >= 3)):
        dq = Counter(); dd = Counter(); n = 0
        for r in res:
            for a, b, L, rank, desc in r['segs']:
                if not sel(L):
                    continue
                x = r['block'][rank - 1]; e = r['e']
                f = F(x, e) - (F(x, e).numerator // F(x, e).denominator)
                p, q, d = nearest(f)
                dq[q] += 1; n += 1
                dd['|f - p/q| < 0.01' if d < F(1, 100) else ('< 0.03' if d < F(3, 100) else ('< 0.06' if d < F(6, 100) else '>= 0.06'))] += 1
        w("%s (%d): nearest denominator q: %s; distance: %s" % (label, n, dict(sorted(dq.items())), dict(dd)))
    meas, near = null_by_q()
    w("matched null, uniform f (exact, Farey regions of order 8): expected share by nearest q: %s; within 0.01: %.3f" % (
        {q: round(float(m), 4) for q, m in sorted(meas.items())}, float(near)))
    out.close()
    print(open('hole6_handoff_v2.out').read()[len(__doc__):])
