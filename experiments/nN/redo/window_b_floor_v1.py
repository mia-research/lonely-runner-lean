"""E387 (2026-10-05), window_b_floor_v1: the second window of a gate crosser, in the carving's terms.

Owner: "Yes, do that for window B and keep going on layer 5".
FORCED FACT (1-D, stated before the run): the zones of reading 7 are open intervals of width 2/rho7 spaced 8/rho7, so
distinct zones are disjoint with clear gaps of length 6/rho7 between them; a closed connected window of K'_6 (the set of R in
[9,15] clear for readings 1..6) lies in the union of the zones only if it lies in ONE zone, hence only if its length is
< 2/rho7.  So K'_7 (readings 1..7 clear, R in [9,15]) is empty only if every window of K'_6 has length < 2/rho7.
Contrapositive: a window of K'_6 of length >= 2/rho7 gives a lonely R in [9,15].
QUESTION RUN: for every exact gate-crossing member of the J=1 and (every 10th) J=2 trees, the longest window of K'_6 and the
ratio r = (longest K'_6 window) * rho7 / 2; r >= 1 would be the sufficient condition above.  Misses (r < 1) are listed.
Exact (Fractions); members are the exact members of cell_members7_J{1,2}.pkl (the regions' exact points).
"""
import sys, pickle
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from core import clear_set

def work(items):
    out = []
    for idx, x in items:
        k7a = clear_set(x, F(1), F(7))
        if k7a:
            continue                                   # not a crosser
        six = x[:6]
        k6 = clear_set(six, F(9), F(15))
        k7 = clear_set(x, F(9), F(15))
        if not k6:
            out.append((idx, None, x, bool(k7))); continue
        L = max(b - a for a, b in k6)
        out.append((idx, L * x[6] / 2, x, bool(k7), len(k6), len(k7)))
    return out

if __name__ == '__main__':
    res = []
    with Pool(4) as pool:
        for J, step in ((1, 1), (2, 10)):
            d = pickle.load(open('cell_members7_J%d.pkl' % J, 'rb'))
            items = [(i, x) for i, x in d[::step]]
            chunks = [items[i:i + 500] for i in range(0, len(items), 500)]
            rr = [r for c in pool.map(work, chunks) for r in c]
            res.append((J, step, len(items), rr))
    out = open('window_b_floor_v1.out', 'w'); out.write(__doc__ + "\n")
    for J, step, n, rr in res:
        rs = [r for r in rr if r[1] is not None]
        out.write("J=%d (every %dth member, %d members): gate-crossing %d; K'_6 empty in [9,15]: %d\n" % (J, step, n, len(rr), len(rr) - len(rs)))
        if rs:
            m = min(rs, key=lambda r: r[1])
            out.write("  min r over crossers = %s (= %.6f) at member %d, rho7 = %.6f; r < 1 in %d crossers; K'_7 non-empty in all: %s\n" % (
                m[1], float(m[1]), m[0], float(m[2][6]), sum(1 for r in rs if r[1] < 1), all(r[3] for r in rr)))
            for r in sorted(rs, key=lambda r: r[1])[:5]:
                out.write("    r=%.5f idx=%d rho7=%.4f K'6 windows=%d K'7 windows=%d\n" % (float(r[1]), r[0], float(r[2][6]), r[4], r[5]))
    out.close(); print(open('window_b_floor_v1.out').read()[len(__doc__):])
