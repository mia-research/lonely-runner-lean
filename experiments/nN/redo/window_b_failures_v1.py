"""E388 (2026-10-05), window_b_failures_v1: the window-B crossers where no K'_6 window reaches 2/rho7 (E387), through the cascade.

Owner: "perturb the failures and keep going on layer 5".
CLASS: the exact crossing members of the J=1 tree (all) and J=2 tree (every tenth) whose longest K'_6 window is shorter than
2/rho7 (r < 1 in E387: 145 and 14).  For each: the landing R* (exact cascade = least clear point), its opener (reading y, lap j
with R* = (8j+1)/rho_y exactly) and whether K'_7's first window starts at a reading-7 zone exit, and the K'_6 windows against the
reading-7 zones.  PERTURBATION: each of readings 2..7 moved one at a time to 8 exact points inside the region's own range
(tree range, float LP; exact arrangement evaluated, gate re-tested): for each moved arrangement that is still a crosser, the
same record.  Recorded: opener rank distribution (base failures, moved crossers), whether K'_7 is non-empty in every moved
crosser, and every moved crosser with K'_7 empty individually.
Exact (Fractions).
"""
import sys, pickle
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from core import clear_set

def info(x):
    if clear_set(x, F(1), F(7)):
        return None
    k7 = clear_set(x, F(9), F(15))
    if not k7:
        return dict(empty=True)
    R = k7[0][0]
    opener = None
    for y in range(7):
        j = (R * x[y] - 1) / 8
        if j.denominator == 1 and j >= 0:
            opener = (y + 1, int(j)); break
    k6 = clear_set(x[:6], F(9), F(15))
    L = max((b - a for a, b in k6), default=F(0))
    r = L * x[6] / 2
    return dict(empty=False, R=R, opener=opener, r=r)

def work(item):
    tag, x, rng = item
    base = info(x)
    out = [('base', tag, base)]
    for y in range(1, 7):
        lo, hi = rng[y]
        for k in range(1, 9):
            v = F(lo).limit_denominator(10 ** 9) + (F(hi).limit_denominator(10 ** 9) - F(lo).limit_denominator(10 ** 9)) * F(k, 9)
            z = list(x); z[y] = v
            if sorted(z) != z or len(set(z)) < 7:
                continue
            i = info(z)
            if i is not None:
                out.append(('moved', (tag, y + 1, k), i))
    return out

if __name__ == '__main__':
    items = []
    for J, step in ((1, 1), (2, 10)):
        t = pickle.load(open('terminals7_J%d.pkl' % J, 'rb'))
        d = pickle.load(open('cell_members7_J%d.pkl' % J, 'rb'))
        for i, x in d[::step]:
            if clear_set(x, F(1), F(7)):
                continue
            k6 = clear_set(x[:6], F(9), F(15))
            if not k6:
                continue
            L = max(b - a for a, b in k6)
            if L * x[6] / 2 < 1:
                items.append(((J, i), x, [(float(a), float(b)) for a, b in t[i][3]]))
    with Pool(4) as pool:
        res = [r for rs in pool.map(work, items, chunksize=4) for r in rs]
    out = open('window_b_failures_v1.out', 'w'); out.write(__doc__ + "\n")
    base = [r for r in res if r[0] == 'base']; moved = [r for r in res if r[0] == 'moved']
    out.write("failures: %d (base members); moved crossers: %d\n" % (len(base), len(moved)))
    out.write("base: K'_7 empty: %d; opener rank counts: %s\n" % (sum(1 for r in base if r[2] and r[2]['empty']), dict(Counter(r[2]['opener'][0] if r[2]['opener'] else None for r in base if r[2] and not r[2]['empty']))))
    out.write("base: opener (rank, lap) counts: %s\n" % dict(Counter(r[2]['opener'] for r in base if r[2] and not r[2]['empty']).most_common(12)))
    out.write("moved: K'_7 empty: %d; opener rank counts: %s\n" % (sum(1 for r in moved if r[2]['empty']), dict(Counter(r[2]['opener'][0] if r[2]['opener'] else None for r in moved if not r[2]['empty']))))
    out.write("moved with floor r < 1: %d of %d\n" % (sum(1 for r in moved if not r[2]['empty'] and r[2]['r'] < 1), sum(1 for r in moved if not r[2]['empty'])))
    for r in moved:
        if r[2]['empty']:
            out.write("  MOVED K'_7 EMPTY: %s\n" % (r[1],))
    out.close(); print(open('window_b_failures_v1.out').read()[len(__doc__):])
