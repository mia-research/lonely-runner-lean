# E829: polish the near-carves above 25 (best readings printed by frontier_box_carve_v1.py) by a fine local search on the float uncovered length (steps from 1e-3 down to 1e-12); an exact carve candidate is re-tested with Fractions (strict overlap of open zones) and pushed through the exact cascade.
import re, glob, random, os
from fractions import Fraction as F
random.seed(7)
def unc(rs):
    iv = []
    for r in rs:
        j = 1
        while (8 * j - 1) / r < 7:
            a, b = (8 * j - 1) / r, (8 * j + 1) / r
            if b > 1: iv.append((max(a, 1.0), min(b, 7.0)))
            j += 1
    iv.sort(); cur = 1.0; gap = 0.0
    if not any((8 * j - 1) / r < 1 < (8 * j + 1) / r for r in rs for j in range(1, int(r / 8) + 3)): gap += 1e-3
    for a, b in iv:
        if a > cur: gap += a - cur
        if b > cur: cur = b
    if cur < 7: gap += 7 - cur
    return gap
def carves_exact(rs):
    iv = []
    for r in rs:
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    if not any(a < 1 < b for a, b in iv): return False
    cur = max(b for a, b in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return False
        cur = max(nxt)
    return True
starts = []
for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
    m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    starts.append([float(x) for x in m.group(1).split(',')])
os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir('/Users/trentpalelei/Desktop/Math Ex/experiments/n8')
for x0 in starts:
    x = sorted(x0); f = unc(x); step = 1e-3
    for it in range(200000):
        y = sorted(max(1.0001, v + random.gauss(0, step)) if random.random() < 0.5 else v for v in x)
        fy = unc(y)
        if fy <= f: x, f = y, fy
        if it % 4000 == 3999: step = max(step * 0.5, 1e-12)
        if f <= 0: break
    ok = f <= 0 and carves_exact(x)
    line = 'start r7 = %.4f -> polished uncovered length (float) %.3e | r6 = %.9f r7 = %.6f | exact carve: %s' % (x0[5], f, x[4], x[5], ok)
    if ok:
        o = outcome([F(1)] + [F(v) for v in x])
        line += ' | cascade landing R = %s (%.5f), window %d, moves %d' % (o['R'], float(o['R']), int((o['R'] - 1) // 8), o['nmoves'])
        print('READINGS', [repr(v) for v in x])
    print(line, flush=True)
