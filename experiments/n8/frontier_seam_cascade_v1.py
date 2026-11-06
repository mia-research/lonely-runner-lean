# E827: the six annealing candidates (carves of [1,7] with 31/r6 > 73/r7 and r7 > 511/31) pushed through the exact cascade of LonelyRunner/experiments/nN/redo/outcome_classes_v2.py (Fractions); and the least-precision rounding of each that still carves exactly and still has a seam violation.
import re, glob, os
from fractions import Fraction as F
RD = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/'
HERE = os.getcwd(); os.chdir(RD)
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
def carves(rs):
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
cands = []
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: cands.append([float(x) for x in l.strip('[]\n ').split(',')])
for v in cands:
    rh = [F(1)] + [F(x) for x in v]
    o = outcome(rh)
    print('candidate rho7 =', float(rh[-1]), '| cascade landing R =', float(o['R']), '| moves', o['nmoves'], '| window', int((o['R'] - 1) // 8), '| exact R =', o['R'])
    for k in range(1, 8):
        D = 10 ** k
        rr = [F(round(x * D), D) for x in v]
        if all(a < b for a, b in zip(rr, rr[1:])) and rr[0] >= 1 and F(47, 7) < rr[4] < 7 and rr[5] > 15 and carves(rr) and F(31) / rr[4] > F(73) / rr[5]:
            o2 = outcome([F(1)] + rr)
            print('   rounded to 1/%d: readings %s | exact carve | seam violated | cascade landing R = %s (%.6f), window %d, moves %d' % (D, [str(x) for x in rr], o2['R'], float(o2['R']), int((o2['R'] - 1) // 8), o2['nmoves']))
            break
