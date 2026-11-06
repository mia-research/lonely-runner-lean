# E829: (a) the box-search control carves (rho7 in (23, 25)) re-tested exactly and run through the exact cascade; (b) the best near-carves above 25 (frontier_box_carve_v1_hi2_s*.out) and the first polished vector run through the exact cascade.
import glob, pickle, os, re, collections
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
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
for f in sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')): cands += pickle.load(open(f, 'rb'))
n = nc = 0; win = collections.Counter(); mx = F(0)
for v in cands:
    n += 1
    if not carves(v): continue
    nc += 1
    o = outcome([F(1)] + [F(x) for x in v]); win[int((o['R'] - 1) // 8)] += 1; mx = max(mx, o['R'])
print('(a) control candidates', n, 'exact carves', nc, '| cascade window of the landing:', sorted(win.items()), '| largest landing exact', mx, '< 26433/2209:', mx < F(26433, 2209))
for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
    m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    v = [float(x) for x in m.group(1).split(',')]
    o = outcome([F(1)] + [F(x) for x in v])
    print('(b)', f[-6:-4], 'rho7 in (73/2, 367/10):', F(73, 2) < F(v[5]) < F(367, 10), '| exact carve:', carves(v), '| cascade landing window', int((o['R'] - 1) // 8), 'exact R =', o['R'])
x = pickle.load(open('frontier_polish_v1_first.pkl', 'rb'))
o = outcome([F(1)] + [F(v) for v in x])
print('(b) polished first vector: exact carve:', carves(x), '| cascade landing window', int((o['R'] - 1) // 8), 'moves', o['nmoves'], 'exact R =', o['R'])
