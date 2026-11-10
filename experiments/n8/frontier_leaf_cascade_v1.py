# E832: the exact cascade (outcome_classes_v2.py, Fractions) on the centre of every uncertified leaf at D = 64 (frontier_box_dfs_v1_leaves64_*.txt): the window of the landing and the exact carve test.
import glob, os, collections
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
def carves(rs):
    iv = []
    for r in rs:
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
win = collections.Counter(); nc = 0; n = 0; mx = F(0)
for f in sorted(glob.glob('frontier_box_dfs_v1_leaves64_*.txt')):
    for l in open(f):
        v = [int(x) for x in l.split()]
        if not v: continue
        D, nb = v[0], v[1:]
        x = sorted((F(2 * a + 1, 2 * D)) for a in nb)
        o = outcome([F(1)] + x); win[int((o['R'] - 1) // 8)] += 1; mx = max(mx, o['R']); n += 1
        if carves(x): nc += 1
print('leaf centres', n, '| cascade landing window counts:', sorted(win.items()), '| exact carves among centres:', nc, '| largest landing R (exact):', mx)
