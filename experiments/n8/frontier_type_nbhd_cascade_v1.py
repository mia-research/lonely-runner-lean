# E831: cascade test of the neighbourhood scan: the same kind of perturbed vectors (6,000 per group, random relative size 1e-3 to 0.1 of a start vector, seeded) run through the exact cascade (outcome_classes_v2.py, Fractions): the window of the landing, and the exact carve test.  usage: group seed N
import sys, glob, re, pickle, random, os, collections
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
def carves_exact(x):
    iv = []
    for r in x:
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
group = sys.argv[1]; random.seed(int(sys.argv[2])); N = int(sys.argv[3])
starts = []
if group == 'lap3':
    for f in sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')): starts += pickle.load(open(f, 'rb'))[:6]
else:
    for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
        m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline()); starts.append([float(v) for v in m.group(1).split(',')])
    starts.append(pickle.load(open('frontier_polish_v1_first.pkl', 'rb')))
win = collections.Counter(); carve = 0; mx = F(0)
for it in range(N):
    x0 = random.choice(starts); scale = random.choice([1e-3, 1e-2, 5e-2, 0.1])
    x = sorted(max(1.0001, v * (1 + scale * random.uniform(-1, 1))) for v in x0)
    o = outcome([F(1)] + [F(v) for v in x]); win[int((o['R'] - 1) // 8)] += 1; mx = max(mx, o['R'])
    if carves_exact(x): carve += 1
print(group, '| perturbed vectors', N, '| cascade landing window counts:', sorted(win.items()), '| exact carves:', carve, '| largest landing R exact:', mx)
