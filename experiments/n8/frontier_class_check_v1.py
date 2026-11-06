# E828: the carves found by the band searches (laps 2, 3 and the free search) and the six of E827, classified by E802's label (opener rank, window) through the exact cascade, and compared with the record's supremum 26433/2209 of the landing (E319, E349).
import glob, pickle, os, collections
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
SUP = F(26433, 2209)
cands = []
for f in sorted(glob.glob('frontier_band_carve_v1_k*_s*.pkl')):
    for v in pickle.load(open(f, 'rb')): cands.append((f, v))
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: cands.append((f, [float(x) for x in l.strip('[]\n ').split(',')]))
lab = collections.Counter(); n = nc = nover = 0; mx = F(0); bands = collections.Counter()
for f, v in cands:
    n += 1
    if not carves(v): continue
    nc += 1
    o = outcome([F(1)] + [F(x) for x in v])
    window = int((o['R'] - 1) // 8)
    lab[(o['opener'][0], window)] += 1
    mx = max(mx, o['R'])
    if o['R'] > SUP: nover += 1
    bands[int(round(v[5] / 8))] += 1
print('candidates', n, 'exact carves', nc, '| strip lap of r7 (round(r7/8)):', sorted(bands.items()))
print('labels (opener rank, window) of the exact carves:', sorted(lab.items()))
print('largest landing R among them:', float(mx), 'exact', mx, '| landings above the record supremum 26433/2209:', nover)
