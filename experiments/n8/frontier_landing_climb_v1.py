# E827: hill-climb on the exact cascade landing R itself (Fractions, outcome_classes_v2.py) over arrangements (1, r2..r7) with r7 > 17: seeds = the six carve candidates and random arrangements; the largest landing found.  Seeded.  usage: seed restarts steps
import sys, random, os, glob, re
from fractions import Fraction as F
HERE = os.getcwd(); os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE)
random.seed(int(sys.argv[1]))
def land(v):
    try: return outcome([F(1)] + [F(x).limit_denominator(10**6) for x in v])['R']
    except Exception: return F(0)
seeds = []
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: seeds.append([float(x) for x in l.strip('[]\n ').split(',')])
best = (F(0), None); nland = 0; over = []
for rest in range(int(sys.argv[2])):
    if rest < len(seeds) and sys.argv[1] == '1': x = list(seeds[rest])
    else: x = sorted([random.uniform(1, 8) for _ in range(5)] + [random.uniform(17.01, 40)])
    cur = land(x)
    for it in range(int(sys.argv[3])):
        y = sorted(max(1.0001, v + random.gauss(0, random.choice([0.3, 0.03, 0.003]))) if random.random() < 0.4 else v for v in x)
        y[-1] = max(y[-1], 17.001)
        if len(set(y)) < 6: continue
        ly = land(y); nland += 1
        if ly >= cur: x, cur = y, ly
        if cur > best[0]: best = (cur, list(x))
        if cur >= 17: over.append(list(x)); break
    if cur >= 17: break
print('evaluations', nland, 'largest landing R found', float(best[0]), 'exact', best[0], 'readings', best[1])
print('arrangements with landing >= 17:', len(over))
for o in over[:3]: print(o)
