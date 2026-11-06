# E829: carves of [1,7] with r7 in (lo7, hi7) and the middle readings in the bounded box E387 records for crossers (r2 in [2.1,4.9], r3 in [2.8,5.4], r4 in [3.7,6.3], r5 in [4.2,7.2], r6 in [5.4,8.2], each sorted); seeded annealing on the uncovered length of [1,7] (floats steer).  usage: lo7 hi7 seed restarts steps
import sys, random, math, pickle
lo7, hi7 = float(sys.argv[1]), float(sys.argv[2]); random.seed(int(sys.argv[3]))
BOX = [(2.1, 4.9), (2.8, 5.4), (3.7, 6.3), (4.2, 7.2), (5.4, 8.2)]
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
def clamp(x):
    mid = sorted(min(max(v, lo), hi) for v, (lo, hi) in zip(x[:5], BOX))
    mid = [min(max(v, lo), hi) for v, (lo, hi) in zip(mid, BOX)]
    return mid + [min(max(x[5], lo7), hi7)]
found = []; best = 1e9; bestx = None
for rest in range(int(sys.argv[4])):
    x = clamp([random.uniform(lo, hi) for lo, hi in BOX] + [random.uniform(lo7, hi7)])
    f = unc(x); T = 0.05; step = 0.3
    for it in range(int(sys.argv[5])):
        y = clamp([v + random.gauss(0, step) if random.random() < 0.4 else v for v in x])
        fy = unc(y)
        if fy < f or random.random() < math.exp(-(fy - f) / max(T, 1e-9)): x, f = y, fy
        T *= 0.9993; step = max(step * 0.9995, 1e-4)
        if f < best: best = f; bestx = list(x)
        if f <= 1e-12: found.append(list(x)); break
pickle.dump(found, open('frontier_box_carve_v1_%s_%s_s%s.pkl' % (sys.argv[1], sys.argv[2], sys.argv[3]), 'wb'))
print('best near-carve readings (float):', bestx)
print('r7 in', (lo7, hi7), 'restarts', sys.argv[4], 'carves found (float):', len(found), 'least uncovered (float):', best, 'rho7 of carves:', sorted(round(f[5], 3) for f in found)[:12])
