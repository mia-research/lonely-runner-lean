# E828: carves of [1,7] by six sorted readings with r7 in the strip band (8k-1, 8k+1) of lap k (the R = 1 coverer), r2..r6 free in [1, r7]: seeded annealing on the uncovered length of [1,7] (floats steer); found candidates are saved for the exact checks.  usage: k seed restarts steps
import sys, random, math, pickle
k = int(sys.argv[1]); random.seed(int(sys.argv[2]))
lo7, hi7 = (17.0, 80.0) if k == 0 else (8 * k - 1, 8 * k + 1)
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
    r7 = min(max(x[5], lo7 + 1e-9), hi7 - 1e-9)
    mid = sorted(min(max(v, 1.0 + 1e-9), r7) for v in x[:5])
    return mid + [r7]
found = []; best = 1e9; bestx = None
for rest in range(int(sys.argv[3])):
    x = clamp([random.uniform(1, 8) for _ in range(5)] + [random.uniform(lo7, hi7)])
    f = unc(x); T = 0.05; step = 0.4
    for it in range(int(sys.argv[4])):
        y = clamp([v + random.gauss(0, step) if random.random() < 0.4 else v for v in x])
        fy = unc(y)
        if fy < f or random.random() < math.exp(-(fy - f) / max(T, 1e-9)): x, f = y, fy
        T *= 0.9993; step = max(step * 0.9995, 1e-4)
        if f < best: best = f; bestx = list(x)
        if f <= 1e-12: found.append(list(x)); break
pickle.dump(found, open('frontier_band_carve_v1_k%d_s%s.pkl' % (k, sys.argv[2]), 'wb'))
pickle.dump((best, bestx), open('frontier_band_best_v1_k%d_s%s.pkl' % (k, sys.argv[2]), 'wb'))
print('carve rho7 values:', sorted(round(f[5], 3) for f in found))
print('lap k =', k, 'band', (lo7, hi7), 'restarts', sys.argv[3], 'steps', sys.argv[4], 'carves found (float):', len(found), 'least uncovered length (float):', best)
