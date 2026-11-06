# E827: search (floats steer only) for readings 1 <= r2 <= r3 <= r4 <= r5 <= r6 < r7 with 47/7 < r6 < 7, 15 < r7 that carve [1,7] (open zones (8j-1, 8j+1)/r, strict overlap) while 31/r6 > 73/r7 (seam violated).  Simulated annealing on (uncovered length + seam penalty); seeded.  usage: seed restarts steps
import sys, random, math
random.seed(int(sys.argv[1]))
def uncovered(rs):
    iv = []
    for r in rs:
        j = 1
        while (8 * j - 1) / r < 7:
            a, b = (8 * j - 1) / r, (8 * j + 1) / r
            if b > 1: iv.append((max(a, 1.0), min(b, 7.0)))
            j += 1
    iv.sort(); cur = 1.0; gap = 0.0
    # R = 1 must lie strictly inside a zone: treat zones as open, so require a zone with a < 1 < b
    if not any((8 * j - 1) / r < 1 < (8 * j + 1) / r for r in rs for j in range(1, int(r / 8) + 3)): gap += 1e-3
    for a, b in iv:
        if a > cur: gap += a - cur
        if b > cur: cur = b
    if cur < 7: gap += 7 - cur
    return gap
def objective(x):
    r2, r3, r4, r5, r6, r7 = x
    pen = 0.0
    margin = 31 / r6 - 73 / r7
    if margin < 5e-3: pen = (5e-3 - margin) * 5
    return uncovered(sorted(x[:4]) + [r6, r7]) + pen
def clamp(x):
    r2, r3, r4, r5, r6, r7 = x
    r6 = min(max(r6, 47 / 7 + 1e-9), 7 - 1e-9); r7 = max(r7, 15 + 1e-9)
    mid = sorted(min(max(v, 1.0), r6) for v in x[:4])
    return mid + [r6, r7]
best_overall = (1e9, None); found = []
for rest in range(int(sys.argv[2])):
    r6 = random.uniform(47 / 7, 7)
    x = clamp([random.uniform(1, r6) for _ in range(4)] + [r6, random.uniform(15, 40)])
    f = objective(x); T = 0.05; step = 0.3
    for it in range(int(sys.argv[3])):
        y = clamp([v + random.gauss(0, step) * (1 if random.random() < 0.5 else 0.1) if random.random() < 0.5 else v for v in x])
        fy = objective(y)
        if fy < f or random.random() < math.exp(-(fy - f) / max(T, 1e-9)): x, f = y, fy
        T *= 0.9993; step = max(step * 0.9995, 1e-4)
        if f < best_overall[0]: best_overall = (f, list(x))
        if f <= 1e-12:
            found.append(list(x)); break
print('restarts', sys.argv[2], 'steps each', sys.argv[3], 'best objective', best_overall[0], 'readings', best_overall[1])
print('candidates with objective 0 (a carve with the seam violated by at least 5e-3 on floats):', len(found))
for c in found[:5]: print(c)
