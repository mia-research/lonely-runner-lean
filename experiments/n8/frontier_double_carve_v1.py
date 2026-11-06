# E827: search (floats steer only) for readings 1 < r2 <= ... <= r7 with r7 > 17 that carve BOTH [1,7] and [9,15] (open zones (8j-1, 8j+1)/r, reading 1 covers neither): a landing at R >= 17.  Simulated annealing on the total uncovered length; seeded.  usage: seed restarts steps
import sys, random, math
random.seed(int(sys.argv[1]))
def unc(rs, lo, hi):
    iv = []
    for r in rs:
        j = 1
        while (8 * j - 1) / r < hi:
            a, b = (8 * j - 1) / r, (8 * j + 1) / r
            if b > lo: iv.append((max(a, lo), min(b, hi)))
            j += 1
    iv.sort(); cur = lo; gap = 0.0
    for a, b in iv:
        if a > cur: gap += a - cur
        if b > cur: cur = b
    if cur < hi: gap += hi - cur
    return gap
def obj(x):
    xs = sorted(x)
    return unc(xs, 1.0, 7.0) + unc(xs, 9.0, 15.0)
def clamp(x):
    x = sorted(min(max(v, 1.0000001), 80.0) for v in x)
    x[-1] = max(x[-1], 17.0000001)
    return sorted(x)
best = (1e9, None); found = []
for rest in range(int(sys.argv[2])):
    x = clamp([random.uniform(1, 8) for _ in range(5)] + [random.uniform(17, 40)])
    f = obj(x); T = 0.05; step = 0.4
    for it in range(int(sys.argv[3])):
        y = clamp([v + random.gauss(0, step) if random.random() < 0.4 else v for v in x])
        fy = obj(y)
        if fy < f or random.random() < math.exp(-(fy - f) / max(T, 1e-9)): x, f = y, fy
        T *= 0.9993; step = max(step * 0.9995, 1e-4)
        if f < best[0]: best = (f, list(x))
        if f <= 1e-12: found.append(list(x)); break
print('restarts', sys.argv[2], 'steps', sys.argv[3], 'best total uncovered length', best[0], 'readings', best[1])
print('candidates carving both windows:', len(found))
for c in found[:5]: print(c)
