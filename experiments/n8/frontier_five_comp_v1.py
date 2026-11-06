# E829: for five sorted readings r2..r6 >= 1, C5 = the points of [1,7] in no open zone (8j-1, 8j+1)/r.  A reading r7 can carve [1,7] with them only if every component of C5 is shorter than 2/r7 (an interval longer than the blocked length 2/r7 contains a clear point of r7).  Here: the least possible longest component m of a nonempty C5 (floats steer), and whether five readings can leave C5 empty.  Seeded annealing.  usage: seed restarts steps
import sys, random, math
random.seed(int(sys.argv[1]))
def gaps(rs):
    iv = []
    for r in rs:
        j = 1
        while (8 * j - 1) / r < 7:
            a, b = (8 * j - 1) / r, (8 * j + 1) / r
            if b > 1: iv.append((a, b))
            j += 1
    iv.sort(); cur = 1.0; out = []
    # points of [1,7] not in any open zone: closed gaps [cur, a]
    started = False
    for a, b in iv:
        if a >= cur and a - cur >= 0 and a > cur - 1e-15:
            if a >= cur: out.append((cur, min(a, 7.0)))
        if b > cur: cur = b
        if cur >= 7: break
    if cur < 7: out.append((cur, 7.0))
    return [(x, y) for x, y in out if y >= x and x <= 7]
def lon(rs):
    g = gaps(rs)
    if not g: return None, g
    return max(y - x for x, y in g), g
best = (1e9, None); empty = 0
for rest in range(int(sys.argv[2])):
    x = sorted(random.uniform(1, 30) for _ in range(5)); f, _ = lon(x)
    if f is None: empty += 1; continue
    T = 0.02; step = 0.5
    for it in range(int(sys.argv[3])):
        y = sorted(max(1.0, v + random.gauss(0, step)) if random.random() < 0.4 else v for v in x)
        fy, gy = lon(y)
        if fy is None: empty += 1; continue
        if fy < f or random.random() < math.exp(-(fy - f) / max(T, 1e-9)): x, f = y, fy
        T *= 0.9993; step = max(step * 0.9996, 1e-4)
        if f < best[0]: best = (f, list(x))
print('restarts', sys.argv[2], 'steps', sys.argv[3], '| five-reading sets with C5 empty found:', empty)
print('least longest-component m of a nonempty C5 (float):', best[0], ' 2/m =', 2 / best[0] if best[0] else None)
print('readings', best[1])
