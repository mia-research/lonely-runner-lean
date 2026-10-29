# Exact cascade landing R* = 8 d_min T for generic random arrangements (rho_1 = 1, six log-uniform in [1, B], denominator 10^6), seeded.  Distribution of R*, and the maximum.
import math, random, sys, collections
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def casc(r):
    t = F(1, 8 * min(r)); mv = 0
    while True:
        way = [d for d in r if dist(d * t) < E]
        if not way: return t, mv
        t = max((F(round(d * t)) + E) / d for d in way); mv += 1
seed = int(sys.argv[1]); N = int(sys.argv[2]); B = int(sys.argv[3]); rnd = random.Random(seed)
H = collections.Counter(); mx = (F(0), None); mvs = collections.Counter(); n = 0
while n < N:
    r = sorted({F(1)} | {F(round(10 ** 6 * B ** rnd.random()), 10 ** 6) for _ in range(6)})
    if len(r) != 7: continue
    n += 1; t, mv = casc(r); R = 8 * t
    H[min(int(R), 12)] += 1; mvs[mv] += 1
    if R > mx[0]: mx = (R, [str(x) for x in r])
print('B', B, 'N', N, 'R* floor histogram (12 = 12 or more):', dict(sorted(H.items())))
print('moves', dict(sorted(mvs.items())))
print('max R*', float(mx[0]), mx[0], mx[1])
