# Random exact test of Claim L2: for rates r1 != r2 in (0,1) and any offset u0, some k in N has both dist(r_j (u0+k)) >= 1/8.  Seeded; exact Fractions.
import math, random, sys
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
rnd = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); KMAX = int(sys.argv[3])
fails = []; worst = (0, None)
for _ in range(N):
    q = rnd.choice([2,3,4,5,6,7,8,12,16,24,48,97,1000])
    r1 = F(rnd.randint(1, q - 1), q) if rnd.random() < 0.7 else F(rnd.randint(1, 999), 1000)
    r2 = F(rnd.randint(1, 999), 1000) if rnd.random() < 0.5 else F(rnd.randint(1, 96), 97)
    if r1 == r2: continue
    u0 = F(rnd.randint(0, 10**6), rnd.choice([7, 8, 1000, 10**6]))
    k = 0
    while k <= KMAX and not (dist(r1 * (u0 + k)) >= E and dist(r2 * (u0 + k)) >= E): k += 1
    if k > KMAX: fails.append((str(r1), str(r2), str(u0)))
    else:
        m = min(r1, 1 - r1, r2, 1 - r2)
        if k * m > worst[0]: worst = (k * m, (str(r1), str(r2), str(u0), k))
print('samples', N, 'failures', len(fails), fails[:6]); print('max k*min-rate-dist', float(worst[0]), worst[1])
