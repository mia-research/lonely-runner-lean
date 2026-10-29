# Same greedy cover, on GENERIC random arrangements (seeded): rho_1 = 1, six more log-uniform in [1, 50] with denominator 10^6 (readings are not commensurable in practice).  Exact Fractions.
import math, random, sys
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
rnd = random.Random(int(sys.argv[1])); N = int(sys.argv[2])
arrs = []
while len(arrs) < N:
    r = sorted({F(1)} | {F(round(10 ** 6 * 50 ** rnd.random()), 10 ** 6) for _ in range(6)})
    if len(r) == 7: arrs.append(r)
cands = sorted({F(8 * a, b) for b in range(2, 13) for a in range(1, 8 * 60 * b // 8 + 1) if F(8 * a, b) <= 60})
cov = {R: {i for i, r in enumerate(arrs) if all(dist(d * R / 8) >= E for d in r)} for R in cands}
left = set(range(N)); cum = 0
for step in range(30):
    best = max(cands, key=lambda R: len(cov[R] & left)); gain = len(cov[best] & left)
    if gain == 0: break
    left -= cov[best]; cum = N - len(left)
    print(step + 1, 'R =', best, 'gain', gain, 'covered', cum, 'of', N)
