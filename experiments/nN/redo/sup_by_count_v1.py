# largest landing of the cascade for k readings (reading 1 = 1 plus k-1 others): exact hill-climb on rationals with denominator 10^4
import sys, random
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
k = int(sys.argv[1]); rnd = random.Random(int(sys.argv[2])); RMAX = F(int(sys.argv[3]))
def q(x): return F(round(x * 10**4), 10**4)
def land(xs):
    rho = [F(1)] + sorted(xs)
    if len(set(rho)) < k or rho[1] <= 1: return F(-1)
    return outcome(rho)['R']
best = F(0); bx = None
for restart in range(int(sys.argv[4])):
    xs = [q(rnd.uniform(1.05, float(RMAX))) for _ in range(k - 1)]; cur = land(xs)
    for it in range(1500):
        ys = list(xs); i = rnd.randrange(k - 1); sc = rnd.choice((0.001, 0.01, 0.1, 0.5, 2.0))
        ys[i] = max(F(105, 100), min(RMAX, q(float(ys[i]) + rnd.uniform(-sc, sc))))
        v = land(ys)
        if v >= cur: xs, cur = ys, v
    if cur > best: best, bx = cur, sorted(xs)
print(f"k={k} readings: best landing {float(best):.5f} (= {best}) at 1, " + ", ".join(str(x) for x in bx))
