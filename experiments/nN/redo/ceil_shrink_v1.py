# Does the clear set K6 of six readings on [1,7] ever have all components degenerate (finite point set) or empty?
# Floats steer (Metropolis on the total length of K6 components); the best arrangements are then examined exactly (Fractions).
import sys, time, random, math
from fractions import Fraction as F
from ceil_climb_v1 import fcomps
from ceil_k6_lib_v1 import clear_components
LIM = float(sys.argv[1]); seed = int(sys.argv[2]); RMAX = float(sys.argv[3]); T0 = time.time(); rnd = random.Random(seed)
def tot(six): c = fcomps(six, 7.0); return sum(b - a for a, b in c), c
results = []; nev = 0
while time.time() - T0 < LIM:
    six = [1.0] + sorted(math.exp(rnd.uniform(math.log(1.05), math.log(RMAX))) for _ in range(5))
    cur, _ = tot(six); T = 0.3
    for it in range(40000):
        if time.time() - T0 > LIM: break
        y = list(six)
        for i in rnd.sample(range(1, 6), rnd.choice([1, 1, 2])):
            y[i] *= 1 + rnd.choice([-1, 1]) * 10 ** (-rnd.uniform(1, 6))
        if not all(y[i] < y[i+1] for i in range(5)) or y[1] <= 1.0: continue
        nev += 1; v, _ = tot(y)
        if v <= cur or rnd.random() < math.exp(-(v - cur) / T): six, cur = y, v
        T = max(1e-4, T * 0.9998)
    v, c = tot(six); results.append((v, len(c), six))
results.sort(key=lambda t: t[0])
print('restarts', len(results), 'evals', nev)
for v, n, six in results[:6]:
    x = [F(t).limit_denominator(10**12) for t in six]
    ce = clear_components(x, F(7))
    print('float total %.6f comps %d rho6 %.4f | exact (rationalised 1e-12): comps %d total %.6f' % (v, n, six[-1], len(ce), float(sum(b - a for a, b in ce))), [round(t, 5) for t in six])
print('smallest float total', results[0][0], ' number of restarts with total < 0.05:', sum(1 for r in results if r[0] < 0.05), ' with zero comps:', sum(1 for r in results if r[1] == 0))
