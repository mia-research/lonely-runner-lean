# annealing on six readings maximising sup of the allowed rho_7 set (floats steer); aimed moves put an entry/exit of reading i on an edge of a K6 component or on 1, 7, 9.
import sys, time, random, math, pickle
from ceil_climb_v1 import fcomps, fallowed
LIM = float(sys.argv[1]); seed = int(sys.argv[2]); cap = float(sys.argv[3]); T0 = time.time(); rnd = random.Random(seed)
starts = pickle.load(open('ceil_starts2_v1.pkl', 'rb'))
best = (0, None); nev = 0; runs = 0
def aimed(y):
    i = rnd.randrange(1, 6); comps = fcomps(y, 7.0)
    pts = [1.0, 7.0] + [e for c in comps for e in c]
    p = rnd.choice(pts); j = max(1, round(y[i] * p / 8 + rnd.choice([-1, 0, 1])))
    s = rnd.choice([-1, 1]); z = (8 * j + s) / p
    z *= 1 + rnd.choice([-1, 1, 0]) * 10 ** (-rnd.uniform(6, 13))
    y = list(y); y[i] = z; return y
while time.time() - T0 < LIM:
    six = list(rnd.choice(starts)); c, v = fallowed(six, cap)
    if v is None: continue
    cur = (v, six); runs += 1; bestrun = cur; T = 1.0
    for it in range(60000):
        if time.time() - T0 > LIM: break
        if rnd.random() < 0.3: y = aimed(cur[1])
        else:
            y = list(cur[1])
            for i in rnd.sample(range(1, 6), rnd.choice([1, 1, 2, 3])): y[i] *= 1 + rnd.choice([-1, 1]) * 10 ** (-rnd.uniform(1.3, 11))
        if not all(y[i] < y[i+1] for i in range(5)) or y[0] != 1.0 or y[1] <= 1.0: continue
        nev += 1; c2, v2 = fallowed(y, cap)
        if v2 is None: continue
        if v2 >= cur[0] or rnd.random() < math.exp((v2 - cur[0]) / T): cur = (v2, y)
        if cur[0] > bestrun[0]: bestrun = cur
        T = max(0.003, T * 0.9999)
    if bestrun[0] > best[0]: best = bestrun
    print('run', runs, 'best in run %.9f' % bestrun[0], 'rho6 %.9f' % bestrun[1][-1], 'evals', nev, flush=True)
print('best float sup', best[0], [repr(t) for t in best[1]])
pickle.dump(best, open('ceil_anneal_best_%d_v1.pkl' % seed, 'wb'))
