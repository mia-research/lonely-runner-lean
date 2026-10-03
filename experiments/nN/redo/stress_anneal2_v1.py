# stress_anneal2_v1.py (seeded from the exact gate-crossing seeds with landing >= 11; denominators of non-aimed moves limited to 1e13)
# (derived from stress_anneal_v1.py) -- exact-evaluation annealing of the landing R* under constraints on the top readings.
# Floats steer only (acceptance probability); every arrangement is an exact Fraction set evaluated by check() (G, C, S, class list).
# usage: python3 stress_anneal_v1.py SECONDS SEED RHO6_MIN RHO7_MIN RHO7_MAX START(x0|rand|pull)
import sys, math; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
import pickle
from collections import Counter, defaultdict
T0 = time.time(); LIM = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2]))
M6, M7, X7, START = F(sys.argv[3]), F(sys.argv[4]), F(sys.argv[5]), sys.argv[6]
(x0,) = pickle.load(open('b12_A_x0_v1.pkl', 'rb')); X0 = [F(x) for x in x0]
SEEDS = pickle.load(open('stress_seeds_v1.pkl', 'rb')); HI = [k for k, v in SEEDS.items() if v[1] >= 10.8]
lim = lambda x: x.limit_denominator(10 ** 13)
def eps(): return F(1, 10 ** rnd.randint(1, 12))
def ok(r):
    r = sorted(r)
    return r[0] == 1 and len(set(r)) == 7 and r[5] >= M6 and r[6] >= M7 and r[6] <= X7
def rand_top(lo, hi):
    k = int(rnd.uniform(float(lo) / 8, float(hi) / 8)) + 1
    return F(8 * k) + rnd.choice((F(0), F(1), F(-1), 1 - eps(), -1 + eps(), 1 + eps(), -1 - eps(), eps(), -eps(), F(rnd.randint(-120, 120), 100)))
def start():
    if START == 'seeds': return sorted(rnd.choice(HI))
    if START == 'x0' or (START == 'pull' and rnd.random() < .5):
        r = list(X0)
        r[5] = rand_top(M6, max(M6 + 1, min(X7, M6 * 2))); r[6] = rand_top(M7, min(X7, max(M7 * 1.5, M7 + 8)))
    else:
        r = [F(1)] + [F(rnd.randint(110, 1200), 100) for _ in range(4)] + [rand_top(M6, max(M6 + 1, min(X7, M6 * 2))), rand_top(M7, min(X7, max(M7 * 1.5, M7 + 8)))]
    return sorted(r)
def propose(r, steps):
    r = list(r); t = rnd.random(); y = rnd.randrange(1, 7)
    if t < 0.35: r[y] = lim(r[y] * (1 + rnd.choice((-1, 1)) * F(1, 10 ** rnd.randint(1, 9))))
    elif t < 0.45: r[y] = lim(r[y] + F(rnd.randint(-100, 100), 100) * rnd.choice((F(1), F(1, 10), F(1, 100))))
    elif t < 0.85 and steps:
        s = rnd.choice(steps); R2 = Fr(s[3]); Rk = Fr(s[0])
        i = max(1, round((R2 * r[y] + 1) / 8)); mode = rnd.randrange(4)
        if mode == 0: r[y] = (8 * i - 1) / R2 * (1 + rnd.choice((-1, 0, 1)) * eps())      # entry at the exit
        elif mode == 1: r[y] = (8 * i + 1) / R2 * (1 + rnd.choice((-1, 0, 1)) * eps())    # exit at the exit
        elif mode == 2:
            i = max(1, round((Rk * r[y] + 1) / 8)); r[y] = (8 * i + 1) / Rk * (1 + rnd.choice((-1, 0, 1)) * eps())
        else:
            i = max(1, round((Rk * r[y] - 1) / 8) + 1); r[y] = (8 * i - 1) / Rk * (1 + rnd.choice((-1, 0, 1)) * eps())
    else:
        r[y] = rand_top(M6, M7 * 2) if y >= 5 else F(rnd.randint(110, 1300), 100)
    return sorted(r)
stats = Counter(); examples = defaultdict(list); best = (F(0), None); N = 0; mism = 0; hist = Counter(); bestgate = (F(0), None)
cur = None
while time.time() - T0 < LIM:
    if cur is None or rnd.random() < 0.0005:
        r = start()
        if not ok(r): continue
        rh = [Q(x) for x in r]; cl, R, v, o = check(rh); cur = (r, float(R), o['steps'])
    r = propose(cur[0], cur[2])
    if not ok(r): continue
    rh = [Q(x) for x in r]; N += 1
    cl, R, v, o = check(rh); stats[cl] += 1; Rf = float(R)
    if R > 9: hist['landing>9'] += 1
    if Fr(R) > best[0]: best = (Fr(R), r)
    if N % 50 == 0:
        oo = OFFICIAL_outcome(r)
        if oo['R'] != Fr(R) or oo['opener'] != o['opener'] or oo['closer'] != o['closer']: mism += 1
    for s in v:
        key = s.split(':')[0].split('_step')[0]; stats['VIOL ' + key] += 1
        if len(examples[key]) < 3: examples[key].append(r)
    temp = 0.03
    if Rf >= cur[1] or rnd.random() < math.exp((Rf - cur[1]) / temp): cur = (r, Rf, o['steps'])
print('args', sys.argv[1:]); print('evaluated', N, 'seconds', round(time.time() - T0), 'mismatch', mism)
print('classes', dict(sorted(stats.items()))); print('hist', dict(hist))
print('best landing', best[0], float(best[0]), [str(x) for x in best[1]])
for k, ex in examples.items():
    for e in ex: print('EXAMPLE', k, [str(x) for x in e])
