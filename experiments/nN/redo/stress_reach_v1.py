# stress_reach_v1.py -- how far up can rho_7 (or rho_6) go while the gate is crossed (exact landing > 9)?  Walk with exact acceptance;
# objective = the chosen reading (floats steer acceptance only); constraint = gate crossed (exact).  Every visited arrangement goes through check().
# usage: python3 stress_reach_v1.py SECONDS SEED IDX(6|5)
import sys, math, pickle; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
from collections import Counter, defaultdict
T0 = time.time(); LIM = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2])); IDX = int(sys.argv[3])
seeds = pickle.load(open('stress_seeds_v1.pkl', 'rb')); S = sorted(seeds, key=lambda r: -r[IDX])[:300]
def eps(): return F(1, 10 ** rnd.randint(2, 12))
def lim(x): return x.limit_denominator(10 ** 13)
def propose(r, steps):
    r = list(r); t = rnd.random(); y = rnd.randrange(1, 7)
    if t < 0.3: r[y] = lim(r[y] * (1 + rnd.choice((-1, 1)) * F(1, 10 ** rnd.randint(1, 9))))
    elif t < 0.4: r[IDX] = lim(r[IDX] * (1 + F(1, 10 ** rnd.randint(1, 4))))
    elif t < 0.5: r[y] = lim(r[y] + F(rnd.randint(-100, 100), 1000))
    elif steps:
        s = rnd.choice(steps); pt = Fr(rnd.choice((s[0], s[3])))
        i = max(1, round((pt * r[y] + rnd.choice((-1, 1))) / 8)); r[y] = (8 * i + rnd.choice((-1, 1))) / pt * (1 + rnd.choice((-1, 0, 0, 1)) * eps())
    return sorted(r)
stats = Counter(); examples = defaultdict(list); N = 0; mism = 0
best = max(S, key=lambda r: r[IDX]); bestv = best[IDX]; cur = list(best); curs = fpath([Q(x) for x in cur])[0]; hist = Counter()
while time.time() - T0 < LIM:
    if rnd.random() < 0.001: cur = list(rnd.choice(S)); curs = fpath([Q(x) for x in cur])[0]
    r = propose(cur, curs)
    if r[0] != 1 or len(set(r)) != 7 or r[1] <= 1: continue
    rh = [Q(x) for x in r]; N += 1
    cl, R, v, o = check(rh); stats[cl] += 1
    for s in v:
        key = s.split(':')[0].split('_step')[0]; stats['VIOL ' + key] += 1
        if len(examples[key]) < 3: examples[key].append(r)
    if N % 40 == 0:
        oo = OFFICIAL_outcome(r)
        if oo['R'] != Fr(R) or oo['opener'] != o['opener']: mism += 1
    if R > 9:
        hist['gate'] += 1
        if r[IDX] >= cur[IDX] or rnd.random() < 0.02:
            cur = r; curs = o['steps']
        if r[IDX] > bestv: best, bestv = r, r[IDX]
        if Fr(R) > F(26433, 2209): examples['ABOVE'].append(r)
print('args', sys.argv[1:], 'evaluated', N, 'mismatch', mism, 'gate-crossed visits', hist['gate'])
print('classes', dict(sorted(stats.items())))
print('start max reading idx', float(max(S, key=lambda r: r[IDX])[IDX]), ' reached max (gate crossed)', bestv, float(bestv))
print('arrangement', [str(x) for x in best]); print('landing', float(Fr(fpath([Q(x) for x in best])[1])))
for k, ex in examples.items():
    for e in ex[:3]: print('EXAMPLE', k, [str(x) for x in e])
