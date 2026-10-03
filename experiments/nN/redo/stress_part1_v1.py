# stress_part1_v1.py -- claims G, C, S and class list on constructed arrangements with rho_6, rho_7 far above the tree window.
# usage: python3 stress_part1_v1.py SECONDS SEED
import sys; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
import pickle
from collections import Counter, defaultdict
T0 = time.time(); LIM = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2]))
(x0,) = pickle.load(open('b12_A_x0_v1.pkl', 'rb'))
X0 = [F(x) for x in x0]
def eps(): return F(1, 10 ** rnd.randint(1, 12))
def q(x, den=10**6): return F(round(x * den), den)
def low_set():
    t = rnd.random()
    if t < 0.25: return [X0[i] * (1 + rnd.choice((-1, 1)) * eps() * rnd.choice((0, 1, 1))) for i in range(1, 5)]
    if t < 0.40: return [F(x) for x in rnd.sample(range(2, 13), 4)]
    if t < 0.55: return [F(a) + rnd.choice((-1, 1)) * (1 - eps()) for a in rnd.sample((8, 16), 1)] + [q(rnd.uniform(1.2, 6.8)) for _ in range(3)]
    if t < 0.70:  # AP-ish deformed
        d = q(rnd.uniform(0.8, 1.6)); return [1 + k * d + rnd.choice((-1, 1)) * eps() for k in range(1, 5)]
    if t < 0.85: return [q(rnd.uniform(1.05, 12)) for _ in range(4)]
    return [F(8) + rnd.choice((-1, 1)) * rnd.choice((F(1), 1 - eps(), 1 + eps(), eps())), q(rnd.uniform(1.2, 6.8)), q(rnd.uniform(1.2, 6.8)), q(rnd.uniform(1.2, 12))]
def big_plain():
    k = int(10 ** rnd.uniform(0.5, 5.1)) ; k = max(k, 3)
    d = rnd.choice((F(0), F(1), F(-1), 1 - eps(), -1 + eps(), 1 + eps(), -1 - eps(), eps(), -eps(), q(rnd.uniform(-1.2, 1.2))))
    return F(8 * k) + d
def aimed(lowset, extra=None):
    base = sorted([F(1)] + lowset + ([extra] if extra else []))
    if len(set(base)) != len(base) or base[0] != 1: return None
    steps, R = fpath([Q(x) for x in base])
    states = [Fr(s[0]) for s in steps] + [Fr(R)] + ([Fr(steps[-1][3])] if steps else [])
    Rk = rnd.choice(states); t = rnd.random()
    if t < 0.5:   # rho with R_k*rho = 8j+u
        j = int(10 ** rnd.uniform(0.5, 5.1)) + 3; u = rnd.choice((F(0), F(1), F(-1), 1 - eps(), -1 + eps(), 1 + eps(), -1 - eps(), eps(), -eps(), q(rnd.uniform(-1, 1))))
        return (8 * j + u) / Rk
    y = rnd.choice(base); i = rnd.randint(1, 6); j = int(10 ** rnd.uniform(0.5, 5.1)) + 3
    # exit of (new, j) = entry of (y, i) +- eps  or entry of new = exit of y
    if t < 0.75: return (8 * j + 1) * y / (8 * i - 1) * (1 + rnd.choice((-1, 0, 1)) * eps())
    return (8 * j - 1) * y / (8 * i + 1) * (1 + rnd.choice((-1, 0, 1)) * eps())
stats = Counter(); examples = defaultdict(list); best = (F(0), None); N = 0; hist = Counter(); mism = 0
bigmax = (F(0), None)
while time.time() - T0 < LIM:
    low = low_set(); mode = rnd.randrange(6)
    if mode == 0: a, b = big_plain(), big_plain()
    elif mode == 1: a = big_plain(); b = a * (1 + rnd.choice((-1, 1)) * eps())
    elif mode == 2: a = big_plain(); b = a + rnd.choice((-1, 1)) * eps()
    elif mode == 3: a = aimed(low); b = big_plain() if a is not None else None
    elif mode == 4:
        a = aimed(low); b = aimed(low, a) if a is not None else None
    else:
        a = big_plain(); b = aimed(low, a)
    if a is None or b is None or a <= 25 and b <= 25: continue
    rhos = [F(1)] + low + [a, b]
    if any(r <= 1 for r in rhos[1:]) or len(set(rhos)) != 7: continue
    rhos = sorted(rhos)
    if rhos[0] != 1 or rhos[6] <= 25 or rhos[5] <= 1: continue
    rh = [Q(x) for x in rhos]; N += 1
    cl, R, v, o = check(rh); stats[cl] += 1
    if R > 9: hist['landing>9'] += 1
    if R > 11: hist['landing>11'] += 1
    if o['nm'] >= 10: hist['nm>=10'] += 1
    if rhos[5] > 25: hist['rho6>25'] += 1
    if Fr(R) > best[0]: best = (Fr(R), rhos)
    if rhos[5] > 25 and Fr(R) > bigmax[0]: bigmax = (Fr(R), rhos)
    if N % 50 == 0:   # cross-check against official Fraction code
        oo = OFFICIAL_outcome(rhos)
        if oo['R'] != Fr(R) or oo['opener'] != o['opener'] or oo['closer'] != o['closer']: mism += 1
    for s in v:
        key = s.split(':')[0].split('_step')[0]; stats['VIOL ' + key] += 1
        if len(examples[key]) < 3: examples[key].append(rhos)
print('constructed', N, 'seconds', round(time.time() - T0))
print('official-vs-fast mismatches (every 50th):', mism)
print('classes', dict(sorted(stats.items())))
print('hist', dict(hist))
print('best landing', best[0], float(best[0]), [str(x) for x in best[1]])
print('best landing with rho_6>25', bigmax[0], float(bigmax[0]), [str(x) for x in bigmax[1]] if bigmax[1] else None)
for k, ex in examples.items():
    for e in ex: print('EXAMPLE', k, [str(x) for x in e])
