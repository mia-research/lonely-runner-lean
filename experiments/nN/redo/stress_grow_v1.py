# stress_grow_v1.py -- from exact gate-crossing seeds (stress_seeds_v1.pkl), aimed modifications of the top readings (beyond 25) and exact
# tie constructions (exit of one zone = entry/exit of another, solved exactly, then perturbed by +-1/10^k).  Every arrangement is
# an exact Fraction set checked by check() (G, C, S, class list, structural anomalies); every 40th is re-run with the official code.
# usage: python3 stress_grow_v1.py SECONDS SEED MODE   (MODE: top | tie | both)
import sys, pickle; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
from collections import Counter, defaultdict
T0 = time.time(); LIM = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2])); MODE = sys.argv[3]
seeds = sorted(pickle.load(open('stress_seeds_v1.pkl', 'rb')).items(), key=lambda kv: -kv[1][1])
S = [k for k, _ in seeds]; top = S[:2000] + [rnd.choice(S) for _ in range(2000)] if len(S) > 2000 else S
def eps(): return F(1, 10 ** rnd.randint(2, 12))
UB = lambda: rnd.choice((F(0), F(1), F(-1), 1 - eps(), -1 + eps(), 1 + eps(), -1 - eps(), eps(), -eps(), F(rnd.randint(-100, 100), 100)))
def states_of(r):
    steps, R = fpath([Q(x) for x in r]); return [Fr(s[0]) for s in steps] + [Fr(s[3]) for s in steps]
def op_top(r):
    r = list(r); st = states_of(r); t = rnd.random(); y = rnd.choice((5, 6, 6))
    v = r[y]
    if t < 0.2: r[y] = v * (1 + rnd.choice((-1, 1)) * eps()) if rnd.random() < .5 else v + rnd.choice((-1, 1)) * eps()
    elif t < 0.4: r[y] = v * F(int(10 ** rnd.uniform(0, 4.3) * 1000), 1000) 
    elif t < 0.6: k = int(rnd.uniform(3, 10 ** rnd.uniform(0.5, 5.1))) + 1; r[y] = 8 * k + UB()
    elif t < 0.9 and st:
        Ri = rnd.choice(st); j = int(25 * Ri / 8) + 1 + int(10 ** rnd.uniform(0, 4.5)) * rnd.randrange(2); r[y] = (8 * j + UB()) / Ri
    else:
        r[6] = r[5] * (1 + rnd.choice((-1, 1)) * eps()); r[5] = r[5]
    return r
def op_tie(r):
    r = list(r); steps, R = fpath([Q(x) for x in r])
    if not steps: return r
    k = rnd.randrange(len(steps)); Rk, st, lap, R2 = Fr(steps[k][0]), steps[k][1], steps[k][2], Fr(steps[k][3])
    y = rnd.randrange(1, 7)
    t = rnd.randrange(5); base = r[y]; pt = rnd.choice((Rk, R2))
    if t == 0: i = max(1, round((pt * base + 1) / 8)); new = (8 * i - 1) / pt      # entry of y at pt
    elif t == 1: i = max(1, round((pt * base - 1) / 8)); new = (8 * i + 1) / pt   # exit of y at pt
    elif t == 2:   # exit of y = entry of z at a state (two-reading tie, solved for y)
        z = rnd.randrange(1, 7); i = rnd.randint(1, 6); j = max(1, round(base * r[z] / (r[z]) / 8)) if False else max(1, round((pt * base + 1) / 8))
        new = (8 * j + 1) * r[z] / (8 * i - 1) if z != y else base
    elif t == 3:
        z = rnd.randrange(1, 7); i = max(1, round((pt * r[z] + 1) / 8)); j = max(1, round(pt * base / 8))
        new = (8 * j - 1) * r[z] / (8 * i + 1)
    else:   # equality at the landing / gate state 9
        pt = rnd.choice((F(9), Fr(R))); i = max(1, round((pt * base + 1) / 8)); new = (8 * i + rnd.choice((-1, 1))) / pt
    if new <= 1: return r
    r[y] = new * (1 + rnd.choice((-1, 0, 0, 1)) * eps())
    return r
stats = Counter(); examples = defaultdict(list); N = 0; mism = 0; hist = Counter(); bestA = (F(0), None); bestB = (F(0), None)
while time.time() - T0 < LIM:
    base = list(rnd.choice(top)); m = MODE if MODE != 'both' else rnd.choice(('top', 'tie'))
    r = op_top(base) if m == 'top' else op_tie(base)
    if rnd.random() < 0.3: r = (op_top if m == 'top' else op_tie)(r)
    r = sorted(r)
    if r[0] != 1 or len(set(r)) != 7 or r[1] <= 1: continue
    rh = [Q(x) for x in r]; N += 1
    cl, R, v, o = check(rh); stats[cl] += 1; Rf = Fr(R)
    for th in (9, 11, 12): 
        if Rf > th: hist['landing>%d' % th] += 1
    if r[6] > 25: 
        hist['rho7>25'] += 1
        if Rf > 9: hist['rho7>25 & landing>9'] += 1
        if Rf > bestA[0]: bestA = (Rf, r)
    if r[5] > 25:
        hist['rho6>25'] += 1
        if Rf > 9: hist['rho6>25 & landing>9'] += 1
        if Rf > bestB[0]: bestB = (Rf, r)
    if Rf > F(26433, 2209): hist['ABOVE_26433/2209'] += 1; examples['ABOVE'].append(r)
    if N % 40 == 0:
        oo = OFFICIAL_outcome(r)
        if oo['R'] != Rf or oo['opener'] != o['opener'] or oo['closer'] != o['closer']: mism += 1
    for s in v:
        key = s.split(':')[0].split('_step')[0]; stats['VIOL ' + key] += 1
        if len(examples[key]) < 3: examples[key].append(r)
print('args', sys.argv[1:], 'seeds', len(S)); print('evaluated', N, 'seconds', round(time.time() - T0), 'official mismatches', mism)
print('classes', dict(sorted(stats.items()))); print('hist', dict(hist))
print('best landing with rho_7>25', bestA[0], float(bestA[0]), [str(x) for x in bestA[1]] if bestA[1] else None)
print('best landing with rho_6>25', bestB[0], float(bestB[0]), [str(x) for x in bestB[1]] if bestB[1] else None)
for k, ex in examples.items():
    for e in ex[:3]: print('EXAMPLE', k, [str(x) for x in e])
