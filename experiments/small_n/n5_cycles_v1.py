"""n=5 (near-rational speed ratios): long chains cut into b-cycles.  For each cycle (b's setting to b's next setting): b's lap, c's and d's laps
in the cycle, lap advances, growth of the cycle, and the bound from the setters' laps.  Reports how the longest chains end."""
from fractions import Fraction as F
import math, random
n = 5; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []; ts = [t]
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, ts
        steps.append(who); t = best; ts.append(t)
rng = random.Random(8)
found = []
RATS = [F(1), F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3)]
for _ in range(120000):
    b = F(rng.randint(20, 1000)) + F(rng.randint(0, 999), 1000)
    r = sorted([b, b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)])
    if len(set(r)) < 3 or r[0] <= 1: continue
    s, ts = chain([F(1)] + r)
    if len(s) >= 25: found.append((len(s), r, s, ts))
found.sort(key=lambda x: -x[0])
names = 'abcd'
print('chains with >= 25 moves:', len(found))
for L, r, s, ts in found[:4]:
    print(f'\nlength {L}; ratios b,c,d = {[round(float(x),4) for x in r]}; c/b = {float(r[1]/r[0]):.5f}, d/b = {float(r[2]/r[0]):.5f}; final nearest reading {float(5*ts[-1]):.4f}')
    print('  word:', ''.join(names[i] for i, _ in s))
    bpos = [j for j, (i, _) in enumerate(s) if i == 1]
    for p, q in zip(bpos, bpos[1:]):
        seg = s[p:q + 1]
        laps = ' '.join(f'{names[i]}{k}' for i, k in seg)
        growth = ts[q + 1] / ts[p + 1]
        bound = math.prod(F(5 * k + 1, 5 * k - 1) for _, k in s[p + 1:q + 1])
        print(f'   cycle {laps:32s} growth {float(growth):.5f}  setter-lap bound {float(bound):.5f}')
    # the end: last few iterates, who is near
    j = len(s)
    t = ts[-1]
    print('  at the end: positions (fraction of lap) of b,c,d:', [round(float((x * t) % 1), 4) for x in r])
