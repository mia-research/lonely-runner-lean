"""n=4: lap numbers per setter pattern, a's reading at each iterate (reading = 4*a*t), max final reading."""
from fractions import Fraction as F
import math, random, collections
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    th = F(1, 4); t = th / ds[0]; steps = []
    while True:
        best = t; who = None; inway = []
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                inway.append(i)
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, t
        steps.append((who[0], who[1], tuple(inway))); t = best
names = 'abc'
laps = collections.Counter(); maxread = F(0); arg = None; both = 0
random.seed(5)
samples = []
step = F(1, 20)
for i in range(0, 20 * 24 + 1):
    for j in range(i, 20 * 24 + 1):
        samples.append((1 + i * step, 1 + j * step))
for _ in range(150000):
    b = 1 + F(random.randint(0, 10**6), random.choice([997, 10007, 99991]))
    samples.append((b, b + F(random.randint(0, 10**6), random.choice([991, 10009, 99989]))))
for b, c in samples:
    s, t = chain([F(1), b, c])
    r = 4 * t
    if r > maxread: maxread, arg = r, (b, c, s)
    key = ' '.join(f'{names[i]}{k}' for i, k, _ in s)
    laps[key] += 1
    if any(len(w) > 1 for _, _, w in s): both += 1
print('max final a-reading', maxread, float(maxread), 'at b,c =', arg[0], arg[1], [(names[i], k, w) for i, k, w in arg[2]])
print('chains with two runners in the way at one iterate:', both)
for k, n in sorted(laps.items(), key=lambda kv: (len(kv[0].split()), kv[0])):
    print(f'{k:14s} {n}')
