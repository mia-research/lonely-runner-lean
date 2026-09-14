"""n=4: moment-iteration chains for a subject with differences 1 = a <= b <= c (scale-free), threshold 1/4.
Records chain length, setter ranks and laps. Exact rationals; BSM ground truth: in the way iff circ dist < 1/4."""
from fractions import Fraction as F
import math, random, collections
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    th = F(1, 4); t = th / ds[0]; steps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, t
        steps.append(who); t = best
        if len(steps) > 50: return None, t
names = 'abc'
pat = collections.Counter(); maxlen = 0; ex = {}
def rec(b, c):
    global maxlen
    s, t = chain([F(1), b, c])
    if s is None: print('NO STOP', b, c); return
    key = ' '.join(f'{names[i]}@{k}' if False else names[i] for i, k in s)
    pat[(len(s), key)] += 1
    ex.setdefault((len(s), key), (str(b), str(c), [(names[i], k) for i, k in s], str(t)))
    maxlen = max(maxlen, len(s))
# grid
step = F(1, 20)
for i in range(0, 20 * 24 + 1):
    b = 1 + i * step
    for j in range(i, 20 * 24 + 1):
        rec(b, 1 + j * step)
# random fine rationals, wider range
random.seed(4)
for _ in range(150000):
    b = 1 + F(random.randint(0, 10**6), random.choice([997, 10007, 99991]))
    c = b + F(random.randint(0, 10**6), random.choice([991, 10009, 99989]))
    rec(b, c)
print('max chain length', maxlen)
for (L, key), n in sorted(pat.items()):
    print(f'len {L}  setters {key:8s} count {n:7d}  e.g. b={ex[(L,key)][0]} c={ex[(L,key)][1]} steps={ex[(L,key)][2]} T={ex[(L,key)][3]}')
