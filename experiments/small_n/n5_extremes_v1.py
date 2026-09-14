"""n=5: (1) refine the largest nearest-runner reading by local search; trace the extremal chain;
(2) do returning setters always come back at the next lap; (3) chain length against the largest ratio."""
from fractions import Fraction as F
import math, random, collections
n = 5; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []; its = [t]
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, its
        steps.append(who); t = best; its.append(t)
def reading(r): s, its = chain([F(1)] + sorted(r)); return n * its[-1]
rng = random.Random(3)
best = (F(0), None)
starts = [[F(47117, 20000), F(32827, 10000), F(160133, 40000)]] + [[1 + F(rng.randint(0, 3000), 300) for _ in range(3)] for _ in range(30)]
for st in starts:
    cur = st; cs = reading(cur)
    for it in range(3000):
        scale = [F(1, 10), F(1, 100), F(1, 1000), F(1, 10000)][it * 4 // 3000]
        new = [max(F(1), x + scale * F(rng.randint(-100, 100), 100)) for x in cur]
        ns = reading(new)
        if ns >= cs: cur, cs = new, ns
    if cs > best[0]: best = (cs, cur)
r = sorted(best[1]); s, its = chain([F(1)] + r)
print('largest nearest reading found', float(best[0]), 'ratios', [float(x) for x in r])
names = 'abcd'
for j, (i, k) in enumerate(s):
    print(f'  move {j+1}: setter {names[i]} lap {k}  nearest reading after {float(n*its[j+1]):.5f}')
# (2) and (3)
skip = 0; returns = 0; bylen = collections.defaultdict(int); maxlen_by = collections.defaultdict(int)
for _ in range(80000):
    M = rng.choice([5, 20, 100, 1000])
    r = sorted(1 + F(rng.randint(0, 10**6), 10**6) * M for _ in range(3))
    s, its = chain([F(1)] + r)
    last = {}
    for i, k in s:
        if i in last:
            returns += 1
            if k != last[i] + 1: skip += 1
        last[i] = k
    b = int(math.log10(float(r[-1]))) if r[-1] >= 1 else 0
    maxlen_by[b] = max(maxlen_by[b], len(s))
print('returns', returns, 'returns not at the next lap', skip)
print('longest chain by decade of largest ratio', dict(sorted(maxlen_by.items())))
