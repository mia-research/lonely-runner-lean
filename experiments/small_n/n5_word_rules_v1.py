"""n=5 chains as words over the setters b<c<d (by speed). Check:
W1  x y x occurs only with y slower than x (no bcb, bdb, cdc);
W2  no y z y z;
gaps between consecutive settings of each runner (predicted: b: cd|dc|dcd; c: b|d|bd|db|dbd; d: b|c|bc|cb|cbc);
chains without b: at most 3 moves.  Also: growth G = 5*tau_end split by whether b sets."""
from fractions import Fraction as F
import math, random, collections
n = 5; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, t
        steps.append(who); t = best
names = 'abcd'
rng = random.Random(21)
w1 = w2 = 0; gaps = {x: collections.Counter() for x in 'bcd'}; nob_max = 0; nob_G = F(0); b_G = F(0); total = 0
def arrangements():
    for _ in range(120000):
        M = rng.choice([5, 10, 30, 100, 1000])
        r = sorted(1 + F(rng.randint(0, 10**6), 10**6) * M for _ in range(3))
        if len(set(r)) == 3 and r[0] > 1: yield r
    for _ in range(40000):  # near-AP
        g = F(rng.randint(1, 12), rng.randint(1, 3)); base = F(rng.randint(1, 60), rng.randint(1, 4))
        r = sorted(base + i * g + F(rng.randint(-300, 300), 1000 * rng.randint(1, 9)) for i in range(3))
        if len(set(r)) == 3 and r[0] > 1: yield r
for r in arrangements():
    s, t = chain([F(1)] + r); total += 1
    w = ''.join(names[i] for i, _ in s)
    if 'a' in w: print('nearest sets a move', r)
    for x in 'bcd':
        for y in 'bcd':
            if x != y and (x + y + x) in w and not (y < x): w1 += 1
    for y in 'bcd':
        for z in 'bcd':
            if y != z and (y + z + y + z) in w: w2 += 1
    for x in 'bcd':
        idx = [i for i, ch in enumerate(w) if ch == x]
        for p, q in zip(idx, idx[1:]): gaps[x][w[p + 1:q]] += 1
    G = 5 * t
    if 'b' not in w:
        nob_max = max(nob_max, len(w)); nob_G = max(nob_G, G)
    else:
        b_G = max(b_G, G)
print('arrangements', total)
print('W1 violations (xyx with y not slower):', w1, '| W2 violations (yzyz):', w2)
for x in 'bcd': print(f'gaps between settings of {x}:', dict(gaps[x]))
print('chains without b: longest', nob_max, 'largest nearest reading', float(nob_G), '(27/8 =', 27/8, ')')
print('chains with b: largest nearest reading', float(b_G))
