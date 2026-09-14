"""The cascade's first isolation time for the hard cases on file (exact rationals), checked against BSM (every zone
endpoint; boundary points evaluated separately).  v8 §6.8."""
from fractions import Fraction as F
import math
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade(V, i, n=8):
    ds = sorted(set(abs(v - V[i]) for j, v in enumerate(V) if j != i)); m = ds[0]
    t = F(1, n) / m; steps = 0
    while True:
        best = t; who = None
        for d in ds:
            if cd(d * t) < F(1, n):
                k = math.ceil(d * t - F(1, n)); o = (k + F(1, n)) / d
                if o > best: best, who = o, (d, k)
        if who is None: return t, steps, m
        t = best; steps += 1
def bsm_first(V, i, T, n=8):
    ds = sorted(set(abs(v - V[i]) for j, v in enumerate(V) if j != i)); c = set()
    for d in ds:
        for k in range(0, math.ceil(d * T) + 2):
            for e in (k + F(1, n), k - F(1, n)):
                x = e / d
                if 0 < x <= T: c.add(x)
    return min(x for x in c if all(cd(d * x) >= F(1, n) for d in ds))
CASES = [((1, 31, 75, 97, 128, 160, 176, 225), 1), ((1, 1975, 5265, 6910, 8737, 9589, 11845, 15135), 1),
         ((11, 21, 22, 23, 26, 34, 35, 40), 35), ((4, 12, 29, 37, 101, 121, 176, 196), 37)]
for V, sp in CASES:
    i = V.index(sp); T, st, m = cascade(V, i); b = bsm_first(V, i, T)
    print(f'{V} runner at {sp}: d_min {m}, cascade time {T} (u = {m*T}), moves {st}, BSM first {b}, agree {b == T}')
