"""For n = 3..8: largest final reading of the nearest runner (n * a * T) and whether the nearest runner is ever in the way
at an iterate (i.e. whether the chain leaves the nearest runner's first clear window [1, n-1]); also whether a setter ever
repeats non-alternately. Same generators as chain_depth_by_n_v1."""
from fractions import Fraction as F
import math, random
random.seed(11)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; setters = []; nearest_inway = False
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                if i == 0: nearest_inway = True
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, i
        if who is None: return t, setters, nearest_inway
        t = best; setters.append(who)
for n in range(3, 9):
    trials = 20000 if n < 6 else 6000
    maxr = F(0); cnt_in = 0; cnt_beyond = 0; subj = 0
    for _ in range(trials):
        if random.random() < 0.5:
            v = sorted(set(F(random.randint(1, 4000), random.randint(1, 60)) for _ in range(n)))
        else:
            g = F(random.randint(1, 50), random.randint(1, 7))
            v = sorted(set(i * g + F(random.randint(-200, 200), 1000 * random.randint(1, 9)) for i in range(n)))
        if len(v) < n: continue
        for vi in v:
            ds = sorted(set(abs(w - vi) for w in v if w != vi)); subj += 1
            t, s, inw = chain(ds, n)
            r = n * ds[0] * t
            maxr = max(maxr, r); cnt_in += inw; cnt_beyond += (r > n - 1)
    print(f'n={n}: subjects {subj}, max nearest reading {float(maxr):.4f} (window edge {n-1}), '
          f'nearest in the way at some iterate: {cnt_in}, final reading beyond n-1: {cnt_beyond}')
