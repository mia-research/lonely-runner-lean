# Shared library for the step-rule study.  Exact Fractions.  Readings rho_1=1<...<rho_7, all positive.
import random, math, pickle
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])   # path(), blocks(), pos()
def q(rnd, x, d=1000): return F(round(x * d), d)
def norm(xs):
    xs = sorted(xs); m = xs[0]; return [x / m for x in xs]
def ok(xs): return len(set(xs)) == 7 and min(xs) > 0
# ---- generators that give few moves (copies of outcome_survey_v2 families) ----
def fam_random(rnd):
    while True:
        s = rnd.choice((9, 20, 60, 200)); xs = sorted(q(rnd, math.exp(rnd.uniform(0, math.log(s)))) for _ in range(7)); xs[0] = F(1)
        if len(set(xs)) == 7: return xs
def fam_ap_def(rnd):
    while True:
        xs = [F(k) for k in range(1, 8)]
        for m in rnd.sample(range(7), rnd.choice((1, 2, 3, 4))): xs[m] = max(F(11, 10), xs[m] + q(rnd, rnd.uniform(-1.5, 3.5)))
        xs = norm(xs)
        if ok(xs): return xs
# ---- generators aimed at many moves ----
def fam_strip_multi(rnd):   # several readings in strips (8j-1,8j+1) for several j, several in the first strip
    while True:
        k = rnd.choice((2, 3, 4, 5, 6)); xs = [F(1)]
        for _ in range(k):
            j = rnd.choice((1, 1, 1, 2, 2, 3, 4, 5)); xs.append(q(rnd, 8 * j + rnd.uniform(-1.05, 1.05)))
        while len(xs) < 7: xs.append(q(rnd, rnd.uniform(1.1, 40)))
        xs = norm(xs)
        if ok(xs): return xs
def fam_first_strip(rnd):   # many readings in (7,9), plus others
    while True:
        k = rnd.choice((3, 4, 5, 6)); xs = [F(1)] + [q(rnd, rnd.uniform(6.9, 9.1)) for _ in range(k)]
        while len(xs) < 7: xs.append(q(rnd, 8 * rnd.randint(1, 6) + rnd.uniform(-1.5, 1.5)))
        xs = norm(xs)
        if ok(xs): return xs
def fam_chain(rnd):   # build by chaining: each new reading contains the previous exit R2 in one of its zones
    while True:
        xs = [F(1)]; j = rnd.choice((1, 1, 2, 3)); r1 = q(rnd, 8 * j + rnd.uniform(-1, 1)); xs.append(r1)
        R = (8 * j + 1) / r1
        for _ in range(5):
            jj = rnd.randint(1, 8); lo = (8 * jj - 1) / R; hi = (8 * jj + 1) / R
            if hi <= 1: continue
            lo = max(lo, F(11, 10)); r = q(rnd, rnd.uniform(float(lo), float(hi)))
            if r <= 1 or not (lo - F(1, 1000) <= r): xs.append(q(rnd, rnd.uniform(1.1, 30))); continue
            xs.append(r); R = (8 * jj + 1) / r if rnd.random() < 0.8 else R
        xs = norm(xs[:7])
        if ok(xs): return xs
def fam_climb(rnd, iters=60):   # hill-climb on number of moves from a strip_multi start
    xs = fam_strip_multi(rnd); best = len(path(xs)[0])
    for _ in range(iters):
        ys = list(xs); i = rnd.randrange(1, 7); ys[i] = max(F(11, 10), ys[i] * F(1000 + rnd.randint(-80, 80), 1000) + (q(rnd, rnd.uniform(-1, 1)) if rnd.random() < .3 else 0))
        ys = norm(ys)
        if ok(ys):
            n = len(path(ys)[0])
            if n >= best: xs, best = ys, n
    return xs
FAMS = [("random", fam_random), ("AP deformed", fam_ap_def), ("strip_multi", fam_strip_multi), ("first_strip", fam_first_strip), ("chain", fam_chain), ("climb", fam_climb)]
# ---- independent zone enumeration (does not use path()) ----
def zones_containing(R, rhos, J=400):
    out = []
    for y, r in enumerate(rhos):
        for j in range(1, J):
            lo, hi = (8 * j - 1) / r, (8 * j + 1) / r
            if lo >= R: break
            if lo < R < hi: out.append((y, j, hi))
    return out
