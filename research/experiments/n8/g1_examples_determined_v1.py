"""G1's configurations run through the cascade (threshold 1/8, exact). Readings are at an arbitrary scale D = 1; the
subject is at 0. (a) the no-near-sharer triple, with and without a nearest runner at reading 1; (b) a near-sharer plus one
companion that hold every odd spine up to 31 in the way at D = 1. For each: d_min, the cascade's first lonely instant,
number of moves, the scales visited (D_j = 1/(8 t_j)), and whether the instant is a spine of scale 1."""
from fractions import Fraction as F
import math
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade(ds, n=8):
    th = F(1, n); m = min(ds); t = th / m; ts = [t]
    while True:
        best = t
        for d in ds:
            if cdist(d * t) < th:
                o = (math.ceil(d * t - th) + th) / d
                if o > best: best = o
        if best == t: return ts
        t = best; ts.append(t)
def odd_spines_in_way(ds, R0):
    return all(any(cdist(d * F(r, 8)) < F(1, 8) for d in ds) for r in range(1, R0 + 1, 2))
def report(name, ds):
    ts = cascade(ds); t = ts[-1]
    scales = [1 / (8 * x) for x in ts]
    print(f'{name}: readings {[str(d) for d in ds]}  d_min {min(ds)}')
    print(f'   odd spines 1..31 of scale 1 all in the way: {odd_spines_in_way(ds, 31)}')
    print(f'   cascade: {len(ts)-1} moves, first lonely instant t = {t} (u at scale 1 = {t*8} eighths), '
          f'R = {float(8*min(ds)*t):.4f}; scales visited {[str(D) for D in scales]}')
triple = [F(127, 100), F(141, 100), F(266, 100)]
report('(a) triple alone', triple)
report('(a) triple plus a runner at reading 1', [F(1)] + triple)
# (b) near-sharer at depth 1/3 below 8 (reading 23/3, slot 7, e = 2/3) plus companions keeping spines 3..31 in the way
for extra in ([F(23, 3)] + triple, [F(1), F(23, 3)] + triple, [F(1), F(25, 3)] + triple):
    report('(b) near-sharer plus triple', extra)
