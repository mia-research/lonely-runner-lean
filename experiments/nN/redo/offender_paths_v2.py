"""Double collisions (set A of offender_paths_v1): the base landing's setter and lap, against the bound grid.  Exact.
For each: m = d_min, bound 1/(8m); the setter e's slot and the landing (e, K); whether t* = 9/(8e) (the setter's first
next opening); the colliders' readings at t*."""
from fractions import Fraction as F
from math import floor
from collections import Counter
import offender_paths_v1 as P
c = Counter(); ex = []
for T, L0 in P.A:
    m = min(T); t0 = F(1, 8 * m); t = P.cascade(T); i, K = P.setter(T, t); e = T[i]
    sl = P.slot(e * t0)
    c[('setter slot at bound, lap K', sl, K)] += 1
    c['t* = 9/(8e)'] += (t == F(9, 8 * e))
    cols = [d for d in T if d % 8 == 0]
    c[('colliders at 8m (both on the first lap)', all(d * t0 >= 1 - F(1, 8) and d * t0 < 2 + F(1,8) for d in cols))] += 1
    if len(ex) < 12: ex.append((T, m, e, K, str(t), [str((d * t) % 1) for d in T]))
for k, v in sorted(c.items(), key=str): print(k, v)
for x in ex: print(x)
