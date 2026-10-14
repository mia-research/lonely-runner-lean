"""Checks behind MANUSCRIPT_v9 corrections (from V8_2_ISOLATED_AUDIT_v1).
(1) Runner 2 of (1, 1+√2/100, 3, ..., 8): the cascade from 1/(8δ), δ = √2/100, exactly in Q(√2); its fixed point versus 75√2/4.
(2) Moves of the cascade for (27, 70, 107, 137, 159, 188, 344, 393), runner 393, exact.
"""
from fractions import Fraction as F
import math
from lattice_witness_irrational_v1 import sign, floor_q2
# numbers a + b√2 as pairs
def mul(x, y): return (x[0]*y[0] + 2*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def inv(x):
    a, b = x; den = a*a - 2*b*b
    return (a/den, -b/den)
def sub(x, y): return (x[0]-y[0], x[1]-y[1])
def lt(x, y): return sign(*sub(x, y)) < 0
def fl(x): return floor_q2(*x)
n = 8; th = F(1, n)
speeds = [(F(1), F(0)), (F(1), F(1, 100))] + [(F(k), F(0)) for k in range(3, 9)]
subj = speeds[1]
ds = []
for v in speeds:
    if v == subj: continue
    d = sub(v, subj)
    if sign(*d) < 0: d = (-d[0], -d[1])
    ds.append(d)
def cdist_lt(x):   # circle distance of x < 1/8 ?
    k = fl(x); fr = sub(x, (F(k), F(0)))
    return lt(fr, (th, F(0))) or lt((1 - th, F(0)), fr)
dmin = min(ds, key=lambda d: float(d[0]) + float(d[1]) * math.sqrt(2))
t = mul((th, F(0)), inv(dmin)); moves = 0
while True:
    best = t; 
    for d in ds:
        dt = mul(d, t)
        if cdist_lt(dt):
            k = math.ceil(float(dt[0]) + float(dt[1]) * math.sqrt(2) - 1/8)   # candidate; verify exactly
            for kk in (k - 1, k, k + 1):
                o = mul((F(kk) + th, F(0)), inv(d))
                if not lt(o, t) and not cdist_lt(mul(d, o)) and lt(t, o) or (kk == k):
                    pass
            # exact next opening: least (kk + 1/8)/d strictly after being in the way, i.e. kk = ceil(d t − 1/8)
            kk = fl(sub(dt, (th, F(0))))
            if sign(*sub(sub(dt, (th, F(0))), (F(kk), F(0)))) != 0: kk += 1
            o = mul((F(kk) + th, F(0)), inv(d))
            if lt(best, o): best = o
    if best == t: break
    t = best; moves += 1
val = float(t[0]) + float(t[1]) * math.sqrt(2)
print(f'(1) runner 2 cascade: {moves} moves, fixed at {t[0]} + {t[1]}·√2 ≈ {val:.6f}; 75√2/4 ≈ {75*math.sqrt(2)/4:.6f}')
# (2)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
v = [27, 70, 107, 137, 159, 188, 344, 393]; i = 7
dd = [F(abs(x - v[i])) for x in v if x != v[i]]
m = min(dd); tt = th / m; mv = 0
while True:
    b = tt
    for d in dd:
        if cd(d * tt) < th:
            o = (math.ceil(d * tt - th) + th) / d
            if o > b: b = o
    if b == tt: break
    tt = b; mv += 1
print(f'(2) (27,...,393) runner 393: {mv} moves, t = {tt}')
