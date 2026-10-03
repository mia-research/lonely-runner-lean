# Edge of the R*<7 band: climb R* inside the cells that reach it; print readings and positions at the best point found.
import sys, pickle, random
import numpy as np
from fractions import Fraction as F
exec(open('disc_gapsearch_v1.py').read().split('GAPS =')[0])
rnd = random.Random(12)
for ci in (62251, 62250, 62249, 62248, 62247, 62252):
    path_c, rlo, rhi, rng, w = cells[ci]; cur = [float(x) for x in mem[ci]]; curR = fpath(cur)[1]; acc = 0
    for t in range(150000):
        sc = 10 ** rnd.uniform(-9, -2)
        x = [1.0] + [min(max(cur[k] + rnd.gauss(0, sc), rng[k][0]), rng[k][1]) for k in range(1, 7)]
        if any(x[k] >= x[k+1] for k in range(6)): continue
        wd, R = fpath(x)
        if wd != tuple(path_c): continue
        acc += 1
        if R >= curR: cur, curR = x, R
    psn = [(curR*r) % 8 for r in cur]
    rh=[F(1)]+[F(v) for v in cur[1:]]; st,Rx=path(rh); okw=tuple((q['setter']+1,q['lap']) for q in st)==tuple(path_c)
    print('   EXACT check of the climbed point (Fractions): path word equals cell word %s ; exact R* = %s ; exact positions at 1: %s' % (okw, Rx, [(Rx*r)%8==1 for r in rh]))
    print("cell %d: start R*=%.6f -> climbed R*=%.8f (accepted %d/150000); readings %s ; positions %s ; path last %s" % (ci, float(path(mem[ci])[1]), curR, acc, [round(v, 6) for v in cur], [round(p, 6) for p in psn], path_c[-3:]))
