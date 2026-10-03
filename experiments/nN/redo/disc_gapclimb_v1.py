# Greedy climb of R* inside each cell meeting a gap edge: argv gap-lo gap-hi trials-per-cell.  Accept a step only if the path word equals the cell's and R* does not decrease.
import sys, pickle, random
import numpy as np
from fractions import Fraction as F
src = open('disc_gapsearch_v1.py').read()
exec(src.split('GAPS =')[0])
lo, hi, NT = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
Rl = np.array([c[1] for c in cells]); Rh = np.array([c[2] for c in cells])
cand = [i for i in range(len(cells)) if Rl[i] < hi and Rh[i] > lo and i in mem]
rnd = random.Random(7); best_all = (0, None); inside = []; tried = 0; acc = 0; nstart = []
for ci in cand:
    path_c, rlo, rhi, rng, w = cells[ci]; cur = [float(x) for x in mem[ci]]; curR = fpath(cur)[1]; nstart.append(curR)
    for t in range(NT):
        sc = 10 ** rnd.uniform(-7, -1)
        x = [1.0] + [min(max(cur[k] + rnd.gauss(0, sc), rng[k][0]), rng[k][1]) for k in range(1, 7)]
        if any(x[k] >= x[k+1] for k in range(6)): continue
        tried += 1; wd, R = fpath(x)
        if wd != tuple(path_c): continue
        acc += 1
        if R >= curR: cur, curR = x, R
        if lo < R < hi: inside.append((ci, x, R))
    if curR > best_all[0]: best_all = (curR, ci)
ver = 0
for ci, x, R in inside[:50]:
    rh = [F(1)] + [F(v) for v in x[1:]]; s, Rx = path(rh)
    if lo < Rx < hi and tuple((q['setter'] + 1, q['lap']) for q in s) == tuple(cells[ci][0]): ver += 1
print("gap (%g,%g): cells meeting gap with member %d, trials %d, accepted %d ; max R* of witnesses at start %.5f ; max R* reached by climb %.5f (cell %d) ; points inside gap %d (exact verified of first 50: %d)" % (lo, hi, len(cand), tried, acc, max(nstart), best_all[0], best_all[1], len(inside), ver))
