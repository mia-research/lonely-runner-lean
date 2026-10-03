# One EXACT witness per gap of the member R* distribution.  Floats only steer the walk; the verdict is path() on Fractions:
# the arrangement below is feasible iff (exact path word == the cell's word) and (exact R* in the open gap).
import sys, pickle, random
import numpy as np
from fractions import Fraction as F
exec(open('disc_gapsearch_v1.py').read().split('GAPS =')[0])
GAPS = [(F(1), F(9570149208162304, 8583747560173039)), (F(9570149208162304, 8583747560173039), F(120733, 100000)), (F(142419, 100000), F(146779, 100000)), (F(579463, 100000), F(583980, 100000)), (F(638543, 100000), F(644043, 100000)),
        (F(662725, 100000), F(666423, 100000)), (F(666423, 100000), F(678001, 100000)), (F(678512, 100000), F(7)), (F(1082875, 100000), F(1090586, 100000)), (F(1108715, 100000), F(1123725, 100000)),
        (F(1123725, 100000), F(1127444, 100000)), (F(1133189, 100000), F(1152507, 100000)), (F(1152507, 100000), F(1155633, 100000))]
Rl = np.array([c[1] for c in cells]); Rh = np.array([c[2] for c in cells])
for gi, (glo, ghi) in enumerate(GAPS):
    lo, hi = float(glo), float(ghi); mid = (lo+hi)/2; rnd = random.Random(500+gi)
    cand = [i for i in range(len(cells)) if Rl[i] < hi and Rh[i] > lo and i in mem]; rnd.shuffle(cand); found = None; tested = 0
    for ci in cand[:40]:
        path_c, rlo, rhi, rng, w = cells[ci]; cur = [float(x) for x in mem[ci]]; curd = abs(fpath(cur)[1]-mid); tested += 1
        for t in range(6000):
            sc = 10 ** rnd.uniform(-9, -1)
            x = [1.0] + [min(max(cur[k] + rnd.gauss(0, sc), rng[k][0]), rng[k][1]) for k in range(1, 7)]
            if any(x[k] >= x[k+1] for k in range(6)): continue
            wd, R = fpath(x)
            if wd != tuple(path_c): continue
            if abs(R-mid) <= curd: cur, curd = x, abs(R-mid)
            if lo < R < hi:
                rh = [F(1)] + [F(v) for v in x[1:]]; s, Rx = path(rh)
                if glo < Rx < ghi and tuple((q['setter']+1, q['lap']) for q in s) == tuple(path_c): found = (ci, rh, Rx); break
        if found: break
    if found:
        ci, rh, Rx = found
        print("gap %d (%s,%s): EXACT witness in cell %d, exact R* = %s (%.12f), readings %s" % (gi, float(glo), float(ghi), ci, Rx, float(Rx), [str(v) for v in rh]), flush=True)
    else: print("gap %d (%.6f,%.6f): UNDECIDED after %d cells (no exact witness found; this is not an infeasibility verdict)" % (gi, lo, hi, tested), flush=True)
