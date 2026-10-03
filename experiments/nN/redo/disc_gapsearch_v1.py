# Cell-level search: can a gap of the member R* distribution be entered by another point of a cell that meets the gap?
# For each gap and each (sampled) cell meeting it: random walk of readings inside the cell's reading box starting at the stored witness,
# accepted only if the cascade path word equals the cell's path; the R* of every accepted point is recorded; a point inside the gap is re-verified with exact Fractions.
import pickle, random, sys
import numpy as np
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
cells = pickle.load(open('terminals5_J2.pkl', 'rb')); mem = dict(pickle.load(open('cell_members_J2.pkl', 'rb')))
def fpath(rh):
    R = 1.0; word = []
    for _ in range(80):
        best = None
        for i, r in enumerate(rh):
            p = (R * r) % 8
            if min(p, 8 - p) < 1:
                j = round(R * r / 8); e = (8 * j + 1) / r
                if best is None or e > best[0]: best = (e, i, j)
        if best is None: return tuple(word), R
        word.append((best[1] + 1, best[2])); R = best[0]
    return tuple(word), R
GAPS = [(1.0, 1.114915), (1.114915, 1.20733), (1.42419, 1.46779), (5.79463, 5.83980), (6.38543, 6.44043), (6.62725, 6.66423), (6.66423, 6.78001), (6.78512, 7.0), (10.82875, 10.90586), (11.08715, 11.23725), (11.23725, 11.27444), (11.33189, 11.52507), (11.52507, 11.55633)]
Rl = np.array([c[1] for c in cells]); Rh = np.array([c[2] for c in cells])
which = [int(a) for a in sys.argv[1].split(',')]
NC, NT = int(sys.argv[2]), int(sys.argv[3])
for gi in which:
    lo, hi = GAPS[gi]; rnd = random.Random(1000 + gi)
    cand = [i for i in range(len(cells)) if Rl[i] < hi and Rh[i] > lo and i in mem]
    ncand_all = int(((Rl < hi) & (Rh > lo)).sum())
    pick = cand if len(cand) <= NC else rnd.sample(cand, NC)
    acc = 0; tried = 0; inside = []; Rmin, Rmax = 99, 0; near = 0
    for ci in pick:
        path_c, rlo, rhi, rng, w = cells[ci]; w0 = [float(x) for x in mem[ci]]
        cur = w0[:]; 
        for t in range(NT):
            sc = 10 ** rnd.uniform(-6, -0.5)
            x = [1.0] + [min(max(cur[k] + rnd.gauss(0, sc), rng[k][0]), rng[k][1]) for k in range(1, 7)]
            if any(x[k] >= x[k+1] for k in range(6)): continue
            tried += 1
            wd, R = fpath(x)
            if wd != tuple(path_c): continue
            acc += 1; Rmin = min(Rmin, R); Rmax = max(Rmax, R)
            if lo < R < hi: inside.append((ci, x, R))
            # drift towards the gap
            mid = (lo + hi) / 2
            if abs(R - mid) < abs(float(path(mem[ci])[1]) - mid) or rnd.random() < 0.3: cur = x
    ver = 0
    for ci, x, R in inside[:50]:
        rh = [F(1)] + [F(v) for v in x[1:]]; s, Rx = path(rh)
        if lo < Rx < hi and tuple((q['setter'] + 1, q['lap']) for q in s) == tuple(cells[ci][0]): ver += 1
    print("gap %d (%.5f,%.5f): cells meeting gap %d (with member %d), searched %d cells, %d trials, %d accepted (path word reproduced), accepted R* range [%.5f, %.5f], inside gap: %d (exact-verified of first 50: %d)" % (gi, lo, hi, ncand_all, len(cand), len(pick), tried, acc, Rmin, Rmax, len(inside), ver), flush=True)
