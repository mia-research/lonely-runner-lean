# Task 2: pins.  For every distinct fine cell (b12 sense) of the exact gate-crossing arrangements in stress_seeds_v1.pkl (plus X7, X24, the b12 extremal arrangement):
#  (i) every row of cell_rows has at most two nonzero entries (binary homogeneous);
#  (ii) exact optimum vertex of rho_IDX (IDX = 7 or 6) over the closed cell (Fractions, exact dual): tight binary rows form a graph on the 7 readings;
#  (iii) rows incident to reading 1 at the vertex: the state height R_k (value at the vertex) and the pinned reading's value.
# usage: k6map_pins_v1.py IDX LIMIT_SECONDS
import sys, time, pickle, math
from collections import Counter, defaultdict
sys.path.insert(0, '.')
from ceil_lib_v1 import *
IDX = int(sys.argv[1]); BUD = float(sys.argv[2])
seeds = list(pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys())
extra = [X7, [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286', '474233610200591258564537783/19451412054102649094869700']]]
try:
    x0 = pickle.load(open('b12_A_x0_v1.pkl', 'rb')); extra.append([F(t) for t in x0] if not isinstance(x0, dict) else None)
except Exception as e: print("b12 x0 not loaded:", e)
extra = [e for e in extra if e]
seeds = extra + seeds
seen = set(); t0 = time.time(); ncell = 0; nonbinary_cells = 0; maxnz = 0
disconnected = 0; tree_ok = 0; nolp = 0
pin_count = Counter(); height_count = Counter(); rank_count = Counter(); rowtype = Counter(); examples = {}
top = []
for x in seeds:
    if time.time() - t0 > BUD: break
    x = norm(list(x)); rows, tags, (steps, Rend) = cell_rows(x)
    sg = sigkey(tags, steps)
    if sg in seen: continue
    seen.add(sg); ncell += 1
    nz = [sum(1 for v in a if v) for a in rows]; maxnz = max(maxnz, max(nz))
    if max(nz) > 2: nonbinary_cells += 1
    r = maxrho(rows, IDX)
    if not r: nolp += 1; continue
    X, lam = r
    tl = dedupe_rows(rows, tight(rows, X))
    # graph on readings
    par = list(range(7))
    def find(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    for i in tl:
        idx = [k for k, v in enumerate(rows[i]) if v]
        if len(idx) == 2: par[find(idx[0])] = find(idx[1])
    comps = len(set(find(a) for a in range(7)))
    if comps == 1: tree_ok += 1
    else: disconnected += 1
    states = [(1, 0)] + [(8 * st['lap'] + 1, st['setter']) for st in steps]
    for i in tl:
        a = rows[i]; idx = [k for k, v in enumerate(a) if v]
        if 0 in idx and len(idx) == 2:
            y = idx[0] if idx[1] == 0 else idx[1]; tg = tags[i]
            kind = tg[0] if tg[0] in ('exit', 'clear-low', 'clear-high', 'setter', 'order') else 'entry'
            if kind == 'order': rowtype[('order', y + 1)] += 1; continue
            k = tg[2]; c, s = states[k]; Rk = F(c) / X[s]
            pin = X[y]
            key = (y + 1, str(pin), str(Rk), kind, k == 0)
            pin_count[(y + 1, pin)] += 1; height_count[Rk] += 1; rowtype[(kind, s == 0)] += 1
            if key not in examples: examples[key] = (tags[i][0] if False else row_meaning(tg), [str(v) for v in X])
    top.append((X[IDX - 1], [str(v) for v in X]))
print("IDX", IDX, "cells processed", ncell, "time %.0fs" % (time.time() - t0), "| cells with a row of >2 nonzero entries:", nonbinary_cells, "(max nonzero entries in any row: %d)" % maxnz, "| LP not certified:", nolp)
print("tight binary rows at the vertex connect all 7 readings:", tree_ok, "cells; not connected:", disconnected)
print("heights R_k of the states carrying a tight row incident to reading 1 (value at the vertex) -> count:", sorted((str(k), v) for k, v in height_count.items()))
print("row types incident to reading 1 (kind, setter is reading 1) -> count:", sorted(rowtype.items(), key=str))
print("pinned readings (rank, value) -> count:")
for (y, v), n in sorted(pin_count.items(), key=lambda t: (-t[1], t[0][0])): print("   rho_%d = %s = %.6f : %d" % (y, v, float(v), n))
print("examples (distinct (rank, value, height, kind, state0)):")
for k, (m, X) in list(examples.items())[:40]: print("  ", k, "|", m)
top.sort(key=lambda t: -t[0]); print("top vertices:")
for v, X in top[:6]: print("  ", v, float(v), X)
