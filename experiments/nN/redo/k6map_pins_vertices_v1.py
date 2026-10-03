# Task 2, named extremal vertices: for each vertex V (from the b12 / ceil outputs) find (by exact micro-jitter of V and path()) a fine cell whose exact optimum of rho_IDX is V,
# list its tight rows (deduped), the graph on the 7 readings, and the rows incident to reading 1 with the state height.
import sys, random, time
sys.path.insert(0, '.')
from ceil_lib_v1 import *
rnd = random.Random(5)
V = {
 "X24 cell (max rho7 86989/3565)": (7, [F(1), F(2023, 713), F(119, 31), F(608923, 124155), F(86989, 13795), F(7), F(86989, 3565)]),
 "16.21 cell (max rho7 34675/2139)": (7, [F(1), F(95, 33), F(475, 123), F(475, 99), F(19, 3), F(475, 69), F(34675, 2139)]),
 "511/31 vertex (max rho7)": (7, [F(1), F(161, 55), F(161, 41), F(161, 33), F(161, 25), F(7), F(511, 31)]),
 "rho6 max 124509/15275 vertex": (6, [F(1), F(11319, 3055), F(119, 23), F(3773, 611), F(7), F(124509, 15275), F(343, 39)]),
 "rho6 57/7 vertex": (6, [F(1), F(285, 77), F(1767, 343), F(475, 77), F(1625, 231), F(57, 7), F(22325, 2541)]),
 "rho6 73/9 vertex": (6, [F(1), F(365, 99), F(2263, 441), F(1825, 297), F(7), F(73, 9), F(79, 9)]),
 "b12 extremal vertex (min rho7 = 2209/297, R* sup 26433/2209)": (7, [F(1), F(16715503, 7123545), F(47, 15), F(726761, 173745), F(47, 9), F(15463, 2673), F(2209, 297)]),
}
X24I = [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286', '474233610200591258564537783/19451412054102649094869700']]
START = {"X24 cell (max rho7 86989/3565)": X24I, "16.21 cell (max rho7 34675/2139)": X7}
def meaning(rows, tags, i): return row_meaning(tags[i])
for name, (IDX, v) in V.items():
    print("==", name, "IDX", IDX, "V =", [str(t) for t in v])
    found = None; t0 = time.time()
    for it in range(3000):
        if time.time() - t0 > 60: break
        sc = F(1, 10**rnd.choice((5, 6, 7, 8, 9)))
        P = START[name] if (it == 0 and name in START) else [F(1)] + [x + F(rnd.randint(-10**6, 10**6), 10**6) * sc for x in v[1:]]
        if not all(a < b for a, b in zip(P, P[1:])): continue
        st, R = path(P)
        if not (any(s['setter'] == 0 for s in st) and R > 7): continue
        rows, tags, _ = cell_rows(P)
        if IDX == 7 and name.startswith("b12"):
            # the b12 objective: minimise the last setter's reading; here the vertex is a min of rho_7 over the cell
            r = min_rho_s_exact(rows, 7)
        else:
            r = maxrho(rows, IDX)
        if r and r[0] == v: found = (rows, tags, st, r); break
    if not found: print("   cell with this vertex as exact optimum: not reached by 3000 jitters in 60 s"); continue
    rows, tags, st, (X, lam) = found
    tl = dedupe_rows(rows, tight(rows, X)); states = [(1, 0)] + [(8 * s_['lap'] + 1, s_['setter']) for s_ in st]
    print("   jitter iterations", it, "| path moves", len(st), "| tight rows (deduped)", len(tl))
    par = list(range(7))
    def find(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    for i in tl:
        a = rows[i]; idx = [k for k, c in enumerate(a) if c]
        if len(idx) == 2: par[find(idx[0])] = find(idx[1])
        mark = ""
        if 0 in idx and len(idx) == 2 and tags[i][0] != 'order':
            k = tags[i][2]; c, s = states[k]; mark = "   <-- incident to reading 1; state %d at height R = %s" % (k, F(c) / X[s]); y = idx[0] if idx[1] == 0 else idx[1]; mark += ", pins rho_%d = %s" % (y + 1, X[y])
        print("   ", a, row_meaning(tags[i]), "dual", lam.get(i), mark)
    print("   tight graph connected on 7 readings:", len(set(find(a) for a in range(7))) == 1)
