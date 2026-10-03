# Task 1(c): exact minimisation of  ratio = 7 rho_6 L_max / 2  (L_max = longest component of K6 on [1,7]) over the closed fine cell, then a pivot-style walk across cells.
# Exact per cell (k6map_lp_v1.exact_lp: Fraction vertex, all rows checked in Fractions, exact dual certificate).  Neighbouring cells are found by exact micro-perturbations of the
# vertex (not by random restarts of the objective).  "Not reached by" language: the walk visits only the cells it reaches.
import sys, time, heapq, pickle
from k6map_lp_v1 import *
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 480
rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
def label(e): return {'in': 'entry', 'out': 'exit', 'lo': 'R=1', 'hi': 'R=7'}[e[0]] + ('' if e[0] in ('lo', 'hi') else '(%d,%d)' % (e[1] + 1, e[2]))
def jitter(rho, scale):
    out = [rho[0]]
    for r in rho[1:]: out.append(r + F(rnd.randint(-10**6, 10**6), 10**6) * scale)
    return out if all(a < b for a, b in zip(out, out[1:])) else None
visited = {}; heap = []; cnt = 0; best = None; t0 = time.time(); lpfail = 0
def add_point(rho, src):
    global cnt, best, lpfail
    c = cell(rho)
    if c is None: return
    sig, rows, comps, cf = c
    if sig in visited: return
    r = exact_lp(rows, cf)
    if r is None: lpfail += 1; visited[sig] = None; return
    val, w, lam = r
    vert = w_to_rho(w); ratio = 7 * val / 2
    visited[sig] = (ratio, vert, lam, sig, src)
    cnt += 1
    heapq.heappush(heap, (ratio, cnt, vert))
    if best is None or ratio < best[0]: best = (ratio, vert, lam, sig, src); print("  new best %s = %.6f  (cells %d, t=%.0fs, from %s)" % (ratio, float(ratio), cnt, time.time() - t0, src), flush=True)
def seeds():
    S = []
    S += [("progression", [F(i) for i in range(1, 7)])]
    S += [("X24 six", [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286']])]
    S += [("mix8 min", [F(1), F(8, 3), F(10, 3), F(9, 2), F(6), F(22, 3)]), ("mix8 2nd", [F(1), F(3), F(7, 2), F(4), F(5), F(20, 3)]),
          ("int 1,2,5,6,7,8", [F(x) for x in (1, 2, 5, 6, 7, 8)]), ("int 1,4,5,6,7,11", [F(x) for x in (1, 4, 5, 6, 7, 11)]), ("int 1,2,3,4,5,7", [F(x) for x in (1, 2, 3, 4, 5, 7)]),
          ("16.21 vertex six", [F(1), F(95, 33), F(475, 123), F(475, 99), F(19, 3), F(475, 69)])]
    seeds_all = list(pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys())
    for x in rnd.sample(seeds_all, 40): S.append(("crosser six", list(x[:6])))
    return S

old = pickle.load(open('k6map_walk_best_v1.pkl', 'rb'))["visited"]
for sg, v in old.items(): visited[sg] = v
top = sorted(old.values(), key=lambda v: v[0])[:60]
for ratio, vert, lam, sg, src in top:
    cnt += 1; heapq.heappush(heap, (ratio, cnt, vert))
best = (top[0][0], top[0][1], top[0][2], top[0][3], top[0][4])
print("resumed: visited cells", len(visited), "heap", len(heap), "best", float(best[0]), flush=True)
exp = 0

while heap and time.time() - t0 < BUDGET:
    ratio, _, vert = heapq.heappop(heap); exp += 1
    for sc in (F(1, 10**8), F(1, 10**6), F(1, 10**5), F(1, 3*10**4), F(1, 10**4), F(1, 3000), F(1, 1000), F(1, 300)):
        for _ in range(20):
            p = jitter(vert, sc)
            if p: add_point(p, "walk")
    if time.time() - t0 > BUDGET: break
print("cells visited %d, expanded %d, frontier left %d, LP not certified %d, time %.0fs" % (cnt, exp, len(heap), lpfail, time.time() - t0))
vals = sorted(set(v[0] for v in visited.values() if v)); print("lowest distinct cell minima:", [(str(v), round(float(v), 6)) for v in vals[:10]])
ratio, vert, lam, sig, src = best
print("BEST exact:", ratio, float(ratio), "vertex", [str(x) for x in vert], "from", src)
print("check by exact K6 of the vertex tuple: ratio, L =", ratio_of(vert), "strictly increasing:", all(a < b for a, b in zip(vert, vert[1:])))
print("K6 of vertex:", [(str(a), str(b)) for a, b in K6(vert)])
nrows = len(cell(jitter(vert, F(1, 10**9)) or vert)[1]) if cell(jitter(vert, F(1, 10**9)) or vert) else None
pickle.dump({"best": best, "visited": {k: v for k, v in visited.items() if v}}, open('k6map_walk_best_v2.pkl', 'wb'))
