# For the cells visited by the walks (lowest ratio first): an exact interior six-tuple of the cell (micro-jitter of the cell's vertex, same signature), then the exact R2 set of rho_7 > rho_6 (cap 1000).
# Reports whether any visited low-ratio cell has a nonempty allowed set (a gate crosser), and the largest rho_7/(7 rho_6) among allowed values.
import pickle, sys, time, random
exec(open('k6map_task1b_v1.py').read().split('rnd = random.Random')[0].replace('CAP = F(80)', 'CAP = F(1000)'))
from k6map_lp_v1 import cell
rnd = random.Random(9)
vis = {}
for f in ['k6map_walk_best_v1.pkl', 'k6map_walk_best_wide_v1.pkl']: vis.update(pickle.load(open(f, 'rb'))["visited"])
cells = sorted(vis.values(), key=lambda v: v[0])
t0 = time.time(); done = 0; nonempty = 0; refound = 0; best = None; lowest_ne = None
for ratio, vert, lam, sg, src in cells:
    if time.time() - t0 > 420: break
    pt = None
    for t in range(60):
        P = [F(1)] + [x + F(rnd.randint(-10**6, 10**6), 10**6) * F(1, 10**8) for x in vert[1:]]
        if all(a < b for a, b in zip(P, P[1:])):
            cc = cell(P)
            if cc and cc[0] == sg: pt = P; break
    done += 1
    if pt is None: continue
    refound += 1
    c, A = allowed(pt, F(1000))
    if A:
        nonempty += 1
        r = max(h for l, h in A) / (7 * pt[5])
        if best is None or r > best[0]: best = (r, ratio, pt, A)
        if lowest_ne is None: lowest_ne = (ratio, pt, A)
print("cells examined (lowest ratio first):", done, "| interior point re-found:", refound, "| with nonempty allowed rho_7 set (cap 1000):", nonempty, "| time %.0fs" % (time.time() - t0))
print("ratio value of the examined range: %.5f .. %.5f" % (float(cells[0][0]), float(cells[done - 1][0])))
if lowest_ne: print("lowest-ratio cell with a gate crosser: ratio %s = %.5f; tuple %s; allowed %s" % (lowest_ne[0], float(lowest_ne[0]), [str(x) for x in lowest_ne[1]], [(round(float(l), 4), round(float(h), 4)) for l, h in lowest_ne[2]]))
if best: print("largest sup(allowed)/(7 rho_6): %.5f (cell ratio %.5f)" % (float(best[0]), float(best[1])), "tuple", [str(x) for x in best[2]], "allowed", [(round(float(l), 4), round(float(h), 4)) for l, h in best[3]])
