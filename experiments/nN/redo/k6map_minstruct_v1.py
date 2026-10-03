# structure of the cell minimisers of 7 rho_6 L_max / 2: for the lowest cells of the walks, the exact vertex, the binding components (dual weight on 't' rows), the tight order rows (labelled), and the tight graph on readings.
import sys, pickle
from k6map_lp_v1 import *
files = sys.argv[1:]
vis = {}
for f in files:
    d = pickle.load(open(f, 'rb'))["visited"]; vis.update(d)
low = sorted(vis.values(), key=lambda v: v[0])[:int(12)]
def lab(e):
    k, y, j = e
    return {'in': 'entry', 'out': 'exit', 'lo': 'R=1', 'hi': 'R=7'}[k] + ('' if k in ('lo', 'hi') else '(%d,%d)' % (y + 1, j))
for ratio, vert, lam, sg, src in low:
    # use the stored signature: find a point of that cell by jittering the vertex
    pt = None
    for t in range(4000):
        P = [F(1)] + [x + F(random.randint(-10**6, 10**6), 10**6) * F(1, 10**8) for x in vert[1:]]
        if all(a < b for a, b in zip(P, P[1:])):
            cc = cell(P)
            if cc and cc[0] == sg: pt = cc; break
    print("ratio %s = %.6f | vertex %s" % (ratio, float(ratio), [str(x) for x in vert]))
    if pt is None: print("   (cell point not re-found)"); continue
    sig, rows, comps, cf = pt
    r = exact_lp(rows, cf)
    val, w, lam = r
    nr = len(rows)
    print("   integers among readings:", [str(x) for x in vert if x.denominator == 1], "| rho_5, rho_6 =", str(vert[4]), str(vert[5]))
    for i, l in lam.items():
        if l == 0: continue
        if i < nr:
            if i < len(sig) - 1: print("   tight row (dual %s): %s <= %s" % (l, lab(sig[i]), lab(sig[i + 1])))
            else: print("   tight row (dual %s): rho-order / positivity row %d" % (l, i - (len(sig) - 1)))
        else:
            s_, e_ = comps[i - nr]; print('   binding component (dual %s): from %s to %s' % (l, lab((s_[1], s_[2], s_[3])), lab((e_[1], e_[2], e_[3]))))
    Wk = K6(vert); L = max(b - a for a, b in Wk)
    print("   K6 of vertex: %d windows, point windows %d, windows of length L: %d (L=%s)" % (len(Wk), sum(1 for a, b in Wk if a == b), sum(1 for a, b in Wk if b - a == L), L))
