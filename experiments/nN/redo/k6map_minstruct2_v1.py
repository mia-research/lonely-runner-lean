# table over the visited cells (both walks): rho_6 and rho_5 at the cell-minimiser vertices, lowest cells first; counts of pinned rho_6 in the lowest N cells.
import pickle, sys
from collections import Counter
from k6map_lp_v1 import *
for f in sys.argv[1:]:
    vis = pickle.load(open(f, 'rb'))["visited"]
    cells = sorted(vis.values(), key=lambda v: v[0])
    print("==", f, "cells with certified minimum:", len(cells))
    for N in (10, 50, 200, 1000):
        c = Counter(str(v[1][5]) for v in cells[:N])
        print("  lowest %d cells: rho_6 values at the vertices (value: count):" % N, dict(c.most_common(6)))
    print("  rho_6 = 7 exactly among all cells:", sum(1 for v in cells if v[1][5] == 7), "of", len(cells), "| rho_6 or rho_5 in {7, 19/3, 57/7, 47/9}:", sum(1 for v in cells if v[1][5] in (7, F(19,3), F(57,7), F(47,9)) or v[1][4] in (7, F(19,3), F(57,7), F(47,9))))
    print("  rank-wise: cells whose lowest-ratio vertex has some reading equal to an integer >= 7:", sum(1 for v in cells if any(x.denominator == 1 and x >= 7 for x in v[1])))
    for v in cells[:15]: print("   %s = %.5f  rho=%s" % (v[0], float(v[0]), [str(x) for x in v[1]]))
    # lowest value among cells with rho_6 != 7
    o = [v for v in cells if v[1][5] != 7]
    print("  lowest cell with rho_6 != 7: %s = %.5f rho=%s" % (o[0][0], float(o[0][0]), [str(x) for x in o[0][1]]))
