"""The Case C cascades in which some runner sets more than once (case_c_cascade_path_v1): which family, the gaps, the
repeating runner, and the six-block's structure (tightest five-cluster spread sigma5 against d_2; deviations from the
progression at scale d_2).  Exact."""
from fractions import Fraction as F
from math import floor
from itertools import combinations
from collections import Counter
from arrangement_lib import nd
import case_c_map_v1 as cm
from case_c_cascade_path_v1 import path
cm.rnd.seed(26)
rows = []
for shape in ('even', 'clumped+outliers', 'even+clump'):
    for g1div in (30, 100, 1000):
        n = 0
        while n < 150:
            g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
            if g1 + W6 <= 22 * g1: continue
            V = cm.arrangement([g1] + g)
            if len(set(V)) < 8: continue
            n += 1
            mv, ms, wait, bnd, _ = path(V)
            if ms >= 2:
                ds = sorted(v - V[0] for v in V[1:]); six = ds[1:]
                s5 = min(max(c) - min(c) for c in combinations(six, 5))
                rows.append((shape, g1div, ms, mv, float(wait), g, float(F(s5, six[0]))))
for r in rows:
    print(f"  {r[0]:17s} W/{r[1]:<5d} max sets {r[2]} moves {r[3]:>2d} wait {r[4]:.3f}  gaps g2..g7 {r[5]}  sigma5/d2 {r[6]:.4f}")
print("families of the repeat-setter cases:", dict(Counter((r[0]) for r in rows)))
