"""The reference for grids with laps: the grid's own class instants p/8 (a complete grid is globally isolated there,
laps or not: phi(8) and whole laps invisible).  For each deviated runner and each class p = 1,3,5,7: the first lonely
instant at or after p/8 - 1/64 (exact cascade from that start), its relative offset (t_p - p/8)/(p/8), and whether its
flank is the class-p circle neighbour (residue offset +-p).  Reported: the smallest |offset|/rho over the four classes
(the event read as a relocated grid event), which class carries it, and how that depends on the laps."""
import random
from fractions import Fraction as F
from collections import Counter
from nested_cascade_v1 import cascade_from
rnd = random.Random(47)
def run(Q, rho, trials=200):
    rel = []; cls = Counter(); nbr = 0; n = 0; lapspan = []
    for _ in range(trials):
        while True:
            laps = [rnd.randint(0, Q) for _ in range(8)]; u = [i + 8 * laps[i] for i in range(8)]
            if len(set(u)) == 8: break
        v = [100 + u[i] + rho * F(rnd.randint(-97, 97), 97) for i in range(8)]
        if len(set(v)) < 8: continue
        for k in range(8):
            ds = [abs(v[i] - v[k]) for i in range(8) if i != k]
            best = None
            for p in (1, 3, 5, 7):
                t = cascade_from(ds, F(p, 8) - F(1, 64))
                off = abs(t - F(p, 8)) / F(p, 8)
                if best is None or off < best[0]: best = (off, p, t)
            off, p, t = best; n += 1
            rel.append(off / rho); cls[p] += 1
            fl = [i for i in range(8) if i != k and (abs(v[i] - v[k]) * t) % 1 == F(1, 8)]
            nbr += any((i - k) % 8 in (p % 8, (8 - p) % 8) for i in fl)
            lapspan.append((max(laps) - min(laps), off / rho))
    rel.sort()
    by_span = {}
    for sp, x in lapspan: by_span.setdefault(min(sp, 12), []).append(x)
    print(f"  laps<= {Q:>2}, rho {str(rho):>5}: {n} runners; class carrying the nearest event {dict(sorted(cls.items()))}; "
          f"offset/rho median {float(rel[n//2]):.2f}, 95% {float(rel[19*n//20]):.2f}, max {float(rel[-1]):.2f}; "
          f"flank a class neighbour {nbr}/{n}")
    print("        max offset/rho by lap spread: " + ", ".join(f"{s}: {float(max(xs)):.1f}" for s, xs in sorted(by_span.items())))
for Q in (0, 1, 3, 10):
    for rho in (F(1, 64), F(1, 16), F(1, 8)):
        run(Q, rho)
