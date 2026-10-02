# Along a linear deformation s in [0,1] (k movers, others frozen) the cascade's MOVE SEQUENCE (setter, lap per move) is piecewise constant.
# Claim under test: it changes only where two zone edges cross, i.e. (8j+a)/rho_x(s) = (8j'+a')/rho_y(s) with a, a' in {-1, +1}
# (zone start / zone end), j, j' laps, at least one of x, y a mover (or the start 1/rho_min).  Observed change points are located
# by dense sampling and exact bisection; each is compared with the predicted crossing set.  Anything not predicted is printed.
import sys, random, bisect
from fractions import Fraction as F
from collections import Counter
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
RMAXP = F(14)
def label(rhos):
    steps, Rend = path(rhos)
    return tuple((mv["setter"], mv["lap"]) for mv in steps) + (("end",),)
def crossings(p, q, movers):
    n = len(p); out = []
    J = [int(max(p[i], p[i] + q[i]) * RMAXP / 8) + 2 for i in range(n)]
    edges = [(x, a, j) for x in range(n) for a in (-1, 1) for j in range(J[x] + 1) if 8 * j + a > 0 or (a == 1 and j == 0)]
    for ia, (x, a, j) in enumerate(edges):
        for (y, b, k) in edges[ia + 1:]:
            if x == y or (x not in movers and y not in movers): continue
            num = (8 * k + b) * p[x] - (8 * j + a) * p[y]
            den = (8 * j + a) * q[y] - (8 * k + b) * q[x]
            if den == 0: continue
            s = num / den
            if 0 <= s <= 1: out.append((float(s), (x, a, j), (y, b, k)))
    out.sort(); return out
def observed(p, q, N=1200):
    rho = lambda s: [p[i] + q[i] * s for i in range(len(p))]
    labs = [label(rho(F(i, N))) for i in range(N + 1)]
    pts = []
    for i in range(N):
        if labs[i] != labs[i + 1]:
            lo, hi = F(i, N), F(i + 1, N); ll = labs[i]
            for _ in range(60):
                mid = (lo + hi) / 2
                if label(rho(mid)) == ll: lo = mid
                else: hi = mid
            pts.append((float((lo + hi) / 2), labs[i], labs[i + 1]))
    return pts
if __name__ == "__main__":
    nrun = int(sys.argv[1]); rnd = random.Random(311); tot = explained = 0; unexplained = []; kinds = Counter()
    bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("g14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]), ("3AP", [F(3 * x) for x in range(1, 8)]),
             ("mixed", [F(x, 10) for x in (10, 17, 29, 41, 58, 77, 93)])]
    for name, base in bases:
        for r in range(nrun if name in ("AP", "mixed") else max(3, nrun // 2)):
            k = rnd.choice((1, 2, 3, 4)); movers = tuple(sorted(rnd.sample(range(7), k)))
            p = list(base); q = [F(0)] * 7
            for m in movers: q[m] = max(F(3, 10), base[m] + F(rnd.randint(-150, 450), 100)) - base[m]
            pred = crossings(p, q, movers); ps = [x[0] for x in pred]
            for s_obs, l0, l1 in observed(p, q):
                tot += 1
                i = bisect.bisect_left(ps, s_obs - 1e-9)
                hit = []
                while i < len(ps) and ps[i] <= s_obs + 1e-9: hit.append(pred[i]); i += 1
                if hit:
                    explained += 1
                    for (_, e1, e2) in hit[:1]:
                        t = lambda e: ("mover" if e[0] in movers else "frozen") + (" end" if e[1] == 1 else " start")
                        kinds[tuple(sorted((t(e1), t(e2))))] += 1
                else: unexplained.append((name, movers, [round(float(q[m]), 2) for m in movers], round(s_obs, 6), l0, l1))
    print("observed changes of the move sequence:", tot, "; explained by a predicted edge crossing:", explained, "; unexplained:", len(unexplained))
    for u in unexplained[:20]: print("  UNEXPLAINED", u)
    print("types of the first matching crossing:", sorted(kinds.items(), key=lambda x: -x[1]))
