"""modgap_threshold_v2 (2026-10-06): where does the arc criterion fail?  For a six-reading integer cluster C (least reading c1) and rho = c1/m, the first clear arc of m = c1/rho in tau = c1 t is [rho/7, 6 rho/7]; S = {m} + C is lonely at 1/7
on any lonely component of C fully inside the arc (Lean: lonely_cons_of_arc).  For each cluster: the set of rho in the grid 26, 26.5, ..., 200 for which NO component of C at 1/7 lies fully inside [rho/7, 6 rho/7]; recorded as the
number of failing grid points and the least failing rho.  Parameters (exact): sigma = c6/c1 - 1, delta = (least consecutive difference)/c1.  Families: (R) six distinct integers uniform in [c1, c1 (1 + sigma)], sigma in
{1/50, 1/20, 1/10, 1/5, 2/5, 1, 2, 5}; (A) AP c1 + i k with k = round(sigma c1 / 5).  c1 random in [10^5, 10^6], seeded 20261006, 40 clusters per cell.  Exact (Fractions); only the grid and the buckets are chosen here."""
import sys, math, random, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def casc7(T, t):
    while True:
        B = [x for x in T if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
def comps(T, limit):
    t = casc7(T, F(1, 7 * min(T))); out = []
    while t <= limit:
        best = None
        for x in T:
            N = math.ceil(x * t - F(6, 7)); e = (N + F(6, 7)) / x
            if best is None or e < best[0]: best = (e, [x])
            elif e == best[0]: best[1].append(x)
        r, cl = best; out.append((t, r))
        Fs = [F(7 * (math.floor(x * r - F(6, 7)) + 1) + 1, 7 * x) for x in cl]
        t = casc7(T, max(Fs))
    return out
RHOS = [F(52 + j, 2) for j in range(0, 2 * (200 - 26) + 1)]   # 26, 26.5, ..., 200
def failing(C):
    c1 = min(C); cs = [(l * c1, r * c1) for l, r in comps(list(C), F(6 * 200, 7 * c1))]
    bad = []
    for rho in RHOS:
        lo, hi = rho / 7, 6 * rho / 7
        if not any(l >= lo and r <= hi for l, r in cs): bad.append(rho)
    return bad
rnd = random.Random(20261006)
out = open('modgap_threshold_v2.out', 'w'); out.write(__doc__ + "\n")
out.write("v2: the small-sigma regime.  Family A: c1 in {1000, 2000, 5000, 10000, 20000}, k in {1, 2, 3, 5, 8, 13, 21, 37, 59} (AP c1 + i k); family R: six distinct integers uniform in [c1, c1 (1 + sigma)], sigma in {1/1000, 1/300, 1/100}, c1 in [5000, 50000], 40 each.\n")
rows = []
for c1 in (1000, 2000, 5000, 10000, 20000):
    for k in (1, 2, 3, 5, 8, 13, 21, 37, 59):
        C = tuple(c1 + i * k for i in range(6))
        bad = failing(C); rows.append((F(C[-1], C[0]) - 1, F(k, c1), len(bad), bad[0] if bad else None, bad[-1] if bad else None, C))
rows.sort()
out.write("\n==== A: (sigma, delta, failing grid points of %d, least failing rho, greatest failing rho, cluster) sorted by sigma\n" % len(RHOS))
for r in rows: out.write("  sigma = %-12s delta = %-10s failing %3d  least %-6s greatest %-6s  %s\n" % (r[0], r[1], r[2], r[3], r[4], r[5]))
out.write("\n==== R\n")
for sig in (F(1, 1000), F(1, 300), F(1, 100)):
    res = []
    for _ in range(40):
        c1 = rnd.randrange(5000, 50000)
        hi = max(c1 + 8, int(c1 * (1 + sig)))
        C = tuple(sorted(rnd.sample(range(c1 + 1, hi + 1), 5) + [c1]))
        if len(set(C)) != 6: continue
        bad = failing(C); res.append((len(bad), bad[0] if bad else None, F(C[-1], C[0]) - 1))
    out.write("  sigma = %-6s: %d clusters; with a failing rho: %d; most failing grid points: %d; clusters failing at rho = 26: %d\n" %
              (sig, len(res), sum(1 for r in res if r[0]), max(r[0] for r in res), sum(1 for r in res if r[1] == 26)))
out.close(); print(open('modgap_threshold_v2.out').read()[len(__doc__):])
