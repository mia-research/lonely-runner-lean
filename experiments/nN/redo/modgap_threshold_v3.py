"""modgap_threshold_v3 (2026-10-06): where does the arc criterion fail?  For a six-reading integer cluster C (least reading c1) and rho = c1/m, the first clear arc of m = c1/rho in tau = c1 t is [rho/7, 6 rho/7]; S = {m} + C is lonely at 1/7
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
RHOS = [F(8 + j, 4) for j in range(0, 4 * 26 - 8 + 1)]   # 2, 2.25, ..., 26
def failing(C):
    c1 = min(C); cs = [(l * c1, r * c1) for l, r in comps(list(C), F(6 * 26, 7 * c1))]
    bad = []
    for rho in RHOS:
        lo, hi = rho / 7, 6 * rho / 7
        if not any(l >= lo and r <= hi for l, r in cs): bad.append(rho)
    return bad
rnd = random.Random(20261006)
out = open('modgap_threshold_v3.out', 'w'); out.write(__doc__ + "\n")
out.write("v3: rho swept DOWNWARD, 2 <= rho <= 26 in steps of 1/4 (the arc [rho/7, 6 rho/7] in tau = c1 t; rho < 7/6 means the arc starts before the cluster's first lonely instant).  Mixed populations: (R) six distinct integers uniform in [c1, c1 (1+sigma)] (sigma in {1/100, 1/10, 1/2, 2, 5}, c1 in [10^4, 10^6]), (A) AP clusters c1 + i k, k in {1, 3, 8, 21, 59}, c1 in {1000, 5000, 20000}; 40 R-clusters per sigma.\n")
tot = collections.Counter(); fails = []
for sig in (F(1, 100), F(1, 10), F(1, 2), F(2), F(5)):
    for _ in range(40):
        c1 = rnd.randrange(10 ** 4, 10 ** 6); hi = max(c1 + 8, int(c1 * (1 + sig)))
        C = tuple(sorted(rnd.sample(range(c1 + 1, hi + 1), 5) + [c1]))
        if len(set(C)) != 6: continue
        bad = failing(C); tot['R clusters'] += 1
        for r in bad: tot[('R failing at rho', r)] += 1
        if bad: fails.append(('R', sig, C[0], bad[0], bad[-1], len(bad)))
for c1 in (1000, 5000, 20000):
    for k in (1, 3, 8, 21, 59):
        C = tuple(c1 + i * k for i in range(6)); bad = failing(C); tot['A clusters'] += 1
        for r in bad: tot[('A failing at rho', r)] += 1
        if bad: fails.append(('A', F(k * 5, c1), C[0], bad[0], bad[-1], len(bad)))
out.write("clusters: R %d, A %d.  Clusters with a failing rho in [2, 26]: %d\n" % (tot['R clusters'], tot['A clusters'], len(fails)))
byr = collections.Counter()
for k, v in tot.items():
    if isinstance(k, tuple): byr[k[1]] += v
for r in sorted(byr): out.write("  rho = %-6s: %d failing clusters (of %d)\n" % (r, byr[r], tot['R clusters'] + tot['A clusters']))
out.write("the greatest rho at which any cluster fails: %s\n" % (max(byr) if byr else None))
for f in fails[:12]: out.write("  e.g. %s sigma %s c1 %d: least failing rho %s, greatest %s, %d grid points\n" % f)
out.close(); print(open('modgap_threshold_v3.out').read()[len(__doc__):][:4500])
