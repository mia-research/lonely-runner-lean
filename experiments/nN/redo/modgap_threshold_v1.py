"""modgap_threshold_v1 (2026-10-06): where does the arc criterion fail?  For a six-reading integer cluster C (least reading c1) and rho = c1/m, the first clear arc of m = c1/rho in tau = c1 t is [rho/7, 6 rho/7]; S = {m} + C is lonely at 1/7
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
SIG = [F(1, 50), F(1, 20), F(1, 10), F(1, 5), F(2, 5), F(1), F(2), F(5)]
out = open('modgap_threshold_v1.out', 'w'); out.write(__doc__ + "\n")
for fam in ('R', 'A'):
    out.write("\n==== family %s\n" % fam)
    for sig in SIG:
        res = []
        for _ in range(40):
            c1 = rnd.randrange(10 ** 5, 10 ** 6)
            if fam == 'R':
                C = tuple(sorted(rnd.sample(range(c1 + 1, int(c1 * (1 + sig)) + 1), 5) + [c1]))
            else:
                k = max(1, round(sig * c1 / 5)); C = tuple(c1 + i * k for i in range(6))
            if len(set(C)) != 6: continue
            bad = failing(C)
            delta = F(min(C[i + 1] - C[i] for i in range(5)), C[0])
            res.append((len(bad), bad[0] if bad else None, delta, F(C[-1], C[0]) - 1))
        nfail = sum(1 for r in res if r[0] > 0)
        worst = max(res, key=lambda r: r[0])
        out.write("  sigma = %-5s: %d clusters; clusters with a failing rho in [26, 200]: %d; the most failing grid points in one cluster: %d of %d (least failing rho %s; its delta = %s, sigma = %s); clusters failing at rho = 26: %d\n" %
                  (sig, len(res), nfail, worst[0], len(RHOS), worst[1], worst[2], worst[3], sum(1 for r in res if r[1] == 26)))
out.close(); print(open('modgap_threshold_v1.out').read()[len(__doc__):])
