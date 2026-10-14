"""modgap_gap_cluster_v1 (2026-10-06): the recurrence of a six-reading cluster's lonely set at 1/7.  Seeded (20261006) random integer clusters C = six distinct integers in [N, SP*N] (spread at most SP; SP = 6 so that R1 at 1/7 applies;
SP = 8 also), N in {10^3, 10^4, 10^6, 10^9}.  For each cluster the lonely components at 1/7 over tau = c_1 t in [1/7, TAU_MAX] (TAU_MAX = 40) as exact Fractions; the gaps between the end of one component and the start of the next, and the
start of the first component after tau = 1/7 ... recorded in units of tau (1 unit = one period of the least reading); also the number of components per unit tau.  Reported per (N, SP): the maximum gap and its
distribution, the minimum number of components in [1, 40] over the sample.  Also the adversarial commensurable clusters: multiples of a common factor and AP-like clusters (c_i = c_1 + i k with k small).  Exact."""
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
rnd = random.Random(20261006); TAU = 40
out = open('modgap_gap_cluster_v1.out', 'w'); out.write(__doc__ + "\n")
def stats(name, clusters):
    mg = F(0); worst = None; mincnt = 10 ** 9; hist = collections.Counter()
    for C in clusters:
        c1 = min(C); cs = comps(list(C), F(TAU, c1))
        tau = [(l * c1, r * c1) for l, r in cs]
        gaps = [tau[i + 1][0] - tau[i][1] for i in range(len(tau) - 1)]
        gaps = [g for g in gaps if g >= 0]
        g = max(gaps) if gaps else F(TAU)
        if g > mg: mg = g; worst = C
        hist[int(g * 4)] += 1                     # quarters of a period
        n = len([1 for a, b in tau if a >= 1])
        mincnt = min(mincnt, n)
    out.write("%s: %d clusters; maximum gap between consecutive components = %s (about %.3f periods); components with tau >= 1: at least %d; gap histogram (quarter periods): %s\n  worst cluster: %s\n" %
              (name, len(clusters), mg, float(mg), mincnt, dict(sorted(hist.items())), worst if worst is None or len(str(max(worst))) < 14 else '[big]'))
for N in (10 ** 3, 10 ** 4, 10 ** 6, 10 ** 9):
    for SP in (6, 8):
        cl = []
        while len(cl) < 400:
            C = tuple(sorted(rnd.sample(range(N, SP * N + 1), 6)))
            cl.append(C)
        stats("random N=%d spread<=%d" % (N, SP), cl)
adv = []
for k in range(1, 60):
    for c1 in (1000, 5000):
        adv.append(tuple(c1 + i * k for i in range(6)))
stats("AP-like c_1 + i k (k = 1..59, c_1 in {1000, 5000})", adv)
adv2 = []
for g in (7, 14, 21, 70, 120):
    for _ in range(60):
        base = sorted(rnd.sample(range(150, 900), 6)); adv2.append(tuple(g * b for b in base))
stats("common factor g in {7,14,21,70,120} times a random cluster", adv2)
out.close(); print(open('modgap_gap_cluster_v1.out').read()[len(__doc__):])
