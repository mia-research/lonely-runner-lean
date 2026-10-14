"""modgap_cluster_v1 (2026-10-06): the worked case.  For each of the 9 exceptions S = {m} + C (m = d_min, C the six readings above): in R-coordinates u = 7 m t (the 1/7 analogue of R = 8 d_min t) the clear arc of m is
exactly u in [1, 6] [P: ||m t|| >= 1/7 iff t in [(k + 1/7)/m, (k + 6/7)/m]].  Computed exactly (Fractions): (1) G = gcd(C), whether G divides m (the record's one_free: G >= 2 and G does not divide m would settle S);
(2) the lonely components of C alone at 1/7 in u in [0, 7] (the cluster's own 1/7-cascade restarted after each exit, as modgap_rigid_v1), each as (u_l, u_r) with the exact Fractions' decimals only for display;
(3) which components lie fully inside u in [1, 6] (then S is lonely at 1/7 on them by Fact A), how many, and the first; (4) S's own 1/7 landing in u.  Also, for the cluster spread d_7/d_2: whether it is <= 6 (R1 at 1/7 applies to C)."""
import sys, math
sys.path.insert(0, '.')
exec(open('modgap_dmin_perturb_v1.py').read().split("rnd = random.Random")[0])
from fractions import Fraction as F
from math import gcd
from functools import reduce
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
out = open('modgap_cluster_v1.out', 'w'); out.write(__doc__ + "\n")
for S in exc:
    m = S[0]; C = list(S[1:]); G = reduce(gcd, C)
    u = lambda t: 7 * m * t
    cs = comps(C, F(8, 7 * m))
    inside = [(l, r) for l, r in cs if u(l) >= 1 and u(r) <= 6]
    tt = casc7(list(S), F(1, 7 * m))
    out.write("S = %s\n  G = gcd(C) = %s (G divides m: %s; G >= 2: %s -> one_free applies: %s); spread d_7/d_2 <= 6: %s\n  cluster components with u in [0, 8]: %d; fully inside u in [1, 6]: %d; first component starts at u = %.6f; first inside component u in [%.6f, %.6f]; S's 1/7 landing u = %.6f\n" %
              (S if len(str(S[-1])) < 6 else '[%d-digit]' % len(str(S[-1])), (str(G) if len(str(G)) < 14 else '[%d-digit]' % len(str(G))), m % G == 0, G >= 2, G >= 2 and m % G != 0, F(S[-1], S[1]) <= 6,
               len(cs), len(inside), float(u(cs[0][0])), float(u(inside[0][0])) if inside else float('nan'), float(u(inside[0][1])) if inside else float('nan'), float(u(tt))))
out.close(); print(open('modgap_cluster_v1.out').read()[len(__doc__):])
