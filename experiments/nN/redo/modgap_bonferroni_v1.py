"""modgap_bonferroni_v1 (2026-10-06): the Bonferroni / Hunter-Worsley truncations for the arc statement, exact.  For six readings rho_1..rho_6 (rationals, rho_i >= 7), the bad sets B_i = {u in [1, 6] : ||rho_i u / 7|| < 1/7}
(open zones ((7j - 1)/rho_i, (7j + 1)/rho_i) cut to [1, 6]); all measures are exact Fractions (union of intervals by sweep).  Recorded per cluster: S1 = sum |B_i|, S2 = sum over pairs |B_i n B_j|, S3 = sum over triples
|B_i n B_j n B_k|, the Hunter-Worsley upper bound H = S1 - (maximum spanning tree of the pair intersections), the third-order upper bound U3 = S1 - S2 + S3, the true measure |union B_i|, and the arc length 5.  The claim a bound would
prove: |union| < 5 (the lonely set inside the arc has positive measure).  Counts of clusters with H < 5 and U3 < 5, and the least margins; also under the independence heuristic the same quantities (values 60/7, 20/49 per pair, ...) for comparison.
[PROVISIONAL: counting tool; supports: the question whether a pairwise (second-order) or triple (third-order) truncation can show |union B_i| < 5 uniformly; nothing here is an existence claim]
Populations: seeded (20261006) random rational clusters, rho_i uniform in [RMIN, RMIN + 13] with denominators up to 10^5, RMIN in {7, 10, 20, 50}, 150 clusters each; plus the two exact counterexamples of E416 (union = the whole arc)."""
import random, itertools
from fractions import Fraction as F
def zones(rho, lo=F(1), hi=F(6)):
    out = []; j = 1
    while True:
        a = F(7 * j - 1) / rho; b = F(7 * j + 1) / rho
        if a >= hi: break
        a2, b2 = max(a, lo), min(b, hi)
        if a2 < b2: out.append((a2, b2))
        j += 1
    return out
def measure(iv): return sum((b - a for a, b in iv), F(0))
def union(ivs):
    ivs = sorted(ivs); out = []
    for a, b in ivs:
        if out and a <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], b))
        else: out.append((a, b))
    return out
def inter(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        a = max(A[i][0], B[j][0]); b = min(A[i][1], B[j][1])
        if a < b: out.append((a, b))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def stats(rho):
    B = [union(zones(r)) for r in rho]; n = len(B)
    S1 = sum(measure(b) for b in B)
    pair = {(i, j): measure(inter(B[i], B[j])) for i, j in itertools.combinations(range(n), 2)}
    S2 = sum(pair.values())
    S3 = F(0)
    for i, j, k in itertools.combinations(range(n), 3):
        S3 += measure(inter(inter(B[i], B[j]), B[k]))
    # maximum spanning tree (Kruskal)
    parent = list(range(n))
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    mst = F(0)
    for (i, j), w in sorted(pair.items(), key=lambda kv: -kv[1]):
        a, b = find(i), find(j)
        if a != b: parent[a] = b; mst += w
    U = measure(union([iv for b in B for iv in b]))
    return S1, S2, S3, S1 - mst, S1 - S2 + S3, U
rnd = random.Random(20261006)
out = open('modgap_bonferroni_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("independence heuristic for an arc of length 5 (exact rationals): S1 = 60/7, S2 = 15 * 20/49 = 300/49, S3 = 20 * 40/343 = 800/343, S1 - S2 + S3 = %s, Hunter-Worsley = %s, true union = 5 (1 - (5/7)^6) = %s\n" %
          (F(60, 7) - F(300, 49) + F(800, 343), F(60, 7) - 5 * F(20, 49), 5 * (1 - F(5, 7) ** 6)))
for rmin in (7, 10, 20, 50):
    nH = nU = 0; worstH = worstU = None; n = 0; minU = None
    for _ in range(150):
        rho = [F(rnd.randrange(rmin * 10 ** 5, (rmin + 13) * 10 ** 5), 10 ** 5) for _ in range(6)]
        S1, S2, S3, H, U3, U = stats(rho); n += 1
        nH += H < 5; nU += U3 < 5
        worstH = H if worstH is None else min(worstH, H)
        worstU = U3 if worstU is None else max(worstU, U3)
        minU = U if minU is None else max(minU, U)
    out.write("rho_min = %2d: %d clusters; Hunter-Worsley bound < 5 in %d (least value %s); third-order U3 < 5 in %d (greatest value %s); the greatest true union measure %s\n" %
              (rmin, n, nH, '%s' % worstH, nU, '%s' % worstU, '%s' % minU))
ce = [F(5), F(1412741, 261840), F(525941, 88195), F(5575838, 821095), F(189353, 24304), F(7946201, 940370)]
S1, S2, S3, H, U3, U = stats(ce)
out.write("E416 counterexample: S1 = %s, S2 = %s, S3 = %s, Hunter-Worsley %s, U3 %s, true union %s (the arc is covered when the union equals 5)\n" % (S1, S2, S3, H, U3, U))
out.close(); print(open('modgap_bonferroni_v1.out').read()[len(__doc__):])
