# independent checks of the best exact tuple of k6map_walk_v1: K6 by two implementations, pointwise blocked test, allowed rho_7 set (R2) and direct cascade
import sys
exec(open('k6map_task1b_v1.py').read().split('rnd = random.Random')[0].replace('CAP = F(80)', 'CAP = F(400)'))
from k6map_lp_v1 import cell
V = [F(1), F(6559, 2279), F(26236, 6779), F(231, 47), F(26236, 4115), F(7)]
print("vertex tuple", [str(x) for x in V], [round(float(x), 5) for x in V])
a = K6(V); b = cc_ref(V, F(7)); print("K6 (sweep) == K6 (ceil_k6_lib clear_components):", a == b)
print("components:", [(str(x), str(y), str(y - x)) for x, y in a])
L = max(y - x for x, y in a); print("L_max =", L, "=", float(L), "| 2/(7 rho_6) =", F(2) / (7 * V[5]), float(F(2) / (7 * V[5])), "| ratio", L * 7 * V[5] / 2)
# every endpoint and midpoint is clear for readings 1..6 (exact), and a point just outside each component (when inside [1,7]) is blocked
def blk(R): return any(((R * r) % 8) < 1 or ((R * r) % 8) > 7 for r in V)
print("endpoints/midpoints clear:", all(not blk(x) and not blk(y) and not blk((x + y) / 2) for x, y in a))
eps = F(1, 10**12)
print("points eps outside each component blocked:", all(blk(x - eps) for x, y in a if x > 1) and all(blk(y + eps) for x, y in a if y < 7))
c, A = allowed(V, F(400)); print("allowed rho_7 set for the vertex tuple (cap 400):", [(str(l), str(h), round(float(l), 4), round(float(h), 4)) for l, h in A][:12], "count", len(A))
# an interior arrangement of the same cell: jitter and keep the same signature
import random
sig0 = cell([F(1)] + [x + F(1, 10**9) * (k + 1) * (-1) ** k for k, x in enumerate(V[1:])])
rnd = random.Random(3); found = None
for _ in range(2000):
    P = [F(1)] + [x + F(rnd.randint(-10**6, 10**6), 10**6) * F(1, 10**7) for x in V[1:]]
    if not all(p < q for p, q in zip(P, P[1:])): continue
    cc = cell(P)
    if cc and sig0 and cc[0] == sig0[0]: found = P; break
print("interior point of the cell found:", found is not None)
if found:
    P = found; print("interior tuple ratio:", float(ratio := (lambda W: max(y - x for x, y in W) * 7 * P[5] / 2)(K6(P))), "components", len(K6(P)))
    c, A = allowed(P, F(400)); print("allowed rho_7 (cap 400):", [(round(float(l), 4), round(float(h), 4)) for l, h in A], "count", len(A))
    for l, h in A[:3]:
        x = (l + h) / 2; R = path(P + [x])[1]; print("  midpoint rho_7 = %.4f: direct cascade landing %s (> 7: %s)" % (float(x), float(R), R > 7))
print("ratio-of-rho7-to-7rho6 for any allowed value:", [float(h / (7 * V[5])) for l, h in A][:5] if True else None)
