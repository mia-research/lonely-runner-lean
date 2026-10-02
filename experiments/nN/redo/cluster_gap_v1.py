# Bounded-gap question for SIX readings (the cluster of a "slow runner below a cluster" arrangement).
# Normalise the cluster's smallest reading to 1 (R' = 8 c t).  L = lonely set of the six readings in R' in [1, RMAX] (floats, interval intersection).
# gap(L) = largest distance between consecutive lonely points (also from R' = 1 to the first one, and from the last to RMAX).  Adversarial search for its maximum.
import sys, random, math
def windows(r, RMAX):
    out = []; j = 0
    while (8 * j + 1) / r <= RMAX:
        lo = (8 * j + 1) / r; hi = min((8 * j + 7) / r, RMAX); out.append((lo, hi)); j += 1
    return out
def inter(A, B):
    out = []; i = k = 0
    while i < len(A) and k < len(B):
        lo = max(A[i][0], B[k][0]); hi = min(A[i][1], B[k][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[k][1]: i += 1
        else: k += 1
    return out
def lonely(rhos, RMAX):
    L = windows(rhos[0], RMAX)
    for r in rhos[1:]:
        L = inter(L, windows(r, RMAX))
        if not L: return []
    L.sort(); out = []
    for lo, hi in L:
        if out and lo <= out[-1][1] + 1e-12: out[-1] = (out[-1][0], max(out[-1][1], hi))
        else: out.append((lo, hi))
    return out
def maxgap(rhos, RMAX):
    L = lonely(rhos, RMAX)
    if not L: return RMAX
    g = L[0][0] - 1.0; 
    for a, b in zip(L, L[1:]): g = max(g, b[0] - a[1])
    return max(g, RMAX - L[-1][1])
def search(W, RMAX, restarts, iters, seed):
    rnd = random.Random(seed); best = (-1, None)
    for _ in range(restarts):
        rho = [1.0] + sorted(rnd.uniform(1.0, W) for _ in range(5)); cur = maxgap(rho, RMAX)
        for it in range(iters):
            new = list(rho); i = rnd.randrange(1, 6)
            scale = (W - 1) * (0.15 if it < iters // 3 else (0.02 if it < 2 * iters // 3 else 0.003))
            new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale))); new = [1.0] + sorted(new[1:])
            if len(set(new)) < 6: continue
            v = maxgap(new, RMAX)
            if v >= cur or rnd.random() < math.exp((v - cur) / (0.3 * (1 - it / iters) + 1e-9)): rho, cur = new, v
        if cur > best[0]: best = (cur, rho)
    return best
if __name__ == "__main__":
    for W, RMAX in ((7, 40), (9, 40), (25, 60), (60, 60)):
        v, rho = search(W, RMAX, 25, 1200, 7 + W)
        print("six readings, rho_min = 1, rho_max <= %-3d, lonely set scanned on R' in [1, %d]: largest gap found %.3f   readings %s" % (W, RMAX, v, [round(x, 4) for x in rho]), flush=True)
