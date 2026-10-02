# Case C (a slow runner d_min = 1 below a six-reading cluster whose smallest reading is c, c >= 9).  The slow runner is clear for R in [1, 7].
# So the arrangement lands inside d_min's first clear window iff the CLUSTER has a lonely point R in [1, 7], i.e. R' = c R in [c, 7c].
# Quantity: q = (first lonely R' >= c of the six cluster readings) / c.  q <= 7 means the cluster alone settles it.  Adversarial search for max q.
import sys, random, math
exec(open('cluster_gap_v1.py').read().split('\nif __name__ ==')[0])
def first_after(rhos, c, RMAX):
    L = lonely(rhos, RMAX)
    for lo, hi in L:
        if hi >= c: return max(lo, c)
    return None
def q_of(rhos, c):
    RMAX = 70 * c
    f = first_after(rhos, c, RMAX)
    return 1e9 if f is None else f / c
def search(c, W, restarts, iters, seed):
    rnd = random.Random(seed); best = (-1, None)
    for _ in range(restarts):
        rho = [1.0] + sorted(rnd.uniform(1.0, W) for _ in range(5)); cur = q_of(rho, c)
        for it in range(iters):
            new = list(rho); i = rnd.randrange(1, 6)
            scale = (W - 1) * (0.15 if it < iters // 3 else (0.02 if it < 2 * iters // 3 else 0.003))
            new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale))); new = [1.0] + sorted(new[1:])
            if len(set(new)) < 6: continue
            v = q_of(new, c)
            if v >= cur or rnd.random() < math.exp((min(v, 50) - min(cur, 50)) / (0.3 * (1 - it / iters) + 1e-9)): rho, cur = new, v
        if cur > best[0]: best = (cur, rho)
    return best
if __name__ == "__main__":
    for c in (9, 16, 30):
        for W in (7, 25):
            v, rho = search(c, W, 20, 800, 11 + c + W)
            print("cluster min c = %-3d spread <= %-3d : sup q = (first lonely R' >= c)/c found %.3f  (%s)   readings %s" % (c, W, v, "within [c, 7c]" if v <= 7 else "NOT within the slow runner's first clear window", [round(x, 4) for x in rho]), flush=True)
