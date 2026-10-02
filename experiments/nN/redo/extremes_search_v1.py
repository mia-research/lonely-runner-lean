# Adversarial search for the HARDEST arrangements: maximise the landing R* (and the number of moves) over readings 1 = rho_1 < ... < rho_7 <= W.
# Float cascade for the search, exact Fractions to confirm the best.  Windows W = 9, 17, 25, 49, 97.
import sys, random, math
from fractions import Fraction as F
def fpath(rho):
    R = 1.0; n = 0
    while True:
        best = None
        for r in rho:
            p = (R * r) % 8.0
            if p < 1.0 or p > 7.0:
                j = round(R * r / 8.0); e = (8 * j + 1) / r
                if best is None or e > best: best = e
        if best is None: return R, n
        R = best; n += 1
        if n > 400: return R, n
def exact_path(rho):
    exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0], globals())
    steps, Rend = path([F(x).limit_denominator(10**7) for x in rho]); return Rend, len(steps), steps
def search(W, restarts, iters, key, seed):
    rnd = random.Random(seed); best = (-1, None)
    for _ in range(restarts):
        rho = [1.0] + sorted(rnd.uniform(1.0, W) for _ in range(6))
        cur = key(*fpath(rho))
        T0 = 0.5
        for it in range(iters):
            new = list(rho); i = rnd.randrange(1, 7)
            scale = (W - 1) * (0.2 if it < iters // 3 else (0.03 if it < 2 * iters // 3 else 0.004))
            new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale)))
            new = [1.0] + sorted(new[1:])
            if len(set(new)) < 7: continue
            v = key(*fpath(new))
            if v >= cur or rnd.random() < math.exp((v - cur) / (T0 * (1 - it / iters) + 1e-9)):
                rho, cur = new, v
        if cur > best[0]: best = (cur, rho)
    return best
if __name__ == "__main__":
    for W in (9, 17, 25, 49, 97):
        for name, key in (("landing R*", lambda R, n: R), ("moves", lambda R, n: n + 0.001 * R)):
            v, rho = search(W, 40, 1500, key, 100 + W)
            R, n = fpath(rho)
            print("window rho_7 <= %-3d maximise %-10s: best R* = %8.4f, moves = %3d, readings %s" % (W, name, R, n, [round(x, 4) for x in rho]), flush=True)
