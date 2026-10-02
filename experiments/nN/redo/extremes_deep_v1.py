# Deeper adversarial search in the one-lap window rho_7 <= 9 (and 7 < rho_7 <= 9 forced, since rho_7 <= 7 is lonely at R = 1).
# Float cascade with edge tolerance (a position within 1e-9 of 1 or 7 is clear), then EXACT confirmation of the best.  Reports max landing R*, max moves.
import sys, random, math
from fractions import Fraction as F
TOL = 1e-9
def fpath(rho):
    R = 1.0; n = 0
    while True:
        best = None
        for r in rho:
            p = (R * r) % 8.0
            if p < 1.0 - TOL or p > 7.0 + TOL:
                j = round(R * r / 8.0); e = (8 * j + 1) / r
                if e > R + 1e-12 and (best is None or e > best): best = e
        if best is None: return R, n
        R = best; n += 1
        if n > 300: return R, 10**6
def search(restarts, iters, key, seed, W=9.0, lo7=7.0):
    rnd = random.Random(seed); out = []
    for _ in range(restarts):
        rho = [1.0] + sorted(rnd.uniform(1.0, W) for _ in range(6)); rho[-1] = rnd.uniform(lo7, W); rho = [1.0] + sorted(rho[1:])
        cur = key(*fpath(rho))
        for it in range(iters):
            new = list(rho); i = rnd.randrange(1, 7)
            scale = (W - 1) * (0.15 if it < iters // 4 else (0.03 if it < iters // 2 else (0.005 if it < 3 * iters // 4 else 0.0007)))
            new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale)))
            new = [1.0] + sorted(new[1:])
            if new[-1] < lo7 or len(set(new)) < 7: continue
            R, n = fpath(new)
            if n >= 10**6: continue
            v = key(R, n)
            if v >= cur or rnd.random() < math.exp((v - cur) / (0.4 * (1 - it / iters) + 1e-9)): rho, cur = new, v
        out.append((cur, rho))
    out.sort(key=lambda t: -t[0]); return out
if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
    for name, key in (("landing R*", lambda R, n: R), ("number of moves", lambda R, n: n + 0.0001 * R)):
        res = search(60, 3000, key, seed)
        print("== maximise %s over the window 7 < rho_7 <= 9 (seed %d); top 4 by float, exact-confirmed:" % (name, seed), flush=True)
        for v, rho in res[:4]:
            rh = [F(x).limit_denominator(10**7) for x in rho]
            steps, Rend = path(rh)
            print("   exact: R* = %9.4f, moves = %3d, readings %s" % (float(Rend), len(steps), [round(x, 4) for x in rho]), flush=True)
