# The HARD SET: arrangements whose landing is late.  For thresholds T in {2, 3, 5, 7, 9}: maximise the largest reading rho_7 subject to R* > T
# (float cascade with edge tolerance, exact confirmation).  If rho_7 stays small, late landings live in a bounded window.
import sys, random, math
from fractions import Fraction as F
exec(open('extremes_deep_v1.py').read().split('\nif __name__ ==')[0])
def obj(rho, T):
    R, n = fpath(rho)
    if n >= 10**6: return -1e9
    return rho[-1] if R > T else (R / T - 1.0) * 5.0 - 1.0
def run(T, W, restarts, iters, seed):
    rnd = random.Random(seed); best = (-1e9, None)
    for _ in range(restarts):
        rho = [1.0] + sorted(rnd.uniform(1.0, 9.0) for _ in range(6)); cur = obj(rho, T)
        for it in range(iters):
            new = list(rho); i = rnd.randrange(1, 7)
            scale = (W - 1) * (0.1 if it < iters // 3 else (0.02 if it < 2 * iters // 3 else 0.003))
            new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale))); new = [1.0] + sorted(new[1:])
            if len(set(new)) < 7: continue
            v = obj(new, T)
            if v >= cur or rnd.random() < math.exp((v - cur) / (0.3 * (1 - it / iters) + 1e-9)): rho, cur = new, v
        if cur > best[0]: best = (cur, rho)
    return best
if __name__ == "__main__":
    T = float(sys.argv[1]); W = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
    v, rho = run(T, W, 80, 2500, int(T * 10))
    rh = [F(x).limit_denominator(10**7) for x in rho]; steps, Rend = path(rh)
    print("landing R* > %-3.0f : largest rho_7 found %.4f  (exact R* = %.3f, moves %d)  readings %s" % (T, float(rh[-1]), float(Rend), len(steps), [round(x, 4) for x in rho]), flush=True)
