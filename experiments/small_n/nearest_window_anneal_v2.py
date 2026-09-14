"""Heavier adversarial search, n = 5..9: largest final nearest reading; how many laps the nearest runner passes
(window index = floor((reading + 1) / n)); runs where the nearest runner is in the way at some iterate."""
from fractions import Fraction as F
import math, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from multiprocessing import Pool
from nearest_window_anneal_v1 import chain
def run(args):
    n, seed, iters = args
    rng = random.Random(seed); k = n - 2
    cur = [1 + F(rng.randint(0, rng.choice([2000, 5000, 8000])), 1000) for _ in range(k)]
    cs, cn, _ = chain([F(1)] + sorted(cur), n); best = (cs, cn, list(cur)); hit = None
    for it in range(iters):
        T = 0.5 * (1 - it / iters) + 0.002
        step = F(rng.choice([1, 10, 100, 1000]), 1000)
        new = [max(F(1), x + step * F(rng.randint(-100, 100), 100)) if rng.random() < 0.5 else x for x in cur]
        ns, nn, _ = chain([F(1)] + sorted(new), n)
        if ns >= cs or rng.random() < math.exp(float(ns - cs) / T):
            cur, cs, cn = new, ns, nn
            if cs > best[0]: best = (cs, cn, list(cur))
            if cn and (hit is None or cs > hit[0]): hit = (cs, list(cur))
    return n, best, hit
if __name__ == '__main__':
    jobs = [(n, 1000 + s, 6000) for n in (5, 6, 7, 8, 9) for s in range(40)]
    with Pool() as p: res = p.map(run, jobs)
    for n in (5, 6, 7, 8, 9):
        rs = [(b, h) for m, b, h in res if m == n]
        top = max((b for b, _ in rs), key=lambda b: b[0]); hits = [h for _, h in rs if h]
        print(f'n={n}: largest nearest reading {float(top[0]):.4f} (first window edge {n-1}, second {2*n-1}); '
              f'runs with the nearest runner in the way: {len(hits)} of {len(rs)}; ratios {[round(float(x),4) for x in sorted(top[2])]}')
