"""T4 adversarial search. Integer speeds, threshold 1/n, subject with nearest difference m. Lattice L: instants
t = p/(n·L·m), p = 1..n·L·m (one full period; exact). Runner at difference d is clear at p iff (d·p mod nLm) lies in
[L·m, (n−1)·L·m] (coord_iff). Lattice L is dead iff some d is a multiple of n·L·m. Gap = (least lattice with a lonely
instant) − (least live lattice). Hill-climb on speeds to maximise the gap (ties broken by the p needed), per n."""
import numpy as np, random, sys
from multiprocessing import Pool
def least_lonely(ds, m, n, Lmax=40):
    live = None
    for L in range(1, Lmax + 1):
        M = n * L * m
        if live is None and not any(d % M == 0 for d in ds): live = L
        p = np.arange(1, M + 1, dtype=np.int64)
        ok = np.ones(M, dtype=bool)
        for d in ds:
            r = (d * p) % M
            ok &= (r >= L * m) & (r <= (n - 1) * L * m)
            if not ok.any(): break
        if ok.any():
            return live, L, int(p[ok][0])
    return live, None, None
def score(v, n):
    best = (-1, 0, None)
    for i in range(len(v)):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        m = min(ds)
        live, L, p = least_lonely(ds, m, n)
        if L is None: return (999, 0, (i, live, L, p))
        g = (L - live, p)
        if g > best[:2]: best = (g[0], g[1], (i, live, L, p))
    return best
def climb(args):
    n, seed, vmax, iters = args
    rng = random.Random(seed)
    v = sorted(rng.sample(range(1, vmax + 1), n)); s = score(v, n)
    best = (s, list(v))
    for it in range(iters):
        w = list(v); j = rng.randrange(n)
        w[j] = max(1, min(vmax, w[j] + rng.choice([-3, -2, -1, 1, 2, 3, rng.randint(-40, 40)])))
        if len(set(w)) < n: continue
        w.sort(); sw = score(w, n)
        if sw[:2] >= s[:2] or rng.random() < 0.02:
            v, s = w, sw
            if s[:2] > best[0][:2]: best = (s, list(v))
    return best
if __name__ == '__main__':
    for n, vmax, iters, runs in ((5, 120, 1500, 32), (8, 120, 800, 32)):
        with Pool() as pool:
            res = pool.map(climb, [(n, 1000 + k, vmax, iters) for k in range(runs)])
        res.sort(key=lambda r: r[0][:2], reverse=True)
        print(f'n={n}: largest gaps found (gap, p needed, (subject index, first live, least lonely lattice, p), speeds):')
        seen = set()
        for (g, p, info), v in res[:8]:
            if tuple(v) in seen: continue
            seen.add(tuple(v)); print(f'   gap {g}  p {p}  {info}  {v}')
        sys.stdout.flush()
