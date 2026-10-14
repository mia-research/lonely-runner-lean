"""T4, second search. Quantity: least lonely lattice L* against the proved first-live bound B = floor(s_max/n) + 1
(s_max = d_max/m). Maximise L* − B and L*/B separately; also report L* against s_max. Exact integer arithmetic as in
t4_gap_adversarial_v1.py. Speeds to 300."""
import numpy as np, random, sys
from multiprocessing import Pool
from t4_gap_adversarial_v1 import least_lonely
from fractions import Fraction as F
def worst(v, n, key):
    out = None
    for i in range(len(v)):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        m = min(ds)
        live, L, p = least_lonely(ds, m, n, Lmax=80)
        if L is None: return (1e9, (i, live, None, None, None))
        smax = F(max(ds), m); B = int(smax // n) + 1
        k = key(L, B, smax)
        if out is None or k > out[0]: out = (k, (i, live, L, B, float(smax), p))
    return out
KEYS = {'excess': lambda L, B, s: L - B, 'ratio': lambda L, B, s: L / B}
def climb(args):
    n, seed, vmax, iters, kname = args
    key = KEYS[kname]; rng = random.Random(seed)
    v = sorted(rng.sample(range(1, vmax + 1), n)); s = worst(v, n, key); best = (s, v)
    for _ in range(iters):
        w = list(v); j = rng.randrange(n)
        w[j] = max(1, min(vmax, w[j] + rng.choice([-2, -1, 1, 2, rng.randint(-60, 60)])))
        if len(set(w)) < n: continue
        w.sort(); sw = worst(w, n, key)
        if sw[0] >= s[0] or rng.random() < 0.02:
            v, s = w, sw
            if s[0] > best[0][0]: best = (s, list(v))
    return best
if __name__ == '__main__':
    for n, iters in ((5, 1200), (8, 600)):
        for kname in ('excess', 'ratio'):
            with Pool() as pool:
                res = pool.map(climb, [(n, 7000 + k, 300, iters, kname) for k in range(32)])
            res.sort(key=lambda r: r[0][0], reverse=True)
            print(f'n={n}, maximise {kname}: top (value, (subject, first live, least lonely L*, bound B, s_max, p), speeds)')
            for (val, info), v in res[:5]:
                print(f'   {val:.3f}  {info}  {v}')
            sys.stdout.flush()
