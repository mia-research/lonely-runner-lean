"""Five differences (nearest a; others by speed b < c < d < e) at n = 7..10: longest chain, most settings by the
slowest runner b, largest nearest reading; random + near-rational + annealing on length and on b-settings."""
from fractions import Fraction as F
import math, random
from multiprocessing import Pool
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; w = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, i
        if who is None: return w, t
        w.append(who); t = best
        if len(w) > 400: return w, t
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4)]
def job(args):
    n, seed = args
    rng = random.Random(seed)
    best = dict(L=0, B=0, R=F(0), exL=None, exB=None, near=0)
    def rec(r):
        r = sorted(max(F(1), x) for x in r)
        if len(set(r)) < 4: return 0, 0
        ds = [F(1)] + r
        w, t = chain(ds, n)
        L = len(w); B = w.count(1)
        if L > best['L']: best['L'], best['exL'] = L, ([str(x) for x in ds], ''.join('abcde'[i] for i in w))
        if B > best['B']: best['B'], best['exB'] = B, ([str(x) for x in ds], ''.join('abcde'[i] for i in w))
        best['R'] = max(best['R'], n * t); best['near'] += (0 in w)
        return L, B
    for _ in range(4000):
        if rng.random() < 0.5:
            M = rng.choice([3, 10, 50, 300]); rec([1 + F(rng.randint(0, 10**5), 10**5) * M for _ in range(4)])
        else:
            b = 1 + F(rng.randint(0, 60000), 1000)
            rec([b] + [b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000) for _ in range(3)])
    for idx in (0, 1):
        cur = [1 + F(rng.randint(0, 6000), 1000) for _ in range(4)]; cs = rec(cur)[idx]
        for it in range(2500):
            step = F(rng.choice([1, 10, 100, 1000]), 1000)
            new = [max(F(1), x + step * F(rng.randint(-100, 100), 100)) for x in cur]
            ns = rec(new)[idx]
            if ns >= cs or rng.random() < 0.03: cur, cs = new, ns
    return n, best
if __name__ == '__main__':
    with Pool() as p: res = p.map(job, [(n, s) for n in (7, 8, 9, 10) for s in range(12)])
    for n in (7, 8, 9, 10):
        S = [b for m, b in res if m == n]
        L = max(S, key=lambda b: b['L']); B = max(S, key=lambda b: b['B'])
        print(f"n={n}: longest chain {L['L']} {L['exL']}; most settings by the slowest runner {B['B']} {B['exB']}; "
              f"largest nearest reading {float(max(b['R'] for b in S)):.3f}; nearest sets a move in {sum(b['near'] for b in S)} chains")
