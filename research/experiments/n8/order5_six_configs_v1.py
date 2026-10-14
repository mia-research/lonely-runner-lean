"""(1) The six order-5 two-return difference sets, move by move: setter, lap, instant, the setter's reading s_x at the current
scale, its N (so the new slot is 5N+1), the shift g = 5N+1 − s_x, the depth δ = distance of s_x from the nearest multiple of 5,
and the ratios of the other runners to the setter.
(2) Nested returns: over every 5-subset of [1,24], every runner, for each pair of consecutive settings of a runner x at laps
(Q, Q'), whether any intervening setter y itself returns inside that stretch, and if so whether y's laps are strictly below Q."""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
n = 5; th = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def walk(ds):
    t = th / min(ds); steps = []
    while True:
        best = t; who = None
        for idx, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (idx, k, t)
        if who is None: return steps, t
        steps.append(who); t = best
SETS = [[1,7,9,20], [1,9,11,20], [2,8,12,21], [1,8,10,22], [3,10,15,26], [1,13,15,28]]
print('(1) the six two-return difference sets')
for S in SETS:
    ds = [F(x) for x in S]; steps, tend = walk(ds)
    m = min(ds); print(f'\n  differences {S}; readings at d_min {[str(d/m) for d in ds]}; R = {float(n*m*tend):.4f}, {len(steps)} moves')
    for idx, k, t in steps:
        D = 1 / (n * t); sx = ds[idx] / D; N = round(float(sx) / n)
        g = F(n * N + 1) - sx; dep = min(sx - n * N, n * N - sx) if N else sx
        others = [str(ds[j] / ds[idx]) for j in range(len(ds)) if j != idx]
        print(f'    setter d={ds[idx]} lap {k}: t={t}, scale D={D}, reading s_x={sx} (N={N}), g=5N+1−s_x={g}, depth δ={abs(dep)}, ratios to setter {others}')
def job(args):
    v, = args
    nested = Counter(); ex = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        steps, _ = walk(ds)
        pos = {}
        for j, (idx, k, _) in enumerate(steps):
            if idx in pos:
                j0, Q = pos[idx]
                inner = steps[j0 + 1:j]
                seen = {}
                for jj, (idx2, k2, _) in enumerate(inner):
                    if idx2 in seen:
                        nested['nested return'] += 1
                        nested['lower lap' if max(seen[idx2], k2) < Q else 'not lower'] += 1
                        if max(seen[idx2], k2) >= Q and len(ex) < 4: ex.append((v, i, Q, seen[idx2], k2))
                    seen[idx2] = k2
            pos[idx] = (j, k)
    return nested, ex
if __name__ == '__main__':
    V = 24; tot = Counter(); EX = []
    with Pool() as pool:
        for nested, ex in pool.imap_unordered(job, [(v,) for v in itertools.combinations(range(1, V + 1), n)], chunksize=200):
            tot.update(nested); EX += ex[:2]
    print(f'\n(2) nested returns inside a stretch between two settings of the same runner, [1,{V}]: {dict(tot)}')
    print('   exceptions (parent lap Q, inner laps):', EX[:4])
