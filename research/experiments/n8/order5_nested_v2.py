"""Order 5: nested returns. Every 5-subset of [1,V], every runner. For each pair of consecutive settings of a runner x at laps
(Q, Q'), look at the moves in between: if some runner y sets twice inside that stretch (a nested return), are y's laps strictly
below Q? That is the candidate well-founded measure for the two-return lemma's recursion."""
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
                if o > best: best, who = o, (idx, k)
        if who is None: return steps
        steps.append(who); t = best
def job(v):
    c = Counter(); ex = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        st = walk(ds); pos = {}
        for j, (idx, k) in enumerate(st):
            if idx in pos:
                j0, Q = pos[idx]; inner = st[j0 + 1:j]; seen = {}
                c['stretches'] += 1
                if inner and all(kk < Q for _, kk in inner): c['all inner laps below parent'] += 1
                for idx2, k2 in inner:
                    if idx2 in seen:
                        c['nested'] += 1
                        if max(seen[idx2], k2) < Q: c['nested below parent'] += 1
                        else:
                            c['nested NOT below parent'] += 1
                            if len(ex) < 3: ex.append((v, i, Q, seen[idx2], k2))
                    seen[idx2] = k2
            pos[idx] = (j, k)
    return c, ex
if __name__ == '__main__':
    V = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    tot = Counter(); EX = []
    with Pool() as pool:
        for c, ex in pool.imap_unordered(job, itertools.combinations(range(1, V + 1), n), chunksize=200):
            tot.update(c); EX += ex[:1]
    print(f'order 5, every 5-subset of [1,{V}], every runner: {dict(tot)}')
    print('examples where the nested laps are not below the parent lap (speeds, subject, Q, inner laps):', EX[:5])
