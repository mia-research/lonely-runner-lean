"""Order 5 two-return runners, complete characterisation (no truncated prints). Every 5-subset of [1,V], every runner: the
walk's difference set, whether the returner is the largest difference, the returner's lap triple, the intervening laps, R, and
the ratio of the first intervening setter to the returner."""
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
        if who is None: return steps, t
        steps.append(who); t = best
def job(v):
    out = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        st, t = walk(ds); c = Counter(i2 for i2, _ in st)
        if c and max(c.values()) >= 3:
            x = max(c, key=lambda k: c[k])
            first_other = next((str(ds[i2] / ds[x]) for i2, _ in st if i2 != x), 'none')
            out.append((tuple(int(d) for d in sorted(ds)), int(ds[x]), int(max(ds)),
                        tuple(k for i2, k in st if i2 == x), tuple(k for i2, k in st if i2 != x),
                        first_other, F(n) * min(ds) * t))
    return out
if __name__ == '__main__':
    for V in (24, 30):
        rows = []
        with Pool() as pool:
            for out in pool.imap_unordered(job, itertools.combinations(range(1, V + 1), n), chunksize=200):
                rows += out
        sets = Counter(r[0] for r in rows); laps = Counter(r[3] for r in rows)
        inner = Counter(k for r in rows for k in r[4]); Rs = sorted(r[6] for r in rows)
        largest = sum(1 for r in rows if r[1] == r[2])
        print(f'V={V}: {len(rows)} two-return runners; {len(sets)} difference sets: {dict(sets)}')
        print(f'   returner is the largest difference: {largest} of {len(rows)}')
        print(f'   returner lap triples: {dict(laps)}')
        print(f'   intervening laps: {dict(sorted(inner.items()))}')
        print(f'   R: min {Rs[0]} ({float(Rs[0]):.4f}), max {Rs[-1]} ({float(Rs[-1]):.4f})')
        print(f'   ratio of the first intervening setter to the returner: {Counter(r[5] for r in rows).most_common()}')
        sys.stdout.flush()
