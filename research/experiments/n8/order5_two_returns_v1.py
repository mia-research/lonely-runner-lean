"""The order-5 runners whose cascade has a runner setting three times (two returns), over every 5-subset of [1,V], V = 24 and
V = 30. For each: the differences, the readings at d_min, the transcript (setter, lap), the returning runner's laps, the
ratios of the intervening setters to it (reduced), and R = 5·d_min·t at the end."""
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
def job(args):
    v, = args
    out = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        st, t = walk(ds)
        c = Counter(idx for idx, _ in st)
        if c and max(c.values()) >= 3:
            x = max(c, key=lambda k: c[k])
            laps = [k for idx, k in st if idx == x]
            others = [(str(ds[idx] / ds[x]), k) for idx, k in st if idx != x]
            m = min(ds)
            out.append((v, i, [str(d) for d in sorted(ds)], [(int(a), int(b)) for a, b in st], str(ds[x]), laps, others, float(5 * m * t)))
    return out
if __name__ == '__main__':
    for V in (24, 30):
        rows = []
        with Pool() as pool:
            for out in pool.imap_unordered(job, [(v,) for v in itertools.combinations(range(1, V + 1), n)], chunksize=200):
                rows += out
        print(f'V={V}: {len(rows)} runners with a two-return')
        sig = Counter(tuple(sorted(F(x) for x in r[2])) for r in rows)
        print('   difference sets (as multisets):', [( [str(x) for x in k], c) for k, c in sig.most_common(6)])
        rat = Counter(r[6][0][0] if r[6] else None for r in rows)
        print('   ratio of the first intervening setter to the returning runner:', rat.most_common(8))
        for r in rows[:4]:
            print(f'   speeds {r[0]} subject {r[0][r[1]]}: differences {r[2]}; transcript {r[3]}; returner d={r[4]} at laps {r[5]}; intervening (ratio, lap) {r[6]}; R={r[7]:.4f}')
        sys.stdout.flush()
