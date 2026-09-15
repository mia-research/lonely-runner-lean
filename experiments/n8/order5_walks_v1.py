"""Order 5 walk transcripts. Every 5-subset of [1,V], every runner: run the cascade exactly and record each move as
(setter, lap). Then:
 (1) how often a runner sets twice (a return) and three times (two returns);
 (2) between consecutive settings of the same runner: the number of intervening moves and their laps;
 (3) for returns, the check  prod over intervening moves of (5Q_j+1)/(5Q_j-1)  >  (Q+4/5)/(Q+1/5)  (return_growth);
 (4) the ratio denominators d_y/d_x (reduced) of the returning runner against the intervening setters — the resonance side."""
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
def job(args):
    V, v = args
    setcnt = Counter(); gaps = Counter(); laps = Counter(); growth_ok = growth_bad = 0
    dens = Counter(); two_examples = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        st = walk(ds)
        c = Counter(idx for idx, _ in st)
        m = max(c.values()) if c else 0
        setcnt[m] += 1
        pos = {}
        for j, (idx, k) in enumerate(st):
            if idx in pos:
                j0, Q = pos[idx]
                between = st[j0 + 1:j]
                gaps[len(between)] += 1
                laps[(Q, k)] += 1
                prod = math.prod([F(5 * q + 1, 5 * q - 1) for _, q in between], start=F(1))
                need = F(5 * Q + 4, 5 * Q + 1)
                if prod > need: growth_ok += 1
                else: growth_bad += 1
                dx = ds[idx]
                for bidx, _ in between:
                    r = ds[bidx] / dx
                    dens[r.denominator] += 1
            pos[idx] = (j, k)
        if m >= 3 and len(two_examples) < 2:
            two_examples.append((v, i, [(int(a), int(b)) for a, b in st]))
    return setcnt, gaps, laps, growth_ok, growth_bad, dens, two_examples
if __name__ == '__main__':
    V = 24
    SC = Counter(); GA = Counter(); LA = Counter(); OK = BAD = 0; DE = Counter(); EX = []
    with Pool() as pool:
        for sc, ga, la, ok, bad, de, ex in pool.imap_unordered(job, [(V, v) for v in itertools.combinations(range(1, V + 1), n)], chunksize=200):
            SC.update(sc); GA.update(ga); LA.update(la); OK += ok; BAD += bad; DE.update(de)
            if len(EX) < 4: EX += ex
    print(f'order 5, every 5-subset of [1,{V}], every runner: most settings by one runner -> runners: {dict(sorted(SC.items()))}')
    print(f'(2) intervening moves between consecutive settings of the same runner: {dict(sorted(GA.items()))}')
    print(f'(3) return_growth check: product exceeds the lap ratio in {OK} of {OK + BAD}')
    print(f'(4) denominators of d_y/d_x (returning runner x against intervening setters y): {DE.most_common(12)}')
    print(f'    lap pairs (Q, Q\') of consecutive settings, top: {LA.most_common(10)}')
    for v, i, st in EX[:3]: print(f'    two-return transcript: speeds {v} subject index {i}: {st}')
