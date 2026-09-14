"""Four differences (nearest a, others b < c < d) at n = 6, 7, 8: setter words, gaps between settings of b, c, d,
how many times b sets, longest chain; random + near-rational + annealing on chain length."""
from fractions import Fraction as F
import math, random, collections
from multiprocessing import Pool
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; w = []; laps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return w, laps, t
        w.append('abcd'[who[0]]); laps.append(who[1]); t = best
        if len(w) > 500: return w, laps, t
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4), F(5), F(6), F(7)]
def job(args):
    n, seed = args
    rng = random.Random(seed)
    stats = dict(maxlen=0, ex=None, bmax=0, bex=None, gaps={x: collections.Counter() for x in 'bcd'}, near=0, cnt=0)
    def rec(r):
        r = [max(F(1), x) for x in r]
        ds = [F(1)] + sorted(r)
        if len(set(ds)) < 4: return 0
        w, laps, t = chain(ds, n); s = ''.join(w); stats['cnt'] += 1
        if 'a' in s: stats['near'] += 1
        if len(s) > stats['maxlen']: stats['maxlen'], stats['ex'] = len(s), (s, laps, [str(x) for x in ds])
        nb = s.count('b')
        if nb > stats['bmax']: stats['bmax'], stats['bex'] = nb, (s, laps, [str(x) for x in ds])
        for x in 'bcd':
            idx = [i for i, ch in enumerate(s) if ch == x]
            for p, q in zip(idx, idx[1:]): stats['gaps'][x][s[p + 1:q]] += 1
        return len(s)
    for _ in range(6000):
        if rng.random() < 0.5:
            M = rng.choice([3, 10, 50, 300])
            rec([1 + F(rng.randint(0, 10**5), 10**5) * M for _ in range(3)])
        else:
            b = 1 + F(rng.randint(0, 80000), 1000)
            rec([b, b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)])
    cur = [1 + F(rng.randint(0, 6000), 1000) for _ in range(3)]; cl = rec(cur)
    for it in range(3000):
        step = F(rng.choice([1, 10, 100, 1000]), 1000)
        new = [max(F(1), x + step * F(rng.randint(-100, 100), 100)) for x in cur]
        nl = rec(new)
        if nl >= cl or rng.random() < 0.03: cur, cl = new, nl
    return n, stats
if __name__ == '__main__':
    jobs = [(n, s) for n in (6, 7, 8) for s in range(16)]
    with Pool() as p: res = p.map(job, jobs)
    for n in (6, 7, 8):
        S = [st for m, st in res if m == n]
        cnt = sum(st['cnt'] for st in S); near = sum(st['near'] for st in S)
        top = max(S, key=lambda st: st['maxlen']); btop = max(S, key=lambda st: st['bmax'])
        gaps = {x: collections.Counter() for x in 'bcd'}
        for st in S:
            for x in 'bcd': gaps[x].update(st['gaps'][x])
        print(f'\nn={n}: chains {cnt}; nearest sets a move in {near}; longest {top["maxlen"]}: {top["ex"]}')
        print(f'   most settings by b: {btop["bmax"]}: {btop["bex"]}')
        for x in 'bcd': print(f'   gaps between settings of {x}: {dict(gaps[x].most_common(12))}')
