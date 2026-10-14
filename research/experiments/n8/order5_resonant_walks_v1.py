"""Order 5 in the resonant regime: near-rational speed ratios with readings in the hundreds (the generator that produced the
300-move chains). Exact rationals. For each walk: moves, R, the maximum number of settings by one runner, and for every pair of
consecutive settings of the same runner (a return): the parent lap Q, the number of intervening moves, their laps, whether the
pricing holds, and — for nested returns inside that stretch — whether the inner laps are strictly below Q (the candidate
well-founded measure)."""
from fractions import Fraction as F
import math, random, sys
from collections import Counter
from multiprocessing import Pool
n = 5; th = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def walk(ds, cap=4000):
    t = th / min(ds); steps = []
    while len(steps) < cap:
        best = t; who = None
        for idx, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (idx, k)
        if who is None: return steps, t, True
        steps.append(who); t = best
    return steps, t, False
RATS = [F(1), F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job(seed):
    rng = random.Random(seed)
    c = Counter(); lens = []; Rs = []; nested_bad = []; price_bad = 0; price_ok = 0; setmax = Counter()
    for _ in range(300):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) != 4: continue
        ds = r
        st, t, done = walk(ds)
        if not done: c['hit cap'] += 1; continue
        m = min(ds); R = float(n * m * t); lens.append(len(st)); Rs.append(R)
        cnt = Counter(i for i, _ in st); setmax[max(cnt.values()) if cnt else 0] += 1
        pos = {}
        for j, (idx, k) in enumerate(st):
            if idx in pos:
                j0, Q = pos[idx]; inner = st[j0 + 1:j]
                prod = math.prod([F(5 * q + 1, 5 * q - 1) for _, q in inner], start=F(1))
                if prod > F(5 * Q + 4, 5 * Q + 1): price_ok += 1
                else: price_bad += 1
                seen = {}
                for idx2, k2 in inner:
                    if idx2 in seen:
                        c['nested'] += 1
                        if max(seen[idx2], k2) < Q: c['inner below parent'] += 1
                        else:
                            c['inner NOT below parent'] += 1
                            if len(nested_bad) < 3: nested_bad.append((Q, seen[idx2], k2, [str(x) for x in ds]))
                    seen[idx2] = k2
            pos[idx] = (j, k)
    return c, lens, Rs, price_ok, price_bad, setmax, nested_bad
if __name__ == '__main__':
    TOT = Counter(); L = []; RR = []; OK = BAD = 0; SM = Counter(); NB = []
    with Pool(6) as pool:
        for c, lens, Rs, ok, bad, sm, nb in pool.map(job, range(24)):
            TOT.update(c); L += lens; RR += Rs; OK += ok; BAD += bad; SM.update(sm); NB += nb
    L.sort(); RR.sort()
    print(f'resonant order 5: {len(L)} walks; moves: median {L[len(L)//2]}, p99 {L[int(len(L)*0.99)]}, max {L[-1]}')
    print(f'   R: median {RR[len(RR)//2]:.4f}, p99 {RR[int(len(RR)*0.99)]:.4f}, max {RR[-1]:.4f}')
    print(f'   most settings by one runner: {dict(sorted(SM.items()))}')
    print(f'   pricing (return_growth) holds in {OK} of {OK + BAD} returns')
    print(f'   nested returns: {dict(TOT)}')
    print(f'   examples where inner laps are not below the parent lap: {NB[:3]}')
