"""n=5: search resonant configurations directly.  Speeds K*(p,q,r) + offsets (d1,d2,d3), small integers p<=q<=r<=6,
K large; anneal the offsets (and K) to maximise the final nearest reading.  Records the best per K-scale."""
from fractions import Fraction as F
import math, random
from multiprocessing import Pool
th = F(1, 5)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def reading(r):
    ds = [F(1)] + sorted(r); t = th; L = 0
    while True:
        best = t; who = None
        for d in ds:
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, d
        if who is None: return 5 * t, L
        t = best; L += 1
        if L > 20000: return 5 * t, L
TRIPLES = [(p, q, r) for p in range(1, 5) for q in range(p, 7) for r in range(q, 9) if math.gcd(math.gcd(p, q), r) == 1]
def job(args):
    Kscale, seed = args
    rng = random.Random(seed)
    best = (F(0), None, 0, None)
    for _ in range(6):
        p, q, r = rng.choice(TRIPLES)
        K = F(Kscale) + F(rng.randint(0, 10**6), 10**6) * Kscale
        off = [F(rng.randint(-10**4, 10**4), 10**4) for _ in range(3)]
        def spd(K, off): return [max(F(1), K * p + off[0]), max(F(1), K * q + off[1]), max(F(1), K * r + off[2])]
        cur = (K, off)
        cs, L = reading(spd(*cur))
        for it in range(700):
            sc = [F(1), F(1, 10), F(1, 100), F(1, 1000), F(1, 10**5)][it * 5 // 700]
            K2 = cur[0] + sc * F(rng.randint(-100, 100), 100)
            off2 = [o + sc * F(rng.randint(-100, 100), 100) for o in cur[1]]
            s2 = spd(K2, off2)
            if len(set(s2)) < 3: continue
            ns, nL = reading(s2)
            if ns >= cs: cur, cs, L = (K2, off2), ns, nL
        if cs > best[0]: best = (cs, (p, q, r), L, [float(x) for x in spd(*cur)])
    return Kscale, best
if __name__ == '__main__':
    jobs = [(Ks, s) for Ks in (5, 20, 100, 1000) for s in range(24)]
    with Pool() as pl: res = pl.map(job, jobs)
    for Ks in (5, 20, 100, 1000):
        b = max((r for k, r in res if k == Ks), key=lambda r: r[0])
        print(f'K ~ {Ks}: largest nearest reading {float(b[0]):.4f}, triple {b[1]}, chain {b[2]} moves, speeds {[round(x, 4) for x in b[3]]}')
