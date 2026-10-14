"""Cross-shift analysis of the order-5 resonant chains.

The finite certificate proves sup R = 27/8 < 4 for ratio S = d_max/d_min (the difference ratio; the manuscript's 'ratio' is W = v_8 - v_1) <= 8 (order5_certificate_v3.py).
The open question is whether unbounded ratio reduces to bounded ratio. This asks the data one thing:

    when a chain runs long at large global ratio, is the growth of R carried by a bounded-ratio
    sub-family, or do the far-apart speeds carry it too?

R accumulates as R = R_1 + sum_j g_j / s_j with g_j in (0,2), so a setting by a runner of speed s
contributes at most 2/s. Split the realised increments by the setter's ratio r = s / d_min:

    IN   r <= C  (the cluster the certificate already covers)
    OUT  r >  C  (everything above it)

If sup over chains of the OUT part is below 4 - 27/8 = 5/8, then bounded ratio plus a bounded
remainder closes the cap, and the reduction is a lemma to prove rather than a hope.

Also measured, because "cluster" must be checked and not assumed: the ratio of the setters inside
every window of w consecutive settings, against the global ratio. A chain that traverses clusters
shows small window ratio with large global ratio; one that does not shows window ratio ~ global.
"""
from fractions import Fraction as F
import math, random, sys
from collections import Counter
from multiprocessing import Pool
n = 5; th = F(1, n); C = 8
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def walk(ds, cap=4000):
    t = th / min(ds); steps = []; ts = [t]
    while len(steps) < cap:
        best = t; who = None
        for idx, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (idx, k)
        if who is None: return steps, ts, True
        steps.append(who); t = best; ts.append(t)
    return steps, ts, False
RATS = [F(1), F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job(seed):
    rng = random.Random(seed)
    out = []   # per walk: (ratio, moves, R, R_in, R_out, maxwin5, maxwin10, n_active, active_spread)
    for _ in range(300):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) != 4: continue
        ds = r; st, ts, done = walk(ds)
        if not done: continue
        dmin = min(ds); ratio = float(max(ds) / dmin)
        R = float(n * dmin * ts[-1])
        R1 = float(n * dmin * ts[0])
        Rin = Rout = 0.0
        for j, (idx, _k) in enumerate(st):
            dR = float(n * dmin * (ts[j + 1] - ts[j]))
            if float(ds[idx] / dmin) <= C: Rin += dR
            else: Rout += dR
        setters = [idx for idx, _ in st]
        def maxwin(w):
            if not setters: return 1.0
            m = 1.0
            for i in range(0, max(1, len(setters) - w + 1)):
                win = setters[i:i + w]
                sp = float(max(ds[j] for j in win) / min(ds[j] for j in win))
                m = max(m, sp)
            return m
        act = sorted(set(setters))
        asp = float(max(ds[j] for j in act) / min(ds[j] for j in act)) if act else 1.0
        out.append((ratio, len(st), R, R1, Rin, Rout, maxwin(5), maxwin(10), len(act), asp))
    return out
if __name__ == '__main__':
    with Pool() as pool: res = [x for part in pool.map(job, range(24)) for x in part]
    print(f'order 5 resonant chains: {len(res)} completed walks, cluster cut C = {C}')
    big = [x for x in res if x[0] > C]
    print(f'   of which global ratio > {C}: {len(big)}')
    if not big: sys.exit()
    def rep(name, vals):
        vals = sorted(vals)
        q = lambda p: vals[min(len(vals) - 1, int(p * len(vals)))]
        print(f'   {name:<34} min {vals[0]:.4f}   median {q(0.5):.4f}   p99 {q(0.99):.4f}   max {vals[-1]:.4f}')
    rep('global ratio', [x[0] for x in big])
    rep('moves', [float(x[1]) for x in big])
    rep('R (final)', [x[2] for x in big])
    rep('R_1 (first opening)', [x[3] for x in big])
    rep(f'R carried by ratio <= {C}  (IN)', [x[4] for x in big])
    rep(f'R carried by ratio >  {C}  (OUT)', [x[5] for x in big])
    rep('window-5 setter ratio', [x[6] for x in big])
    rep('window-10 setter ratio', [x[7] for x in big])
    rep('ratio of the active set', [x[9] for x in big])
    print(f'   distinct runners that ever set: {Counter(x[8] for x in big)}')
    mo = max(big, key=lambda x: x[5])
    print(f'   worst OUT: {mo[5]:.4f} at global ratio {mo[0]:.1f}, {mo[1]} moves, R = {mo[2]:.4f}')
    print(f'   gap available under the cap: 4 - 27/8 = {4 - 27/8:.4f}   ->  OUT stays below it: {max(x[5] for x in big) < 4 - 27/8}')
    nw = sum(1 for x in big if x[6] > C)
    print(f'   chains whose window-5 setter ratio exceeds {C}: {nw} of {len(big)}')
