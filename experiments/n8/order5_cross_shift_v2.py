"""Cross-shift analysis, v2 — with a generator that CAN straddle clusters.

v1 reported that no window of consecutive settings ever spanned a speed ratio above 8, at global ratios
into the thousands. That null was close to forced: v1's generator drew the three large speeds as b times a
multiplier in [1,3], so the top cluster had ratio <= ~3 by construction and a straddling window was barely
available. The statistic could not have come out the other way, so it is not evidence.

v2 places the speeds at deliberately SEPARATED scales, so a cross-cluster window is available and its absence
would mean something:

    mode 'two'    : {1} u {near b} u {near b*m}          two clusters, gap m
    mode 'three'  : {1, near b, near b*m, near b*m*m}    three clusters
    mode 'ladder' : 1, m, m^2, m^3                       every neighbouring pair separated by m
    mode 'v1'     : v1's own generator, kept as the control that produced the forced null

Measured per walk: global ratio; R and its split by the setter's ratio to d_min (cut C); the ratio of the
setters inside every window of w consecutive settings; and -- the direct question -- whether any two
CONSECUTIVE settings are by runners whose speed ratio exceeds C (a cross-cluster handover).
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
def noise(rng): return F(rng.randint(-3000, 3000), 1000)
def gen(mode, rng):
    b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
    m = F(rng.randint(10, 60))
    if mode == 'v1':
        s = {F(1), b} | {max(F(1), b * rng.choice(RATS) + noise(rng)) for _ in range(2)}
    elif mode == 'two':
        s = {F(1), max(F(1), b + noise(rng)), max(F(1), b * m + noise(rng)), max(F(1), b * m * rng.choice(RATS) + noise(rng))}
    elif mode == 'three':
        s = {F(1), max(F(1), b + noise(rng)), max(F(1), b * m + noise(rng)), max(F(1), b * m * m + noise(rng))}
    else:
        s = {F(1), m, m * m, m * m * m}
    return sorted(s)
def job(args):
    mode, seed = args
    rng = random.Random(seed); out = []
    for _ in range(400):
        ds = gen(mode, rng)
        if len(ds) != 4: continue
        st, ts, done = walk(ds)
        if not done: continue
        dmin = min(ds); ratio = float(max(ds) / dmin)
        R = float(n * dmin * ts[-1]); Rin = Rout = 0.0
        for j, (idx, _k) in enumerate(st):
            dR = float(n * dmin * (ts[j + 1] - ts[j]))
            if float(ds[idx] / dmin) <= C: Rin += dR
            else: Rout += dR
        setters = [idx for idx, _ in st]
        hand = 0                      # consecutive settings by runners more than C apart
        for a, bb in zip(setters, setters[1:]):
            r = float(max(ds[a], ds[bb]) / min(ds[a], ds[bb]))
            if r > C: hand += 1
        def maxwin(w):
            m_ = 1.0
            for i in range(0, max(1, len(setters) - w + 1)):
                win = setters[i:i + w]
                if not win: continue
                m_ = max(m_, float(max(ds[j] for j in win) / min(ds[j] for j in win)))
            return m_
        out.append((ratio, len(st), R, Rin, Rout, maxwin(5), hand, len(set(setters))))
    return mode, out
if __name__ == '__main__':
    modes = ['v1', 'two', 'three', 'ladder']
    tasks = [(mo, 1000 * i + s) for i, mo in enumerate(modes) for s in range(12)]
    agg = {mo: [] for mo in modes}
    with Pool() as pool:
        for mo, out in pool.map(job, tasks): agg[mo] += out
    print(f'order 5 cross-shift v2: cluster cut C = {C}; gap under the cap 4 - 27/8 = {4 - 27/8:.4f}')
    for mo in modes:
        res = agg[mo]
        big = [x for x in res if x[0] > C]
        if not big:
            print(f'\n[{mo}] {len(res)} walks, none with ratio > {C}'); continue
        mv = [x[1] for x in big]
        long_ = [x for x in big if x[1] >= 10]
        def q(v, p):
            v = sorted(v); return v[min(len(v) - 1, int(p * len(v)))]
        print(f'\n[{mo}] {len(big)} walks with global ratio > {C}   (median ratio {q([x[0] for x in big],0.5):.0f}, max {max(x[0] for x in big):.0f})')
        print(f'   moves: median {q(mv,0.5)}, p99 {q(mv,0.99)}, max {max(mv)}   |   walks with >= 10 moves: {len(long_)}')
        print(f'   R: median {q([x[2] for x in big],0.5):.4f}, max {max(x[2] for x in big):.4f}')
        print(f'   R carried by ratio <= {C}: max {max(x[3] for x in big):.4f}    by ratio > {C}: max {max(x[4] for x in big):.4f}')
        print(f'   window-5 setter ratio: median {q([x[5] for x in big],0.5):.3f}, max {max(x[5] for x in big):.3f}')
        ch = [x for x in big if x[6] > 0]
        print(f'   CROSS-CLUSTER HANDOVERS (consecutive setters more than {C} apart): {len(ch)} walks of {len(big)}, max count {max((x[6] for x in big), default=0)}')
        if long_:
            print(f'   among the >= 10-move chains: max window-5 ratio {max(x[5] for x in long_):.3f}, handovers in {sum(1 for x in long_ if x[6] > 0)} of {len(long_)}, max R {max(x[2] for x in long_):.4f}')
