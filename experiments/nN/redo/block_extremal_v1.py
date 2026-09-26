"""WP3 item 1: the extremal six-runner blocks for Q(F) = L(F) * min(min F, sigma5(F)), found by perturbation (move one
runner at a time, steps from coarse to 1, keep improvements).  Q is scale-invariant, so the extremes are shapes.
Exact (Fraction), Boundary Set Method.  Also item 3: L0(F), the start-up stretch from t = 0, and Q0 = L0 * min(...).
Runs under caffeinate; checkpoint of the best per start written as it goes (block_extremal_v1.best.txt)."""
import random, sys
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
from multiprocessing import Pool
def comps(Fs):
    g = reduce(gcd, Fs); P = F(1, g); zones = []
    for d in Fs:
        for m in range(0, d // g + 2):
            a, b = F(8 * m - 1, 8 * d), F(8 * m + 1, 8 * d)
            if b > 0 and a < P: zones.append((a, b))
    zones.sort(); out = []; ca, cb = zones[0]
    for a, b in zones[1:]:
        if a < cb: cb = max(cb, b)
        else: out.append((ca, cb)); ca, cb = a, b
    out.append((ca, cb)); return out
def Q(Fs):
    Fs = sorted(Fs)
    if len(set(Fs)) < 6 or Fs[0] <= 0: return F(-1), F(0), F(0)
    cs = comps(Fs); L = max((b - a for a, b in cs if a > 0), default=F(0))
    L0 = max((b for a, b in cs if a <= 0), default=F(0))          # start-up stretch from t = 0
    s5 = min(max(c) - min(c) for c in combinations(Fs, 5)); sc = min(Fs[0], s5)
    return L * sc, L0 * sc, L
def climb(start):
    cur = sorted(start); q = Q(cur)[0]
    scale = max(cur)
    for step in (scale // 20, scale // 60, scale // 200, 3, 1):
        step = max(1, step); improved = True
        while improved:
            improved = False
            for j in range(6):
                for s in (step, -step):
                    cand = list(cur); cand[j] += s
                    qc = Q(cand)[0]
                    if qc > q: cur, q, improved = sorted(cand), qc, True
    qq, q0, L = Q(cur)
    return start, cur, qq, q0
if __name__ == '__main__':
    rnd = random.Random(12)
    starts = []
    starts += [[k * 120 + rnd.randint(-20, 20) for k in range(1, 7)] for _ in range(6)]                 # evenly spaced
    starts += [sorted(rnd.sample(range(1, 800), 6)) for _ in range(10)]                                 # random
    starts += [[800 + e for e in sorted(rnd.sample(range(0, 60), 6))] for _ in range(6)]                # tight six-train
    starts += [[rnd.randint(20, 80)] + [800 + e for e in sorted(rnd.sample(range(0, 50), 5))] for _ in range(6)]  # slow + five
    starts += [[k * 100 for k in range(1, 7)], [100, 200, 300, 400, 500, 700], [700 + 10 * k for k in range(6)]]
    with Pool() as p, open('block_extremal_v1.best.txt', 'w') as ck:
        res = []
        for start, cur, qq, q0 in p.imap_unordered(climb, starts):
            res.append((qq, cur, start, q0))
            ck.write(f"{qq}\t{float(qq):.4f}\t{cur}\t{q0}\n"); ck.flush()
    res.sort(key=lambda r: -r[0])
    print("extremal blocks for Q = L * min(min F, sigma5) (exact), best first")
    for qq, cur, start, q0 in res[:10]:
        m = cur[0]
        print(f"  Q = {qq} ({float(qq):.4f})  block {cur}  shape {[round(x / m, 3) for x in cur]}  start-up Q0 = {float(q0):.4f}")
    print(f"max Q over {len(res)} climbs: {res[0][0]} = {float(res[0][0]):.4f};  max start-up Q0: {float(max(r[3] for r in res)):.4f}")
