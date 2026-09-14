"""n=5, the cascade in the owner's frame.  Subject with nearest difference m = d_min (reading 1).  Other runners' readings
at scale m: s_x = a_x + e_x (AP index a_x = nearest integer, deviation e_x).  Cascade: R_0 = 1 (scale D_0 = m); at scale
D_j = m/R_j each reading is s_x R_j; a runner is in the way iff s_x R_j is within 1 of 5N; the step takes the smallest
next scale, R_{j+1} = max over in-way runners of (5N+1)/s_x.  Stops when no reading is within 1 of a multiple of 5;
R = R_final = d_min/D_final.  Records full cascades for the highest-R arrangements found by annealing."""
from fractions import Fraction as F
import math, random
from multiprocessing import Pool
def near(x): return math.floor(x + F(1, 2))
def cascade(s):
    R = F(1); steps = []
    while True:
        best = R; who = None
        for i, sx in enumerate(s):
            v = sx * R; N = near(v / 5)
            if abs(v - 5 * N) < 1:
                cand = F(5 * N + 1) / sx
                if cand > best: best, who = cand, (i, N, v)
        if who is None: return R, steps
        steps.append((who[0], who[1], who[2], best)); R = best
def job(seed):
    rng = random.Random(seed)
    cur = sorted(1 + F(rng.randint(0, 9000), 1000) for _ in range(3)); cs = cascade(cur)[0]
    best = (cs, list(cur))
    for it in range(4000):
        sc = [F(1, 10), F(1, 100), F(1, 1000), F(1, 10**5)][it * 4 // 4000]
        new = sorted(max(F(1), x + sc * F(rng.randint(-100, 100), 100)) for x in cur)
        if len(set(new)) < 3: continue
        ns = cascade(new)[0]
        if ns >= cs or rng.random() < 0.01: cur, cs = new, ns
        if cs > best[0]: best = (cs, list(cur))
    return best
if __name__ == '__main__':
    with Pool() as p: res = p.map(job, range(48))
    res.sort(key=lambda r: -r[0])
    seen = []
    for R, s in res:
        key = tuple(round(float(x), 2) for x in s)
        if key in seen: continue
        seen.append(key)
        Rf, steps = cascade(s)
        idx = [near(x) for x in s]; dev = [x - near(x) for x in s]
        print(f'\nR = {float(Rf):.5f}  readings s = {[round(float(x), 5) for x in s]}  AP indices {idx} (mod 5: {[i % 5 for i in idx]})  deviations {[round(float(e), 4) for e in dev]}')
        for i, N, v, Rn in steps:
            print(f'   runner {"bcd"[i]} reading {float(v):8.4f} within 1 of {5*N:3d} -> R = (5·{N}+1)/{float(s[i]):.4f} = {float(Rn):.5f}')
        if len(seen) >= 8: break
