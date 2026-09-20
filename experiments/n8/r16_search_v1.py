"""One round: adversarial search for R >= 16 with S = d_max/d_min in [7,10].  R = d_min / D_final (cascade recursion,
exact).  Simulated annealing over 8 distinct positive speeds; integer grids to 400 / 3000 / 20000 and rational grids
(denominators 10, 100); seeded restarts from the best arrangements found earlier.  Top results re-checked against BSM."""
import sys, os, random, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_cascade_recursion_v1 import cascade
    from full_transit_positions_v2 import first_time
SEEDS = [(96,136,189,227,266,308,331,398), (27,70,107,137,159,188,344,393), (1,31,75,97,128,160,176,225),
         (17,141,170,238,264,293,340,388), (44,89,120,226,260,294,313,368), (644,959,1070,1360,1475,1878,2004,2280)]
def best_R(V):
    b = (F(0), None)
    for i in range(8):
        scale, last, steps, D = cascade(V, i)
        m = min(D.values()); M = max(D.values()); S = M / m
        if 7 <= S <= 10:
            R = m / scale
            if R > b[0]: b = (R, i)
    return b
def anneal(args):
    seed, HI, den, init = args
    rng = random.Random(seed)
    unit = F(1, den)
    def rand_speed(): return F(rng.randint(den, HI * den), den)
    if init is not None:
        V = sorted(F(v) for v in init)
        if HI > max(init) * 2: V = sorted(v * (HI // max(init)) for v in V)
    else:
        V = sorted({rand_speed() for _ in range(12)})[:8]
        while len(V) < 8: V = sorted(set(V) | {rand_speed()})[:8]
    cur = best_R(V); best = (cur[0], list(V), cur[1])
    T0 = 1.5; iters = 5000; t_end = time.time() + 150
    for it in range(iters):
        if time.time() > t_end: break
        T = T0 * (1 - it / iters) + 0.02
        W = list(V); j = rng.randrange(8)
        r = rng.random()
        if r < 0.2: W[j] = rand_speed()
        elif r < 0.6: W[j] = W[j] + unit * rng.choice([-3, -2, -1, 1, 2, 3])
        else: W[j] = W[j] + unit * rng.choice([-1, 1]) * rng.randint(4, max(5, HI * den // 50))
        if W[j] <= 0 or len(set(W)) < 8: continue
        W.sort(); s = best_R(W)
        if s[0] >= cur[0] or rng.random() < math.exp(float(s[0] - cur[0]) / T):
            V, cur = W, s
            if cur[0] > best[0]: best = (cur[0], list(V), cur[1])
    return best, HI, den
if __name__ == "__main__":
    jobs = []
    for s in range(8):  jobs.append((1000 + s, 400, 1, None))
    for s in range(8):  jobs.append((2000 + s, 3000, 1, None))
    for s in range(8):  jobs.append((3000 + s, 20000, 1, None))
    for s in range(4):  jobs.append((4000 + s, 60, 10, None))
    for s in range(4):  jobs.append((5000 + s, 20, 100, None))
    for k, sd in enumerate(SEEDS):
        jobs.append((6000 + k, max(sd) + 50, 1, sd)); jobs.append((7000 + k, max(sd) + 50, 1, sd))
    t0 = time.time()
    with Pool(8) as p: res = p.map(anneal, jobs, chunksize=1)
    res.sort(key=lambda x: x[0][0], reverse=True)
    print(f"{len(jobs)} annealing runs, {time.time()-t0:.0f}s")
    print("R >= 16 found:", any(r[0][0] >= 16 for r in res))
    print("top 10 (R, speeds, runner, grid):")
    for (R, V, i), HI, den in res[:10]:
        t_c = None
        scale, last, steps, D = cascade(V, i)
        t_bsm = first_time(V, i)
        print(f"  R = {float(R):.4f}  depth {steps+1}  S = {float(max(D.values())/min(D.values())):.3f}  speeds {[str(v) for v in V]}  r{i+1}  "
              f"grid <= {HI}, 1/{den}  | cascade time = BSM: {1/(8*scale) == t_bsm}")
