"""Follow-up to relay_third_v1: a third setting is easy to reach (47 of 68 climbs), so the settings count is not the
invariant.  The proof needs the total WAIT bounded (Case C room = (3/4)(d_2/g_1) laps of d_2).  Climb the cascade's
WAIT from the bound 1/(8 g_1), in laps of d_2, by one-runner moves of the six (integer speeds x64; g_1 and subject
fixed; order, distinctness, W > 24 g_1 kept).  Exact.  At the end of each climb record: WAIT; the chain; settings per
rank weighted by zone width (d_2/(4d) laps each); sigma5/d_2 (tightest five-spread); and for every pair of consecutive
setters (s, s') the ratio s'/s and its distance to the nearest p/q with q <= 6."""
import sys, random
from fractions import Fraction as F
from math import floor
from itertools import combinations
from relay_third_v1 import cascade, ok

def wait(V):
    ds = sorted(v - V[0] for v in V[1:]); ch, T = cascade(ds, F(1, 8 * ds[0]))
    return ds[1] * (T - F(1, 8 * ds[0])), ds, ch

def near(x, Q=6):
    best = None
    for q in range(1, Q + 1):
        p = round(x * q); e = abs(x - F(p, q))
        if best is None or e < best[0]: best = (e, p, q)
    return best

def climb(args):
    V, seed, iters = args
    rnd = random.Random(seed); g1 = V[1] - V[0]
    cur = wait(V)[0]
    for it in range(iters):
        j = rnd.randrange(2, 8); scale = max(1, (V[j] - V[j - 1]) // rnd.choice((5, 20, 100)))
        W = list(V); W[j] += rnd.choice((-1, 1)) * rnd.randint(1, scale)
        if not ok(W, g1, None): continue
        w = wait(W)[0]
        if w >= cur: V, cur = W, w
    return V

if __name__ == '__main__':
    from multiprocessing import Pool
    import case_c_map_v1 as cm
    cm.rnd.seed(26); starts = []
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            n = 0
            while n < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                n += 1
                if n % 15 == 0: starts.append((shape, g1div, [64 * v for v in V]))
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    tasks = [(V, 7 + i, iters) for i, (_, _, V) in enumerate(starts)]
    print(f"starts {len(starts)} (every 15th Case C arrangement per family), {iters} proposals each", flush=True)
    with Pool() as pool:
        res = pool.map(climb, tasks)
    rows = []
    for (sh, gd, V0), V in zip(starts, res):
        w, ds, ch = wait(V); w0 = wait(V0)[0]
        six = ds[1:]; s5 = F(min(max(c) - min(c) for c in combinations(six, 5)), six[0])
        rk = [ds.index(s) for s, _ in ch]
        cost = {}
        for s, _ in ch: cost[ds.index(s)] = cost.get(ds.index(s), 0) + F(ds[1], 4 * s)
        links = [(rk[i], rk[i + 1], near(F(ch[i + 1][0], ch[i][0]))) for i in range(len(ch) - 1)]
        rows.append((float(w), sh, gd, float(w0), float(s5), rk, {k: round(float(v), 3) for k, v in sorted(cost.items())},
                     [(a, b, f"{p}/{q}", round(float(e), 4)) for a, b, (e, p, q) in links], [round(e / ds[1], 3) for e in six]))
    rows.sort(key=lambda r: -r[0])
    for r in rows:
        print(f"WAIT {r[0]:.3f} (start {r[3]:.3f})  {r[1]:17s} W/{r[2]:<5d} sigma5/d2 {r[4]:.4f}  readings/d2 {r[8]}")
        print(f"     chain ranks {r[5]}")
        print(f"     cost per rank (laps of d2) {r[6]}")
        print(f"     links (s -> s', nearest p/q to s'/s, distance) {r[7]}")
