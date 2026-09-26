"""Owner: perturb the loop arrangements towards a third setting and read off which relations the second loop needs.
Start: the 17 Case C arrangements (case_c_map_v1, seed 26) in which some runner sets twice.  Move one of the six other
runners at a time (integer speeds x64; g_1 and the subject fixed; order, distinctness and W > 24 g_1 kept; every speed
positive), accepting a move when the cascade's own measure rises:
  obj = max over runners d of  settings(d) + (fraction of d's next clear band the relay covers after d's last setting)
A third setting means obj >= 3.  Exact (Fraction); the moves are the only randomness (seeded).  At every arrangement
reaching three settings, record: the chain; the loops (setters between consecutive settings of the repeater); whether
the second loop repeats the first loop's word; the phase shift per lap of d, rho_e = frac(e/d), of each loop runner, and
its distance to the nearest p/q with q <= 4; the tightest five-spread sigma5/d_2."""
import sys, random
from fractions import Fraction as F
from math import floor
from itertools import combinations
from arrangement_lib import nd

def cascade(ds, t):
    ch = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return ch, t
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); ch.append((d, cand[d])); t = cand[d]

def measure(V):
    ds = sorted(v - V[0] for v in V[1:]); ch, T = cascade(ds, F(1, 8 * ds[0]))
    best = F(0); arg = None
    for d in set(s for s, _ in ch):
        times = [x for s, x in ch if s == d]
        frac = min(F(1), (T - times[-1]) * d / F(3, 4))
        o = len(times) + frac * F(99, 100)
        if o > best: best, arg = o, d
    return best, arg, ds, ch

def ok(V, g1, W0):
    return all(V[i] < V[i + 1] for i in range(7)) and V[1] - V[0] == g1 and V[7] - V[0] > 24 * g1

def near_pq(x):
    return min(abs(x - F(p, q)) for q in (1, 2, 3, 4) for p in range(0, q + 1))

def climb(args):
    V, seed, iters = args
    rnd = random.Random(seed); g1 = V[1] - V[0]
    cur, _, _, _ = measure(V); hist = []
    for it in range(iters):
        j = rnd.randrange(2, 8); scale = max(1, (V[j] - V[j - 1]) // 20)
        W = list(V); W[j] += rnd.choice((-1, 1)) * rnd.randint(1, scale)
        if not ok(W, g1, None): continue
        o, _, _, _ = measure(W)
        if o >= cur:
            V, cur = W, o
            if cur >= 3: break
    o, d, ds, ch = measure(V)
    return V, o, d, ds, ch

def describe(V, o, d, ds, ch):
    idx = [i for i, (s, _) in enumerate(ch) if s == d]
    loops = [[ds.index(s) for s, _ in ch[idx[k] + 1:idx[k + 1]]] for k in range(len(idx) - 1)]
    six = ds[1:]; s5 = min(max(c) - min(c) for c in combinations(six, 5))
    loopr = sorted(set(s for s, _ in ch if s != d))
    rho = {ds.index(e): (F(e, d) - floor(F(e, d))) for e in loopr}
    return dict(obj=float(o), rep=ds.index(d), settings=len(idx), loops=loops,
                same=len(loops) >= 2 and loops[0] == loops[1],
                rho={k: (round(float(v), 4), round(float(near_pq(v)), 4)) for k, v in rho.items()},
                s5=float(F(s5, six[0])), ratios=[round(e / d, 4) for e in ds[1:]])

if __name__ == '__main__':
    from multiprocessing import Pool
    import case_c_map_v1 as cm
    from relay_law_v1 import chain, repeats
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
                ds = sorted(v - V[0] for v in V[1:]); ch, _ = chain(ds, F(1, 8 * ds[0]))
                if repeats(ch): starts.append((shape, g1div, [64 * v for v in V]))
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    tasks = [(V, 1000 * i + r, iters) for i, (_, _, V) in enumerate(starts) for r in range(4)]
    print(f"starts {len(starts)} (4 climbs each, {iters} proposals per climb)", flush=True)
    with Pool() as pool:
        res = pool.map(climb, tasks)
    reached = 0
    for (V, o, d, ds, ch), (V0, seed, _) in zip(res, tasks):
        sh = starts[seed // 1000]
        dsc = describe(V, o, d, ds, ch); reached += dsc['settings'] >= 3
        print(f"{sh[0]:17s} W/{sh[1]:<5d} climb {seed % 1000}: obj {dsc['obj']:.3f} repeater rank {dsc['rep']} settings {dsc['settings']} "
              f"loops {dsc['loops']} same-word {dsc['same']} sigma5/d2 {dsc['s5']:.4f}")
        print(f"      readings/d {dsc['ratios']}   rho(rank): (frac(e/d), dist to p/q q<=4) {dsc['rho']}")
    print(f"climbs reaching a third setting: {reached} of {len(tasks)}")
