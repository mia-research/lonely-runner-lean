"""Adversarial search for an event after the first cycle (u* = d_min t* > 1) with the far runner's reading
S = d_max/d_min >= 9.  Exact (Fraction); eight distinct positive integer speeds; the subject may be any runner.

Objective for an arrangement V: max over runners k with S_k >= 9 of u*_k (the cascade's event in laps of k's
nearest runner).  Search: hill-climb with plateau moves and a small annealing acceptance, many restarts from
diverse starts (random at several speed ranges; the recorded hard cases with the far runner stretched to
S = 9.5, 12, 16).  Two arms: S >= 9 (any), and S in [9, 15] (clear of the next slot zone at 16).

Recorded for every best: S, the distance of S to the nearest multiple of 8 (far runner in the subject's slot
zone iff < 1), and the smallest such distance over ALL of the subject's readings."""
import random, sys
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
from arrangement_lib import readings, nd

def cascade(ds, cap=4000):
    t = F(1, 8 * min(ds)); n = 0
    while n < cap:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, n
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); n += 1
    return None, n

def d8(x):
    r = x % 8; return min(r, 8 - r)

def score(V, lo, hi):
    best = (F(-1), None, None, None)
    for k in range(8):
        ds = readings(V, k); S = F(max(ds), min(ds))
        if not (lo <= S <= hi): continue
        t, n = cascade(ds)
        if t is None: return (F(10**9), k, n, S)      # would be a non-arrival: report loudly
        u = min(ds) * t
        if u > best[0]: best = (u, k, n, S)
    return best

HARD = [[27,70,107,137,159,188,344,393], [1,31,75,97,128,160,176,225], [1,1975,5265,6910,8737,9589,11845,15135]]

def start(r, seed_kind, lo):
    if seed_kind == 'hard':
        V = list(r.choice(HARD)); Vs = sorted(V)
        # stretch the extreme runner away so the far reading of the other extreme becomes about target
        target = r.choice((F(19, 2), F(12), F(16)))
        lo_v, hi_v = Vs[0], Vs[-1]; dmin_hi = hi_v - Vs[-2]
        V = Vs[:-1] + [int(Vs[-2] + 0)]; V[-1] = Vs[-1]
        V = Vs[:]; V[0] = max(1, int(hi_v - target * dmin_hi))
        if V[0] >= V[1]: V = [v + (V[1] - V[0] + 1) for v in V]
        return sorted(set(V)) if len(set(V)) == 8 else None
    hi = r.choice((60, 200, 1000, 5000))
    return r.sample(range(1, hi + 1), 8)

def run(args):
    seed, lo, hi, iters = args
    r = random.Random(seed)
    V = None
    while V is None or score(V, lo, hi)[1] is None:
        V = start(r, 'hard' if seed % 4 == 0 else 'rand', lo)
    cur = score(V, lo, hi); best = (cur, V)
    for it in range(iters):
        W = V[:]
        span = max(W) - min(W)
        for _ in range(r.choice((1, 1, 2))):
            j = r.randrange(8); step = max(1, int(span * r.choice((0.002, 0.01, 0.05))))
            W[j] = W[j] + r.randint(-step, step)
        if min(W) <= 0 or len(set(W)) < 8: continue
        s = score(W, lo, hi)
        if s[1] is None: continue
        if s[0] >= cur[0] or r.random() < 0.02:
            V, cur = W, s
            if cur[0] > best[0][0]: best = (cur, V[:])
    return seed, best

if __name__ == '__main__':
    arms = [(F(7), F(9), 'CONTROL S in [7,9] (late events known here)'),
            (F(9), F(10**9), 'S >= 9'), (F(9), F(15), 'S in [9,15]')]
    restarts, iters = int(sys.argv[1]) if len(sys.argv) > 1 else 48, int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    for lo, hi, name in arms:
        print(f"ARM {name}: {restarts} restarts x {iters} iterations", flush=True)
        with Pool() as p:
            res = p.map(run, [(s, lo, hi, iters) for s in range(restarts)])
        res.sort(key=lambda x: -x[1][0][0])
        late = [x for x in res if x[1][0][0] > 1]
        for seed, ((u, k, n, S), V) in res[:10]:
            ds = readings(V, k); dmin = min(ds)
            allmin = min(d8(F(d, dmin)) for d in ds)
            print(f"  seed {seed:3d}: u*={u} ({float(u):.4f}) moves={n} V={sorted(V)} subject {V[k]} "
                  f"S={float(S):.3f} dist(S,8Z)={float(d8(S)):.3f} min dist any reading={float(allmin):.3f}", flush=True)
        print(f"  restarts ending past the first cycle (u* > 1): {len(late)} of {restarts}", flush=True)
        for seed, ((u, k, n, S), V) in late:
            print(f"    LATE seed {seed}: u*={u} S={S} dist(S,8Z)={d8(S)} V={sorted(V)} subject {V[k]}", flush=True)
