"""Step 1 of E80: find the hard cases with the cascade.  Hardness = the cascade's relay length (moves) for the slowest
runner, tie-broken by the event's R = 8 d_min t.  Exact climbs over whole-number arrangements (speeds 1..600, eight
distinct, all moving): one speed moved at a time by an integer step, accepted when (moves, R) does not fall.  Starts:
random arrangements and the known hard sets (Case C climbs of casec_R_climb_v1).  Report the hardest arrangements with
their relay words (setter ranks) and R."""
import random, re, sys
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
from arrangement_lib import nd

def relay(V):
    ds = sorted(v - V[0] for v in V[1:]); t = F(1, 8 * ds[0]); word = []
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < F(1, 8)]
        if not way: return word, 8 * ds[0] * t, ds
        cand = {i: (F(floor(ds[i] * t - F(1, 8)) + 1) + F(1, 8)) / ds[i] for i in way}
        i = max(cand, key=lambda x: cand[x]); word.append(i); t = cand[i]
        if len(word) > 5000: return word, None, ds

def score(V):
    w, R, ds = relay(V)
    return (len(w), R if R is not None else F(10**9))

def climb(args):
    V, seed, iters = args
    rnd = random.Random(seed); cur = score(V)
    for _ in range(iters):
        i = rnd.randrange(0, 8)
        W = list(V); W[i] += rnd.choice((-1, 1)) * rnd.randint(1, max(1, (V[-1] - V[0]) // rnd.choice((4, 16, 64))))
        W = sorted(W)
        if W[0] < 1 or W[-1] > 600 or len(set(W)) < 8: continue
        sc = score(W)
        if sc >= cur: V, cur = W, sc
    w, R, ds = relay(V)
    return V, len(w), R, w, ds

if __name__ == '__main__':
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    rnd = random.Random(80); starts = [sorted(rnd.sample(range(1, 600), 8)) for _ in range(90)]
    for line in open('casec_R_climb_v1.out'):
        m = re.search(r'V (\[[^\]]*\])', line)
        if m:
            V = eval(m.group(1)); m0 = V[0] - 1
            if V[-1] - m0 <= 600: starts.append([v - m0 for v in V])
    with Pool() as pool: res = pool.map(climb, [(S, 900 + i, iters) for i, S in enumerate(starts)])
    res.sort(key=lambda r: (-r[1], -(r[2] or 0)))
    print(f"climbs {len(res)} ({iters} proposals each); moves reached: max {res[0][1]}")
    for V, n, R, w, ds in res[:15]:
        print(f"  moves {n:3d}  R {float(R):.4f}  readings/d_min {[round(d / ds[0], 3) for d in ds]}  V {V}")
        print(f"       relay word (reading ranks 0..6): {w}")
