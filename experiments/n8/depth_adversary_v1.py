"""Adversarial hill-climb: maximise (a) cascade depth, (b) t/bound = d_min/D_final, over integer 8-sets in [1,HI].
Moves: change one speed by +-1..+-5 or resample it.  Cascade recursion (exact).  Several restarts per seed."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_cascade_recursion_v1 import cascade
HI = 400
def score(V, which):
    best = (0, None)
    for i in range(8):
        scale, last, steps, D = cascade([F(v) for v in V], i)
        val = steps + 1 if which == "depth" else min(D.values()) / scale
        if val > best[0]: best = (val, i)
    return best
def climb(args):
    seed, which = args
    rng = random.Random(seed); bestall = (0, None, None)
    for restart in range(6):
        V = sorted(rng.sample(range(1, HI + 1), 8)); cur = score(V, which)
        for it in range(1500):
            W = list(V); j = rng.randrange(8)
            W[j] = rng.randint(1, HI) if rng.random() < 0.3 else max(1, min(HI, W[j] + rng.choice([-5,-4,-3,-2,-1,1,2,3,4,5])))
            if len(set(W)) < 8: continue
            W.sort(); s = score(W, which)
            if s[0] >= cur[0]: V, cur = W, s
        if cur[0] > bestall[0]: bestall = (cur[0], V, cur[1])
    return bestall
if __name__ == "__main__":
    with Pool(8) as p:
        for which in ("depth", "ratio"):
            res = p.map(climb, [(s, which) for s in range(16)])
            top = sorted(res, key=lambda x: x[0], reverse=True)[:4]
            print(which, [(float(v) if which == "ratio" else v, V, f"r{i+1}") for v, V, i in top], flush=True)
