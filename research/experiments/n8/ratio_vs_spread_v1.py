"""R = t/bound = d_min / D_final and depth, against S = d_max/d_min.  (1) S for the adversarial extremes found.
(2) Adversarial climb maximising R within spread bands S in [7,8), [8,10), [10,15), [15,30), [30,100), and with speeds
to 3000, to see whether R grows and how its maximum depends on S."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_cascade_recursion_v1 import cascade
def stats(V, i):
    scale, last, steps, D = cascade([F(v) for v in V], i)
    m = min(D.values()); M = max(D.values())
    return steps + 1, m / scale, M / m
for V, i in [((27,70,107,137,159,188,344,393), 7), ((96,136,189,227,266,308,331,398), 0), ((1,31,75,97,128,160,176,225), 0), ((1,2,3,4,5,6,32,33), 7)]:
    d, R, S = stats(V, i)
    print(f"{V} r{i+1}: depth {d}, R = {float(R):.3f}, S = d_max/d_min = {float(S):.3f}, (7/8)S R + 7 = {float(F(7,8)*S*R+7):.1f}")
BANDS = [(7, 8), (8, 10), (10, 15), (15, 30), (30, 100)]
def climb(args):
    seed, lo, hi, HI = args
    rng = random.Random(seed); best = (0, None, None, None)
    def sc(V):
        b = (0, None, None)
        for i in range(8):
            d, R, S = stats(V, i)
            if lo <= S < hi and R > b[0]: b = (R, i, d)
        return b
    for restart in range(5):
        V = sorted(rng.sample(range(1, HI + 1), 8)); cur = sc(V)
        for it in range(1200):
            W = list(V); j = rng.randrange(8)
            W[j] = rng.randint(1, HI) if rng.random() < 0.3 else max(1, min(HI, W[j] + rng.choice([-9,-5,-3,-2,-1,1,2,3,5,9])))
            if len(set(W)) < 8: continue
            W.sort(); s = sc(W)
            if s[0] >= cur[0]: V, cur = W, s
        if cur[0] > best[0]: best = (cur[0], V, cur[1], cur[2])
    return best
if __name__ == "__main__":
    with Pool(8) as p:
        for HI in (400, 3000):
            for lo, hi in BANDS:
                res = p.map(climb, [(s * 100 + lo, lo, hi, HI) for s in range(8)])
                b = max(res, key=lambda x: x[0])
                print(f"speeds <= {HI}, S in [{lo},{hi}): max R found {float(b[0]):.3f} (depth {b[3]}) at {b[1]} r{(b[2] or 0)+1}", flush=True)
