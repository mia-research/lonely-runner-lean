"""Control: does the implementation agree with the PROVED Lean statements?

`four_diffs_stop_ge_six`: ds.card <= 4, n >= 6  =>  the 7th iterate is fixed.
`three_diffs_stop_within_three_moves`: ds.card <= 3, n >= 4  =>  the 3rd iterate is fixed.
`two_diffs_stop_within_one_move`: ds.card <= 2, n >= 3  =>  the 1st iterate is fixed.

If this implementation reports MORE moves than the theorem allows, the implementation is
wrong and the n=5 numbers mean nothing.
"""
import random, math
from fractions import Fraction as F

CAP = 100000
def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def inWay(d, t): return circDist(d * t) < INV
    def nextOpening(d, t): return (F(math.ceil(d * t - INV)) + INV) / d
    def cascade(ds):
        a = min(ds); t = F(1,1) / (N * a)
        for j in range(CAP):
            act = [d for d in ds if inWay(d, t)]
            if not act: return True, j
            t = max(nextOpening(d, t) for d in act)
        return False, CAP
    return cascade

random.seed(11)
def probe(N, k, allowed, trials=30000, label=""):
    casc = mk(N); worst, wset, bad = -1, None, 0
    for _ in range(trials):
        S = random.choice([50, 1000, 10**5, 10**8, 10**10])
        c = tuple(sorted(random.sample(range(1, S+1), k)))
        ds = tuple(F(x) for x in c)
        ok, mv = casc(ds)
        if not ok: bad += 1; continue
        if mv > worst: worst, wset = mv, ds
    verdict = "AGREES" if worst <= allowed else "*** CONTRADICTS THEOREM ***"
    print(f"n={N:>3} k={k}  allowed {allowed:>2}   observed max {worst:>5}   {verdict}   {label}")
    if worst > allowed: print("     witness:", tuple(int(x) for x in wset))
    return worst

print("=== controls against proved theorems ===")
for N in [6, 7, 8, 9, 12]:
    probe(N, 4, 7, label="four_diffs_stop_ge_six")
for N in [4, 5, 6, 8]:
    probe(N, 3, 3, label="three_diffs_stop_within_three_moves")
for N in [3, 5, 8]:
    probe(N, 2, 1, label="two_diffs_stop_within_one_move")

print()
print("=== the uncovered diagonal case, same implementation ===")
probe(5, 4, 7, label="(k=4, n=5) -- NOT covered by any theorem")
