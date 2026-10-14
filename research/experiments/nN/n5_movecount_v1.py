"""Is the move count at (k=4, n=5) bounded by a constant?

At n >= 6 the Lean statement is "the 7th iterate is fixed".  The n=5 sweep found 33 moves,
so the analogous n=5 statement cannot use 7.  This probes whether ANY constant works, by
pushing the spread d_max/d_min upward and watching the maximum move count.
"""
import random, math
from fractions import Fraction as F

N = 5
INV = F(1, N)
CAP = 100000

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

random.seed(7)
print("spread sweep: ds = (1, x, y, z) with x,y,z drawn near scale S")
print(f"{'scale S':>12} {'trials':>7} {'max moves':>10}   witness")
for S in [10**2, 10**3, 10**4, 10**5, 10**6, 10**7, 10**8, 10**9, 10**10]:
    worst, wset = -1, None
    for _ in range(4000):
        c = tuple(sorted(random.sample(range(S//2, S+1), 3)))
        ds = (F(1), F(c[0]), F(c[1]), F(c[2]))
        ok, mv = cascade(ds)
        if not ok: print("  NON-ARRIVAL", ds); continue
        if mv > worst: worst, wset = mv, ds
    print(f"{S:>12} {4000:>7} {worst:>10}   {tuple(int(x) for x in wset)}")

print()
print("targeted: the shape that produced 33 — (2, M, M+a, M+b) with M large")
print(f"{'scale M':>12} {'max moves':>10}   witness")
for M in [10**6, 10**7, 10**8, 10**9, 10**10, 10**11]:
    worst, wset = -1, None
    for _ in range(3000):
        a, b = sorted(random.sample(range(1, M//50 + 2), 2))
        ds = (F(2), F(M), F(M+a), F(M+b))
        ok, mv = cascade(ds)
        if not ok: print("  NON-ARRIVAL", ds); continue
        if mv > worst: worst, wset = mv, ds
    print(f"{M:>12} {worst:>10}   {tuple(int(x) for x in wset)}")
