"""The smallest four-difference set at n=5 needing more than 7 moves."""
import math
from fractions import Fraction as F
from itertools import combinations

N = 5; INV = F(1, N)
def circDist(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)
def inWay(d, t): return circDist(d * t) < INV
def nextOpening(d, t): return (F(math.ceil(d * t - INV)) + INV) / d

def trace(ds):
    a = min(ds); t = F(1,1) / (N * a); steps = []
    for j in range(1000):
        act = [d for d in ds if inWay(d, t)]
        if not act: return t, steps
        nt = max(nextOpening(d, t) for d in act)
        steps.append((t, tuple(int(d) for d in act), nt)); t = nt
    return None, steps

# smallest by max element, then lexicographic
best = None
for M in range(4, 60):
    for c in combinations(range(1, M+1), 4):
        if c[3] != M: continue
        if math.gcd(math.gcd(c[0],c[1]), math.gcd(c[2],c[3])) != 1: continue
        ds = tuple(F(x) for x in c)
        fixed, steps = trace(ds)
        if fixed is not None and len(steps) > 7:
            best = (c, fixed, steps); break
    if best: break

c, fixed, steps = best
print(f"smallest (by largest element) four-difference set at n=5 needing >7 moves: {c}")
print(f"moves: {len(steps)}   bound at n>=6 would be 7")
print(f"start  1/(5*{c[0]}) = {F(1,1)/(N*F(c[0]))}")
for i,(t,act,nt) in enumerate(steps):
    print(f"  move {i+1:>2}: t = {str(t):>22}  in the way {act}  ->  {nt}")
print(f"fixed point: t = {fixed} = {float(fixed):.9f}")
print("readings at the fixed point (circDist(d*t), must all be >= 1/5 = 0.2):")
for d in c:
    print(f"   d={d:>3}  circDist = {circDist(F(d)*fixed)} = {float(circDist(F(d)*fixed)):.9f}")
