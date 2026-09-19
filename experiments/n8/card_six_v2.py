"""Fair test: sweep a FULL period. The earlier run capped the sweep and missed witnesses."""
from math import gcd
from functools import reduce
from fractions import Fraction as F
import random
def circ(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1-f)
def best_margin(ds):
    """exact max over t of min_i circDist(d_i t); breakpoints have denominator dividing 2*lcm"""
    M=reduce(lambda a,b: a*b//gcd(a,b), ds)
    best=F(0)
    for i in range(1, 2*M):
        t=F(i, 2*M)
        m=min(circ(F(d)*t) for d in ds)
        if m>best: best=m
    return best
random.seed(7)
print("claim: a subject whose 7 differences have <= 6 DISTINCT |d| is lonely,")
print("       because intLRC_seven gives 6 distinct speeds a margin of 1/7 > 1/8.")
bad=[]; n=0
for _ in range(600):
    k=random.randint(2,6)
    vals=random.sample(range(1,25),k)
    g=reduce(gcd,vals); vals=[v//g for v in vals]
    n+=1
    b=best_margin(sorted(set(vals)))
    if b < F(1,7): bad.append((sorted(set(vals)), b))
print(f"   distinct-speed sets of size <= 6: {n-len(bad)}/{n} reach margin >= 1/7")
for x in bad[:5]: print(f"      below 1/7: speeds {x[0]} best margin {x[1]} = {float(x[1]):.4f}")
print()
print("   and all of them reach >= 1/8 (which is what loneliness at order 8 needs):")
b8=[x for x in bad if x[1] < F(1,8)]
print(f"      below 1/8: {len(b8)} {'(NONE -- every one is lonely)' if not b8 else b8[:3]}")
