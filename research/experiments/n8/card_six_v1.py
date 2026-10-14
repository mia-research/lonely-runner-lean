"""If a subject's 7 differences have <= 6 DISTINCT absolute values, order-7 LRC applies:
6 distinct speeds, margin 1/7 > 1/8. Test the claim, and measure how often it fires."""
from math import gcd
from functools import reduce
from fractions import Fraction as F
import random, itertools
def circ(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)
def lonely_margin(ds, T=200000):
    """best achievable min-distance over a fine sweep (lower bound on the true sup)"""
    best=0
    M=reduce(lambda a,b: a*b//gcd(a,b), ds)
    for i in range(1,T+1):
        t=F(i, 8*M)
        m=min(circ(F(d)*t) for d in ds)
        if m>best: best=m
        if best>=F(1,7): break
    return best
random.seed(7)
print("claim: <= 6 distinct |d| => a witness with margin >= 1/7 (> 1/8)")
bad=0; n=0
for _ in range(400):
    k=random.randint(2,6)
    vals=random.sample(range(1,40),k)
    ds=vals+[random.choice(vals)]*(7-k)     # 7 differences, <= 6 distinct
    g=reduce(gcd,ds); ds=[d//g for d in ds]
    n+=1
    if lonely_margin(sorted(set(ds))) < F(1,7): bad+=1
print(f"   {n-bad}/{n} reach margin >= 1/7  {'(ALL)' if bad==0 else f'{bad} FAIL'}")
print()
print("how often is a subject the midpoint of two others (=> a repeated |d|)?")
for hi in (10,20,50,200):
    hit=0; tot=0
    for _ in range(40000):
        v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
        ds=[abs(v[j]-v[s]) for j in range(8) if j!=s]
        tot+=1
        if len(set(ds))<=6: hit+=1
    print(f"   range +-{hi:3d}: {100*hit/tot:5.2f}% of subjects")
