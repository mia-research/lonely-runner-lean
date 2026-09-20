from itertools import combinations
from math import gcd
from fractions import Fraction as F
def tau(ds):
    m=ds[0]; p,q=1,8*m
    for _ in range(600):
        bn=bd=None
        for d in ds:
            r=(d*p)%q
            if 8*min(r,q-r)<q:
                num=8*d*p-q; Q=-((-num)//(8*q)); n2,d2=8*Q+1,8*d
                if bn is None or n2*bd>bn*d2: bn,bd=n2,d2
        if bn is None: return F(m*p,q)
        g=gcd(bn,bd); p,q=bn//g,bd//g
    return None
print("statistic fixed in advance: max over primitive 7-subsets of [1,H] of tau = d_min * t_arrival")
print("the document asserts this is '33/56, unchanged as the range grows'\n")
print(f"{'H':>4} {'sets':>10} {'max tau':>12} {'float':>9}  argmax")
for H in [18,20,22,24,26,28,30,32]:
    best=None; c=0
    for s in combinations(range(1,H+1),7):
        g=0
        for x in s: g=gcd(g,x)
        if g!=1: continue
        c+=1; v=tau(list(s))
        if v is not None and (best is None or v>best[0]): best=(v,s)
    flag=" <-- EXCEEDS 33/56" if best[0]>F(33,56) else ""
    print(f"{H:>4} {c:>10} {str(best[0]):>12} {float(best[0]):>9.5f}  {best[1]}{flag}")
