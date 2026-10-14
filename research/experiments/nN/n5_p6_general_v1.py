"""P6 generalised: a = k*e + t with t = 1 mod n, 0 < t < e.

Then d*a = d*k*e + d*t; writing d*t = c'*e + s', we get
   d*a mod n*e = e * ((d*k + c') mod n) + s'
so d is clear iff (d*k + (d*t)/e) mod n in {1,...,n-2}, or = n-1 with e | d*t.
t = 1 is the current P6.  Allowing T values of t is a bounded criterion; T = e/n is the full
search.  How fast does coverage rise with T?
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr=x-math.floor(x); return min(fr,1-fr)
def max_gap(ds,_c={}):
    key=tuple(ds)
    if key in _c: return _c[key]
    pts={F(0),F(1)}
    for d in ds:
        for k in range(0,d+2):
            for off in (F(-1,5),F(1,5)):
                t=(F(k)+off)/F(d)
                if 0<=t<=1: pts.add(t)
    P=sorted(pts); best=F(0)
    for i in range(len(P)-1):
        lo,hi=P[i],P[i+1]
        if all(norm(F(d)*((lo+hi)/2))>=F(1,5) for d in ds) and hi-lo>best: best=hi-lo
    _c[key]=best; return best

def ok_kt(ds, ep, k, t, n=5):
    for d in ds:
        c, s = divmod(d*t, ep)
        r = (d*k + c) % n
        if 1 <= r <= n-2: continue
        if r == n-1 and s == 0: continue
        return False
    return True

def P6gen(ds, T, n=5):
    for ep in ds:
        if ep % n: continue
        ts = [1 + n*i for i in range(T) if 1 + n*i < ep]
        for t in ts:
            for k in range(0, n):
                if ok_kt(ds, ep, k, t, n): return True
    return False

def prim(c):
    g=c[0]
    for x in c[1:]: g=math.gcd(g,x)
    return g==1

hi = 34
base = []
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e=c[-1]; nf=c[:-1]
    if all(d%5!=0 for d in nf) or e<=4*c[0] or e<=15: continue
    if max_gap(nf) > F(1,e) or all(d%5==0 for d in nf): continue
    base.append(c)
print(f"sets outside P1'-P5 in [1,{hi}]: {len(base)}")
print(f"{'T (t-budget)':>13} {'covered':>9} {'share':>8}")
for T in (1,2,3,4,6,8,12,20):
    cnt = sum(1 for c in base if P6gen(c, T))
    print(f"{T:>13} {cnt:>9} {100*cnt/len(base):>7.2f}%")
