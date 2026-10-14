"""Map the final 3.93%."""
import math
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def norm(x):
    fr = x - math.floor(x); return min(fr,1-fr)
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
def k_ok(ds,ep,k,n=5):
    for d in ds:
        c,s=divmod(d,ep); r=(d*k+c)%n
        if 1<=r<=n-2: continue
        if r==n-1 and s==0: continue
        return False
    return True
def P6(ds,n=5): return any(ep%n==0 and any(k_ok(ds,ep,k,n) for k in range(1,n)) for ep in ds)
def prim(c):
    g=c[0]
    for x in c[1:]: g=math.gcd(g,x)
    return g==1
def n_open(c):
    e=c[-1]; M=5*e
    return sum(1 for j in range(e) if all(e<=(d*(5*j+1))%M<=4*e for d in c))

hi=40
left=[]
for c in combinations(range(1,hi+1),4):
    if not prim(c): continue
    e=c[-1]; nf=c[:-1]
    if all(d%5!=0 for d in nf) or e<=4*c[0] or e<=15: continue
    if max_gap(nf)>F(1,e) or all(d%5==0 for d in nf) or P6(c): continue
    left.append(c)
print(f"final residue in [1,{hi}]: {len(left)} sets\n")
print("=== structure ===")
print("  two smallest are (1,2)?      ", Counter((c[0],c[1])==(1,2) for c in left))
print("  smallest pair distribution   ", dict(sorted(Counter((c[0],c[1]) for c in left).items(), key=lambda p:-p[1])[:8]))
print("  # of 5-multiples             ", dict(sorted(Counter(sum(1 for d in c if d%5==0) for c in left).items())))
print("  flank mod 5                  ", dict(sorted(Counter(c[-1]%5 for c in left).items())))
print("  min openings                 ", min(n_open(c) for c in left))
print("  max d_max among <=3 openings ", max((max(c) for c in left if n_open(c)<=3), default=0))
print()
print("=== the family, first 30 ===")
for c in left[:30]: print("   ",c,"  openings",n_open(c))
