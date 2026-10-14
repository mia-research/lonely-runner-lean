"""Total coverage with P6 generalised (t-budget 4)."""
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
def ok_kt(ds,ep,k,t,n=5):
    for d in ds:
        c,s=divmod(d*t,ep); r=(d*k+c)%n
        if 1<=r<=n-2: continue
        if r==n-1 and s==0: continue
        return False
    return True
def P6gen(ds,T=4,n=5):
    for ep in ds:
        if ep%n: continue
        for t in [1+n*i for i in range(T)]:
            if t >= ep: break
            for k in range(0,n):
                if ok_kt(ds,ep,k,t,n): return True
    return False
def prim(c):
    g=c[0]
    for x in c[1:]: g=math.gcd(g,x)
    return g==1
def n_open(c):
    e=c[-1]; M=5*e
    return sum(1 for j in range(e) if all(e<=(d*(5*j+1))%M<=4*e for d in c))

for hi in (30,40):
    tot=0; union=0; left=[]
    for c in combinations(range(1,hi+1),4):
        if not prim(c): continue
        tot+=1; e=c[-1]; nf=c[:-1]
        if (all(d%5!=0 for d in nf) or e<=4*c[0] or e<=15
            or max_gap(nf)>F(1,e) or all(d%5==0 for d in nf) or P6gen(c)):
            union+=1
        else: left.append(c)
    print(f"n=5, card 4, [1,{hi}]: {tot} sets   UNION {union} ({100*union/tot:.2f}%)   left {len(left)} ({100*len(left)/tot:.2f}%)")
    if left:
        print(f"   min openings among the left: {min(n_open(c) for c in left)}")
        print(f"   max d_max among the left    : {max(max(c) for c in left)}")
        print(f"   examples: {left[:10]}")
    print()
