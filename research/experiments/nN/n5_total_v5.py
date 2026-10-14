"""Total coverage with P7 added (v-budget 12)."""
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
            if t>=ep: break
            for k in range(0,n):
                if ok_kt(ds,ep,k,t,n): return True
    return False
def rho_ok(ds,e,rho,n=5):
    einv=pow(e,-1,n); w=((1-rho)*einv)%n; a=rho+e*w
    if a%n!=1%n: return False
    M=n*e
    return all(e<=(d*a)%M<=(n-1)*e for d in ds)
def P7(ds,V=12,n=5):
    e=ds[-1]
    if e%n==0 or math.gcd(n,e)!=1: return False
    mults=[d for d in ds if d%n==0]
    if len(mults)!=1: return False
    m=mults[0]//n
    if math.gcd(m,e)!=1: return False
    minv=pow(m,-1,e); lo=-(-e//n); hi=(n-1)*e//n
    if hi<lo: return False
    for i in range(V):
        v=lo+(hi-lo)*i//max(V-1,1)
        if rho_ok(ds,e,(minv*v)%e,n): return True
    return False
def prim(c):
    g=c[0]
    for x in c[1:]: g=math.gcd(g,x)
    return g==1
def n_open(c):
    e=c[-1]; M=5*e
    return sum(1 for j in range(e) if all(e<=(d*(5*j+1))%M<=4*e for d in c))

for hi in (30,40,50,60):
    tot=0; union=0; left=[]
    for c in combinations(range(1,hi+1),4):
        if not prim(c): continue
        tot+=1; e=c[-1]; nf=c[:-1]
        if (all(d%5!=0 for d in nf) or e<=4*c[0] or e<=15
            or max_gap(nf)>F(1,e) or all(d%5==0 for d in nf) or P6gen(c) or P7(c)):
            union+=1
        else: left.append(c)
    print(f"[1,{hi}]  {tot} sets   UNION {union} ({100*union/tot:.3f}%)   left {len(left)} ({100*len(left)/tot:.3f}%)")
    if left:
        print(f"   left: {left}")
        print(f"   min openings {min(n_open(c) for c in left)}   max d_max {max(max(c) for c in left)}")
    print()
