"""Does the rules-with-conditions programme actually have a fixed point?

I concluded it did, from a FLAT RESIDUE DENSITY (1.45e-4 across a 17-fold growth) and wrote
"do not add a seventh criterion".  That conclusion was drawn from a share of an enumeration --
the measurement MANUSCRIPT_v19 withdraws.  Test it: add ONE more rule family (rational instants,
which are rules with conditions in exactly the same sense) and count what is left.
"""
from fractions import Fraction as F
from itertools import combinations
import math
n = 5
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
        def nm(x): return min(x-(x.numerator//x.denominator),1-(x-(x.numerator//x.denominator)))
        if all(nm(F(d)*((lo+hi)/2))>=F(1,5) for d in ds) and hi-lo>best: best=hi-lo
    _c[key]=best; return best
def ok_kt(ds,ep,k,t):
    for d in ds:
        c,s=divmod(d*t,ep); r=(d*k+c)%n
        if 1<=r<=n-2: continue
        if r==n-1 and s==0: continue
        return False
    return True
def P6gen(ds,T=4):
    for ep in ds:
        if ep%n: continue
        for t in [1+n*i for i in range(T)]:
            if t>=ep: break
            for k in range(0,n):
                if ok_kt(ds,ep,k,t): return True
    return False
def P7(ds,V=12):
    e=ds[-1]
    if e%n==0 or math.gcd(n,e)!=1: return False
    mults=[d for d in ds if d%n==0]
    if len(mults)!=1: return False
    m=mults[0]
    if math.gcd(m,e)!=1: return False
    minv=pow(m,-1,e); einv=pow(e,-1,n)
    for v in range(1,V+1):
        rho=(minv*v)%e
        w=((1-rho)*einv)%n; a=rho+e*w
        if a%n!=1%n: continue
        if all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds): return True
    return False
def RAT(ds,Q=19):
    for q in range(2,Q+1):
        for a in range(1,q):
            if math.gcd(a,q)!=1: continue
            if all(F(1,n) <= min(F((d*a)%q,q), 1-F((d*a)%q,q)) for d in ds): return True
    return False
for HI in (40,60):
    tot=0; six=0; seven=0; left6=[]; left7=[]
    for c in combinations(range(1,HI+1),4):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1; e=c[3]; nf=c[:-1]
        s6 = (all(d%5 for d in nf) or e<=4*c[0] or e<=15 or max_gap(nf)>F(1,e)
              or all(d%5==0 for d in nf) or P6gen(c) or P7(c))
        if s6: six+=1
        else: left6.append(c)
        if s6 or RAT(c): seven+=1
        else: left7.append(c)
    print(f"[1,{HI}]  {tot} primitive 4-sets")
    print(f"   six rule families (P1'..P7)              : left {len(left6)}")
    print(f"   + one more family (rational instants q<=19): left {len(left7)}   {left7[:6]}")
