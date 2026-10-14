"""P7: at a NON-multiple flank, choose rho = a mod e to place the multiple inside its band.

Flank e with gcd(n,e)=1.  CRT: a is determined by rho = a mod e (and a = 1 mod n).
Write w = (1 - rho) * e^{-1} mod n, so a = rho + e*w.
  * the multiple n*m :  n*m*a mod n*e = n*(m*a mod e) = n*(m*rho mod e)
       clear iff  m*rho mod e  in [e/n, (n-1)e/n]      -- depends only on rho
  * a non-multiple d :  d*a = e*(floor(d*rho/e) + d*w) + (d*rho mod e)
       clear iff  (floor(d*rho/e) + d*w) mod n in {1,...,n-2}   (or n-1 with d*rho = 0 mod e)

So: pick v inside the multiple's band and set rho = m^{-1} * v mod e.  That makes the multiple
clear BY CONSTRUCTION; the budget is the number of v tried.
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
def prim(c):
    g=c[0]
    for x in c[1:]: g=math.gcd(g,x)
    return g==1

def rho_ok(ds, e, rho, n=5):
    """check the full set at flank e with a = rho + e*w"""
    if math.gcd(n, e) != 1: return False
    einv = pow(e, -1, n)
    w = ((1 - rho) * einv) % n
    a = rho + e*w
    if a % n != 1 % n: return False
    M = n*e
    return all(e <= (d*a) % M <= (n-1)*e for d in ds)

def P7(ds, V=6, n=5):
    e = ds[-1]
    if e % n == 0 or math.gcd(n, e) != 1: return False
    mults = [d for d in ds if d % n == 0]
    if len(mults) != 1: return False
    m = mults[0] // n
    if math.gcd(m, e) != 1: return False
    minv = pow(m, -1, e)
    lo = -(-e // n); hi = (n-1)*e // n
    if hi < lo: return False
    vs = [lo + (hi-lo)*i//max(V-1,1) for i in range(V)]
    for v in vs:
        rho = (minv * v) % e
        if rho_ok(ds, e, rho, n): return True
    return False

hi = 40
left = []
for c in combinations(range(1,hi+1),4):
    if not prim(c): continue
    e=c[-1]; nf=c[:-1]
    if (all(d%5!=0 for d in nf) or e<=4*c[0] or e<=15
        or max_gap(nf)>F(1,e) or all(d%5==0 for d in nf) or P6gen(c)): continue
    left.append(c)
print(f"final residue in [1,{hi}]: {len(left)}")
for V in (1,3,6,10,20):
    got = sum(1 for c in left if P7(c, V))
    print(f"   P7 with v-budget {V:>2}: {got:>4}  ({100*got/len(left):5.2f}%)")
