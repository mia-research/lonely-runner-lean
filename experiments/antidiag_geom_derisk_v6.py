"""
v6: definitively settle "gap vs no gap" + correct the v5 criterion.

Two things:
 (I) ROBUST no-gap: under (50), are there ANY C∩R-empty anti-diagonal tuples,
     over a LARGE q-range? 0 empty => no theorem gap, pentagon NOT needed.
 (II) Correct the clean-argument criterion. v5 tested only FULL 1/6 crossings.
      The real on-circle Y-spacing is 1/e, e=gcd(r+p,q) (since gcd(p,e)=1), and a
      PARTIAL crossing of length L(c0) carries a grid point when 1/e <= L(c0).
      So BHK's argument generalizes to: EXISTS an occupied circle c0 with
      L(c0) >= 1/e. Measure coverage; characterize any true residual (these are
      the genuinely-hard-to-formalize cases, NOT gaps).
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x-(x.numerator//x.denominator)
def S(l,p,q,r): u=2*l+1; return frac(F(r*u,2*q)),frac(F(p*u,2*q))
XLO,XHI=F(1,6),F(1,2);YLO,YHI=F(1,6),F(1,3)
def inR(X,Y): return XLO<=X<=XHI and YLO<=Y<=YHI
def hask(i,p,q,r):
    for k in range(q):
        if (k*r-i)%q==0 and (k*p+i)%q==0: return True
    return False
def b50(i,p,q,r): return 2*i*r<(6+i)*q
def Lcross(c0):
    """vertical length of line x+y=c0 (mod1) intersect S-window R."""
    best=F(0)
    for sh in (c0,c0+1,c0-1):
        lo=max(YLO,sh-XHI); hi=min(YHI,sh-XLO)
        if hi>lo: best=max(best,hi-lo)
    return best
def tuples(QMAX):
    for i in (3,4,5):
        for q in range(18,QMAX+1):
            if gcd(i,q)==1: continue
            for p in range(1,q):
                if 3*p>=q or gcd(p,q)!=1: continue
                for r in range(q+1,(3*q)//2+1):
                    if 2*r>=3*q or not b50(i,p,q,r) or not hask(i,p,q,r): continue
                    yield i,p,q,r

# (I) robust no-gap
print("=== (I) ROBUST no-gap test under (50) ===")
for QMAX in (120, 240, 400):
    empty=0; tot=0
    for i,p,q,r in tuples(QMAX):
        tot+=1
        if all(not inR(*S(l,p,q,r)) for l in range(q)):
            empty+=1
    print(f"  q<= {QMAX}: tuples={tot}, C∩R-EMPTY={empty}")

# (II) corrected clean criterion: exists occupied circle c0 with L(c0) >= 1/e
print("\n=== (II) corrected clean criterion (spacing 1/e, partial crossings) ===")
QMAX=240
n=0; clean=0; resid=[]
for i,p,q,r in tuples(QMAX):
    n+=1
    e=gcd(r+p,q)
    occ=sorted(set(frac(F((r+p)*(2*l+1),2*q)) for l in range(q)))  # occupied circles
    ok=any(Lcross(c0) >= F(1,e) for c0 in occ)
    if ok: clean+=1
    else: resid.append((i,p,q,r,e,gcd(i,q)))
print(f"  tuples: {n}")
print(f"  covered by corrected clean argument (∃ circle L(c0)>=1/e): {clean}/{n}")
print(f"  residual (clean fails, but witness still exists): {len(resid)}")
if resid:
    print("    residual i-values:", sorted(set(t[0] for t in resid)))
    print("    residual e=gcd(r+p,q) values:", sorted(set(t[4] for t in resid)))
    for t in resid[:20]: print("      ",t)
    # verify residual still has witnesses (no gap):
    bad=[(i,p,q,r) for (i,p,q,r,e,d) in resid if all(not inR(*S(l,p,q,r)) for l in range(q))]
    print("    residual WITHOUT any witness (=real gap):", len(bad))
