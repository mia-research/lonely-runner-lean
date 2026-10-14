"""Owner: "If AP is the ideal global isolation but grids also achieve isolation, can we map the
neighbours, maybe we are not mapping from AP ideals but from GLOBAL ISOLATION."

Global isolation <=> the reduced speeds are a complete residue system mod 8 (WHICH_GRIDS sec1),
i.e. the residue map is a BIJECTION onto the slots.  So distance-to-global-isolation is the
minimum total displacement making it a bijection -- a transportation problem on the cycle Z/8,
solved exactly: with c_r the residue counts, S_r = sum_{j<=r}(c_j - 1), the cost is
min_K sum_r |S_r - K|, attained at K = median(S).  A grid has cost 0.

Compare that against distance-to-AP as predictors of difficulty."""
from fractions import Fraction as F
from math import floor, gcd
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds,cap=4000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return float(8*m*t), n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

def grid_distance(v):
    """min total displacement (in units of g) making the residues mod 8 a bijection"""
    g=0
    for a in range(8):
        for b in range(a+1,8): g=gcd(g,abs(v[b]-v[a]))
    if g==0: return None
    u=[(x-v[0])//g for x in v]
    c=[0]*8
    for x in u: c[x%8]+=1
    S=[]; run=0
    for r in range(8):
        run+=c[r]-1; S.append(run)
    K=sorted(S)[len(S)//2]
    return sum(abs(s-K) for s in S)

def ap_distance(v):
    """min over gaps D of the spread of v_k - k*D, normalised by D (the sec2.3 fit margin)"""
    best=None
    W=v[-1]-v[0]
    for num in range(1,400):
        D=F(W*num,7*200)                      # scan gaps around W/7
        if D<=0: continue
        e=[F(v[k])-k*D for k in range(8)]
        val=float((max(e)-min(e))/D)
        if best is None or val<best: best=val
    return best

rng=random.Random(2026)
buckets={}
apvals={}
for _ in range(2500):
    v=sorted(rng.sample(range(0,90),8))
    gd=grid_distance(v)
    if gd is None: continue
    ad=ap_distance(v)
    Rs=[]; mv=[]
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        R,n=cascade(ds)
        if R is None: continue
        Rs.append(R); mv.append(n)
    if not Rs: continue
    b=min(gd,8)
    d=buckets.setdefault(b,{'n':0,'maxR':0,'sumR':0.0,'maxmv':0,'sumad':0.0})
    d['n']+=1; d['maxR']=max(d['maxR'],max(Rs)); d['sumR']+=max(Rs)
    d['maxmv']=max(d['maxmv'],max(mv)); d['sumad']+=ad
print("=== difficulty vs DISTANCE TO GLOBAL ISOLATION (grid distance) ===")
print(f"   {'grid dist':>10} {'n':>6} {'max R':>9} {'mean max R':>12} {'max moves':>10} {'mean AP dist':>13}")
for b in sorted(buckets):
    d=buckets[b]
    print(f"   {b:>10} {d['n']:>6} {d['maxR']:>9.4f} {d['sumR']/d['n']:>12.4f} {d['maxmv']:>10} {d['sumad']/d['n']:>13.4f}")
print()
print("   grid distance 0 = the arrangement IS a grid = globally isolated")
