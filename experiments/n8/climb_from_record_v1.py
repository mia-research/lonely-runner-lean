"""No nesting: zooming into the deepest cell finds nothing deeper.  So depth increases only by
moving SEVERAL coordinates.  The obvious untried move: local search seeded AT the record.

Start from the verified 28-move case and climb, allowing multi-coordinate moves and working in a
scaled-up copy so fractional steps are available.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def depth(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
REC=[49,205,234,256,286,323,366]
print(f"  seed: {REC}  depth {depth(REC)}")
best=(depth(REC), tuple(REC))
for SCALE in (1,4,12,40):
    seed=[x*SCALE for x in best[1]] if SCALE>1 else list(best[1])
    # re-seed from the current best, scaled
    cur=list(seed); curd=depth(cur)
    rng=random.Random(1000+SCALE)
    stall=0
    for step in range(60000):
        w=list(cur)
        nmoves=rng.choice([1,1,1,2,2,3])
        for _ in range(nmoves):
            k=rng.randrange(7)
            w[k]+=rng.choice([-3,-2,-1,1,2,3])
        if min(w)<=0 or len(set(w))!=7: continue
        w=sorted(w)
        d=depth(w)
        if d is None: continue
        if d>curd: cur,curd,stall=w,d,0
        elif d==curd: cur,stall=w,stall+1
        else: stall+=1
        if stall>4000: break
    # normalise by gcd for reporting
    from math import gcd
    g=0
    for x in cur: g=gcd(g,x)
    norm=tuple(x//g for x in cur)
    print(f"  scale x{SCALE:<3}: best depth {curd:>3}   {list(norm)}   S = {max(norm)/min(norm):.4f}")
    if curd>best[0]: best=(curd,norm)
print(f"\n  BEST FOUND: depth {best[0]}   {list(best[1])}")
print(f"    verify: {depth(list(best[1]))}   record was 28 -> "
      f"{'BEATS IT' if best[0]>28 else ('matches' if best[0]==28 else 'below')}")
