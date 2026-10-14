"""Grid = AP displaced by whole 8-slot cycles (WHICH_GRIDS sec2).  So the integer-scale layer
fails exactly when a disparity is a whole number of cycles -- a SLOT-SHARER at scale g (Prop 6.6).
Named candidate for that residue: the sharer's OWN flank at k = b, where d = 8b*g.
Scale d/(8b+1); the sharer then reads 8b+1 exactly (sec 6.2, the setter lands one slot away).
Does that instant work?  Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor, gcd
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def lonely(ds,t): return all(circd(F(d)*t)>=TH for d in ds)
def min_k(ds,KMAX=60):
    for k in range(KMAX+1):
        kk=F(k)+TH
        for e in ds:
            if lonely(ds,kk/F(e)): return k,e
    return None,None

for (LO,HI,label) in [(0,20,"speeds in [0,20)"),(0,60,"speeds in [0,60)"),(0,200,"speeds in [0,200)")]:
    rng=random.Random(31)
    nsh=0; hit=0; hit_any=0; resid={}
    for _ in range(4000):
        v=sorted(rng.sample(range(LO,HI),8))
        for i in range(8):
            ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
            g=0
            for d in ds: g=gcd(g,d)
            sharers=[d for d in ds if (d//g)%8==0]
            if not sharers: continue
            nsh+=1
            # the SMALLEST sharer's own flank at k = b
            d=min(sharers); b=(d//g)//8
            if lonely(ds,(F(b)+TH)/F(d)): hit+=1
            # any sharer's own flank at its own b
            if any(lonely(ds,(F((dd//g)//8)+TH)/F(dd)) for dd in sharers): hit_any+=1
            else:
                k,e=min_k(ds); resid[k]=resid.get(k,0)+1
    print(f"\n=== {label} ===")
    print(f"   subjects WITH a slot-sharer at scale g : {nsh}")
    print(f"   smallest sharer's own flank at k=b works : {hit/nsh:.4f}")
    print(f"   SOME sharer's own flank at its k=b works : {hit_any/nsh:.4f}")
    if resid:
        tot=sum(resid.values())
        print(f"   residue after that criterion: {tot} ({tot/nsh:.4f})   minimal k there: {dict(sorted(resid.items()))}")
