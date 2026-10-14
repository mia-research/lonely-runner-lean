"""Prop 2.2: every arrangement is an ideal AP of gap D plus deviations in [0,D).
So the deformation is uniformly bounded by ONE GAP.  Does transport survive a full gap,
with deviations on ALL runners at once (not one)?"""
from fractions import Fraction as F
import random
def ivs(ds,U):
    out=None
    for d in ds:
        bl=[];k=0
        while F(8*k+1,1)/d<=U:
            a=F(8*k+1)/d;b=F(8*k+7)/d
            bl.append((max(a,F(0)),min(b,U)));k+=1
        bl=[(a,b) for a,b in bl if b>a]
        out=bl if out is None else [(max(a,c),min(b,e)) for a,b in out for c,e in bl if min(b,e)>max(a,c)]
    return out or []
def meas(x): return sum(b-a for a,b in x)
def inter(A,B): return [(max(a,c),min(b,d)) for a,b in A for c,d in B if min(b,d)>max(a,c)]
U=F(20); AP=[F(i) for i in range(8)]
base=[ivs([abs(v-w) for w in AP if w!=v],U) for v in AP]
random.seed(2026)
print("  deviations drawn uniformly in [0, f*D) on EVERY runner, D = 1.  200 draws each.")
print("   f      interior subjects: min transported measure   extremes: min |L|   any subject empty?")
for f in (F(1,10),F(1,4),F(1,2),F(3,4),F(99,100)):
    worst_in=None; worst_ex=None; empty=0
    for _ in range(200):
        dev=[F(random.randrange(0,1000),1000)*f for _ in range(8)]
        V=sorted(F(i)+dev[i] for i in range(8))
        if len(set(V))!=8: continue
        cur=[ivs([abs(v-w) for w in V if w!=v],U) for v in V]
        if any(meas(c)==0 for c in cur): empty+=1
        for k in (1,2,3,4,5,6):
            t=meas(inter(base[k],cur[k]))
            if worst_in is None or t<worst_in: worst_in=t
        for k in (0,7):
            m=meas(cur[k])
            if worst_ex is None or m<worst_ex: worst_ex=m
    print(f"  {str(f):7s} {float(worst_in):34.5f} {float(worst_ex):18.5f} {empty:20d}")
