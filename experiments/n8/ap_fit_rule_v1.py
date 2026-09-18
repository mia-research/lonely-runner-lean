"""The owner's scale rule (2026-09-18), tested.  This is MANUSCRIPT sec 2.3's OPEN item
(revision-list 24): 'how the fit decides which runners then need the cascade'.

Owner: "for AP of scale 1 (eg 1...8) each position can cover overlapping intervening spaces for
the dmin to work.  r1 can be >0 to <2, r2 can be >1 to <3.  So I just look for the scale that most
easily matches the FRONT HALF, knowing that as the later half increase the speeds are likely to be
multiples of the grid position or near them."

Fit, in closed form: against gap D with a free base, runner k sits in (A_k - D, A_k + D) for all k
iff  spread_k( v_k - k*D )  <  2D.   Margin  mu(D) = 2 - spread/D   (fits iff mu > 0).
Owner's calls to reproduce:  (1,31,75,97,128,160,176,225) -> 25 ;  the R-extremal -> 1.2 .
"""
from fractions import Fraction as F
from math import floor
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def spread(xs): return max(xs)-min(xs)
def mu(v,D,idx=None):
    ks=range(len(v)) if idx is None else idx
    e=[v[k]-k*D for k in ks]
    return 2-spread(e)/D
def served(v,i,D,RMAX=64):
    ds=[abs(v[j]-v[i]) for j in range(len(v)) if j!=i]
    for r in range(1,RMAX+1,2):
        t=F(r)/(8*D)
        if all(circd(d*t)>=TH for d in ds): return r
    return None

def report(name,v,call,lo,hi,step):
    v=[F(x) for x in v]
    print(f"\n=== {name}    owner's call: D ~ {call} ===")
    rows=[]
    D=F(lo)
    while D<=hi:
        rows.append((D,mu(v,D),mu(v,D,range(4))))
        D+=step
    fits=[(D,m,mf) for D,m,mf in rows if m>0]
    print(f"   minimal D that fits (all 8):        {min(fits)[0]} = {float(min(fits)[0]):.4f}" if fits else "   never fits")
    bestall=max(rows,key=lambda r:r[1])
    bestfront=max(rows,key=lambda r:r[2])
    print(f"   D maximising the margin, all 8:     {bestall[0]} = {float(bestall[0]):.4f}   mu = {float(bestall[1]):.4f}")
    print(f"   D maximising the margin, FRONT 4:   {bestfront[0]} = {float(bestfront[0]):.4f}   mu4 = {float(bestfront[2]):.4f}")
    c=F(call)
    print(f"   at the owner's D = {call}:  mu(all 8) = {float(mu(v,c)):.4f}   mu(front 4) = {float(mu(v,c,range(4))):.4f}"
          f"   serves {sum(1 for i in range(8) if served(v,i,c) is not None)}/8")
    # does the margin-maximising scale also serve everyone?
    for lbl,D in (("all-8 margin max",bestall[0]),("front-4 margin max",bestfront[0]),("minimal fit",min(fits)[0] if fits else None)):
        if D is None: continue
        n=sum(1 for i in range(8) if served(v,i,D) is not None)
        print(f"   scale from '{lbl}' = {float(D):.4f}  serves {n}/8")

report("(1,31,75,97,128,160,176,225)",[1,31,75,97,128,160,176,225],25,F(5),F(60),F(1,4))
report("R-extremal (1,2,3.365,4.231,5.173,6.231,6.827,8.462)",
       [F(1),F(2),F(3365,1000),F(4231,1000),F(5173,1000),F(6231,1000),F(6827,1000),F(8462,1000)],
       F(6,5),F(1,5),F(4),F(1,100))
report("(27,70,107,137,159,188,344,393)",[27,70,107,137,159,188,344,393],None if False else 50,F(5),F(120),F(1,2))
