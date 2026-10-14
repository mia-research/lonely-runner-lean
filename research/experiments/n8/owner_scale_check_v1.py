"""Owner called the scales by eye, 2026-09-18:
   (1,31,75,97,128,160,176,225)                      -> scale ~25
   (1,2,3.365,4.231,5.173,6.231,6.827,8.462)         -> scale ~1.2
Test: at scale D the spine instants are t = r/(8D), r odd.  For each subject, is there an odd r
at which every one of its disparities is clear?  Report which scales serve how many subjects,
and how close the owner's call is.  Exact Fraction."""
from fractions import Fraction as F
from math import floor
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def served(v,i,D,RMAX=64):
    ds=[abs(v[j]-v[i]) for j in range(len(v)) if j!=i]
    for r in range(1,RMAX+1,2):
        t=F(r)/(8*D)
        if all(circd(d*t)>=TH for d in ds): return r
    return None

def scan(name,v,guess,lo,hi,step):
    v=[F(x) for x in v]
    print(f"\n=== {name}   owner's call: scale ~ {guess} ===")
    best=[]
    D=F(lo)
    while D<=hi:
        got=[served(v,i,D) for i in range(8)]
        cnt=sum(1 for g in got if g is not None)
        best.append((cnt,D,got))
        D+=step
    mx=max(c for c,_,_ in best)
    print(f"   best coverage over the scan: {mx} of 8 subjects")
    winners=[(c,D,g) for c,D,g in best if c==mx]
    print(f"   scales achieving it: {len(winners)}   e.g. {[str(D) for _,D,_ in winners[:6]]}")
    # how does the owner's guess do?
    g=F(guess)
    got=[served(v,i,g) for i in range(8)]
    print(f"   AT THE OWNER'S SCALE D = {guess}: serves {sum(1 for x in got if x is not None)} of 8")
    print(f"      per subject, minimal odd r (None = not served at this scale):")
    for i in range(8):
        print(f"        subject {str(v[i]):>10}   r = {got[i]}")
    # nearest fully-serving scale to the guess
    full=[D for c,D,_ in best if c==8]
    if full:
        near=min(full,key=lambda D: abs(D-g))
        print(f"   nearest scale serving ALL 8: D = {near} = {float(near):.4f}   (owner said {guess})")
    else:
        print(f"   no scale in the scan serves all 8")

scan("(1,31,75,97,128,160,176,225)",[1,31,75,97,128,160,176,225],25,F(1,2),F(60),F(1,4))
scan("(1,2,3.365,4.231,5.173,6.231,6.827,8.462)",
     [F(1),F(2),F(3365,1000),F(4231,1000),F(5173,1000),F(6231,1000),F(6827,1000),F(8462,1000)],
     F(6,5),F(1,20),F(4),F(1,100))
