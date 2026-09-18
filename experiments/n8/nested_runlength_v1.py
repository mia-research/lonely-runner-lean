"""Does the run-length criterion NEST from two walkers to the six a real flank has?

Walker 1 (slowest, ghat_1 minimal) is clear on a contiguous run of length (1-2/n)/ghat_1.
Inside that window walker 2 cannot stay bad for more than (2/n)/ghat_2 + 1, so a clear
sub-window survives of length at least L1 - (2/n)/ghat_2 - 1.  Iterate.  Firing condition:

    L_1 = (1-2/n)/g_1 - 1 ;   L_j = L_{j-1} - (2/n)/g_j - 1 ;   need L_m > 0.

Sound by construction (each step only shrinks a window that is clear for all previous walkers).
Question: does it fire on REAL flanks, where several ratios are integers and hence stationary?
Exact Fraction; ground truth by Thm 6.13 (period e at a whole-number flank)."""
import random
from fractions import Fraction as F
from math import floor, gcd
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def ghat(f): return min(f,1-f)

def flank_data(ds,e):
    """returns (dead, walkers) -- dead if a stationary ratio is blocked"""
    ws=[]
    for d in ds:
        r=F(d,e)
        f=r-floor(r)
        if f==0:
            if (r.numerator)%8==0: return True,None      # stationary and blocked: flank dead
        else:
            ws.append(ghat(f))
    return False,sorted(ws)

def fires(ws):
    """FIXED.  The first version subtracted ONE bad block of walker j from the window.  That is
    wrong when the window is longer than walker j's period 1/ghat_j: walker j then has SEVERAL bad
    blocks inside it, and the largest surviving CONTIGUOUS clear sub-window is capped by walker j's
    own clear-run length (3/4)/ghat_j, not by (window - one block).  Take the min."""
    if not ws: return True
    L=F(3,4)/ws[0]-1
    for g in ws[1:]:
        L=min(L-(F(1,4)/g)-1, F(3,4)/g-1)
        if L<=0: return False
    return L>0

def flank_clear(ds,e):
    for k in range(e):
        t=(F(k)+TH)/F(e)
        if all(circd(F(d)*t)>=TH for d in ds): return True
    return False

rng=random.Random(31)
tot=0; subj_fire=0; viol=0; nwalk={}
flank_tot=0; flank_fire=0
for _ in range(1500):
    v=sorted(rng.sample(range(0,90),8))
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        tot+=1
        hit=False
        for e in ds:
            dead,ws=flank_data(ds,e)
            flank_tot+=1
            if dead: continue
            nwalk[len(ws)]=nwalk.get(len(ws),0)+1
            if fires(ws):
                flank_fire+=1
                if not flank_clear(ds,e): viol+=1
                hit=True
        if hit: subj_fire+=1
print(f"subjects: {tot}")
print(f"  settled by the nested criterion on SOME flank : {subj_fire}  ({subj_fire/tot:.4f})")
print(f"  flanks where it fires: {flank_fire} of {flank_tot} live-ish  ({flank_fire/flank_tot:.4f})")
print(f"  VIOLATIONS (fired but no clear opening): {viol}")
print(f"  walker-count distribution at a flank: {dict(sorted(nwalk.items()))}")
