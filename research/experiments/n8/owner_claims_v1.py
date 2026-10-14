"""Two untested owner claims.
C1  "as the later half increase the speeds are likely to be multiples of the grid position or near
     them" -- do the FASTER speeds sit closer to grid multiples than the slower ones?
C2  "just one that is referenced to the AP ideal" -- a SELECTION PRINCIPLE we have not used.
     Not the first instant, not the smallest k: the IDEAL's instant, relocated.
Exact Fraction."""
from fractions import Fraction as F
from math import floor
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
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

print("=== C1: are the FASTER speeds nearer their grid positions? ===")
rng=random.Random(21); front=[]; back=[]
for _ in range(4000):
    v=sorted(rng.sample(range(0,200),8))
    lo=F(v[0]); g=(F(v[-1])-lo)/7
    if g==0: continue
    dev=[abs((F(x)-lo)/g - round(float((F(x)-lo)/g))) for x in v]   # distance to nearest grid index
    front += dev[1:4]      # slower half, excluding the anchored ends
    back  += dev[4:7]
print(f"   deviation from the nearest grid position, in gap units")
print(f"     slower half (indices 1-3): mean {st.mean(front):.4f}  median {st.median(front):.4f}")
print(f"     faster half (indices 4-6): mean {st.mean(back):.4f}  median {st.median(back):.4f}")
print(f"   claim predicts the faster half is SMALLER -> {'SUPPORTED' if st.mean(back)<st.mean(front) else 'NOT supported'}")

print()
print("=== C2: the instant 'referenced to the AP ideal' ===")
print("   Deform the AP (1..8) by moving one runner; the ideal's own instants are r/8, r odd.")
print("   Question: is the subject lonely AT or NEAR a relocated ideal instant, and how does that")
print("   compare with the cascade's first instant?")
print(f"   {'perturbation':>14} {'cascade t':>12} {'u=d_min*t':>11} {'nearest ideal r/8':>18} {'lonely at r/8?':>15}")
for e in [F(1,10),F(1,4),F(1,2),F(1),F(3,2),F(2)]:
    v=[F(1),F(2),F(3),F(4),F(5),F(6),F(7),F(8)+e]
    i=0
    ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
    t,n=cascade(ds)
    if t is None: continue
    m=min(ds)
    # the ideal's instants for the UNPERTURBED AP seen by r1: r/8, r odd
    hits=[r for r in (1,3,5,7) if all(circd(d*(F(r,8)))>=TH for d in ds)]
    near=min((abs(t-F(r,8)),r) for r in (1,3,5,7))[1]
    print(f"   {str(e):>14} {str(t):>12} {str(m*t):>11} {'r='+str(near):>18} {str(hits):>15}")

print()
print("   and the same for a perturbation in the MIDDLE of the pack:")
print(f"   {'perturbation':>14} {'subject':>8} {'cascade t':>12} {'u':>10} {'ideal r/8 lonely':>18}")
for e in [F(1,10),F(1,4),F(1,2)]:
    v=[F(1),F(2),F(3),F(4)+e,F(5),F(6),F(7),F(8)]
    for i in (0,3):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        t,n=cascade(ds)
        if t is None: continue
        m=min(ds)
        hits=[r for r in (1,3,5,7) if all(circd(d*(F(r,8)))>=TH for d in ds)]
        print(f"   {str(e):>14} {str(v[i]):>8} {str(t):>12} {str(m*t):>10} {str(hits):>18}")
