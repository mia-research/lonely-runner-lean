"""Owner: "varying speed shifts the isolation point -- does it shift who the runner's neighbours
are?"

At the isolation instant the subject has two TRACK neighbours (nearest ahead, nearest behind), and
lonelyAt_iff_neighbours says only those two bind.  Track their IDENTITY as the speeds deform."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds, disparities
from fractions import Fraction as F
from math import floor
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def frac(x): return x-floor(x)
def neighbours(v,i,t):
    """who is nearest AHEAD and nearest BEHIND the subject at time t"""
    sep=[(frac((v[j]-v[i])*t), j) for j in range(8) if j!=i]
    ahead=min(sep)[1]; behind=max(sep)[1]
    return ahead,behind
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    m=min(ds); t=TH/m; n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

AP=speeds([1,2,3,4,5,6,7,8])
print("=== the AP: the subject's neighbours at each of the four isolation instants ===")
print(f"   {'subject':>8}  " + "  ".join(f"r={r}" for r in (1,3,5,7)))
for i in range(8):
    row=[]
    for r in (1,3,5,7):
        a,b=neighbours(AP,i,F(r,8))
        row.append(f"({AP[a]},{AP[b]})")
    print(f"   {AP[i]:>8}  " + "  ".join(f"{c:>9}" for c in row))
print("   (ahead, behind) by SPEED.  At r=1 they are the speed-neighbours; at r=3,5,7 they are not.")

print()
print("=== deforming the AP: does the binding pair move? ===")
print(f"   {'perturbation':>13} {'cascade t':>10} {'ahead':>8} {'behind':>8} {'flank (at exactly 1/8)':>24}")
for e in [F(0),F(1,20),F(1,10),F(1,4),F(1,2),F(1),F(3,2),F(2)]:
    v=speeds([F(1),F(2),F(3),F(4),F(5),F(6),F(7),F(8)+e])
    i=0
    ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
    t,n=cascade(ds)
    if t is None: continue
    a,b=neighbours(v,i,t)
    fl=[str(v[j]) for j in range(8) if j!=i and circd((v[j]-v[i])*t)==TH]
    print(f"   {str(e):>13} {str(t):>10} {str(v[a]):>8} {str(v[b]):>8} {str(fl):>24}")

print()
print("=== in general: is the binding neighbour the SPEED-neighbour? ===")
rng=random.Random(31); cnt=Counter(); tot=0
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        t,n=cascade(ds)
        if t is None: continue
        a,b=neighbours(v,i,t)
        dmin=min(abs(v[j]-v[i]) for j in range(8) if j!=i)
        tot+=1
        cnt['ahead is a speed-neighbour' if abs(v[a]-v[i])==dmin else 'ahead is not']+=1
        cnt['behind is a speed-neighbour' if abs(v[b]-v[i])==dmin else 'behind is not']+=1
        cnt['either is'] += 1 if (abs(v[a]-v[i])==dmin or abs(v[b]-v[i])==dmin) else 0
for k in ['ahead is a speed-neighbour','behind is a speed-neighbour','either is']:
    print(f"   {k:>28}: {cnt[k]/tot:.4f}")
print(f"   ({tot} subject-instances)")
