"""Item 4: what does clear_of_reading_le_gen say at orders already closed (n = 3..7)?
Item 5: consequence of the 'd_min never fails' ceiling.

Item 4 -- at order n the criterion is  c <= a mod nc <= (n-1)c,  and S <= n-1 forces it.  Measure,
per order, the fraction clearing at d_min and the fraction with S <= n-1.

Item 5 -- at order n, d_min never fails, so at most n-2 of the n-1 disparities do.  When EXACTLY
ONE fails the move is forced (a max over one candidate), so the whole k=1 rung is explicit for those
subjects.  Measure how large that class is and how often it clears at k=1.
All speeds positive (generalised frame guard: n distinct positive speeds)."""
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def cascade(ds,n):
    TH=F(1,n)
    def nextOp(d,t):
        k=floor(d*t-TH)
        while F(k)+TH<d*t: k+=1
        if k<0: k=0
        return (F(k)+TH)/d
    t=TH/min(ds); m=0
    while m<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return m
        t=max(nextOp(d,t) for d in b); m+=1
    return None
print("=== item 4: the criterion at orders 3..8 ===")
print(f"  {'n':>2}  {'clear at d_min':>15}  {'S <= n-1':>10}  {'S<=n-1 => clear':>16}")
for n in range(3,9):
    rng=random.Random(50+n); tot=cl=sle=viol=0
    for _ in range(4000):
        v=sorted(rng.sample(range(1,60),n))
        g=gcd_all(v)
        for i in range(n):
            ds=[abs(v[j]-v[i])//g for j in range(n) if j!=i]
            c=min(ds); S=F(max(ds),c)
            ok=all(c <= a%(n*c) <= (n-1)*c for a in ds)
            tot+=1; cl+=ok
            if S<=n-1:
                sle+=1
                if not ok: viol+=1
    print(f"  {n:>2}  {cl/tot:>15.4f}  {sle/tot:>10.4f}  {'0 violations' if viol==0 else str(viol)+' VIOL':>16}")

print("\n=== item 5: the single-failure class ===")
n=8; rng=random.Random(321)
nf=Counter(); one_k1=0; one_tot=0; multi_k1=0; multi_tot=0
for _ in range(3000):
    v=sorted(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        dsr=[abs(v[j]-v[i])//g for j in range(8) if j!=i]
        c=min(dsr)
        bad=[a for a in dsr if not (c <= a%(8*c) <= 7*c)]
        nf[len(bad)]+=1
        if not bad: continue
        d=cascade([F(a*g) for a in dsr],8)
        if d is None: continue
        if len(bad)==1: one_tot+=1; one_k1 += (d==1)
        else:           multi_tot+=1; multi_k1 += (d==1)
print(f"  failing-disparity count: {dict(sorted(nf.items()))}")
print(f"  EXACTLY ONE failure : {one_tot} subjects, of which depth == 1: {one_k1}  ({one_k1/one_tot:.4f})")
print(f"  TWO OR MORE         : {multi_tot} subjects, of which depth == 1: {multi_k1}  ({multi_k1/multi_tot:.4f})")
print("  => a single failure makes the first move FORCED (max over one candidate); the question is")
print("     whether it then clears, which is clear_at_scale_iff at the new (e, N).")
