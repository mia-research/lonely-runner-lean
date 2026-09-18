"""The (e,k) certificate, built as CONSTRUCTIVE COVERAGE + RESIDUE, not as a covering proof.
Each criterion NAMES the instant (flank e, opening k) -- Thm 6.12's band condition, of which
Thm 4.8 is the k=0 case at e=d_min.  We apply them in order of k and characterise what is LEFT,
because the residue is the only thing that still needs an argument.  Exact Fraction.  2026-09-18."""
import random
from fractions import Fraction as F
from math import floor
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def lonely_at(us,j,k):
    t=(F(k)+TH)/us[j]
    return all(circd(u*t)>=TH for u in us)
def min_ek(us,KMAX=60):
    """smallest k for which SOME flank works; returns (k, flank index, rank from largest)"""
    n=len(us)
    for k in range(KMAX+1):
        for j in range(n-1,-1,-1):          # try largest flank first
            if lonely_at(us,j,k): return k,j,(n-j)
    return None,None,None

def sample(rng,Slo,Shi,D=1000):
    top=F(rng.randint(int(Slo*D),int(Shi*D)),D)
    us={F(1),top}
    while len(us)<7: us.add(F(rng.randint(D,int(top*D)),D))
    return sorted(us)

def near_int_count(us,j):
    """how many ratios to flank j are within 1/8 of an integer (the near-sharers of that flank)"""
    return sum(1 for u in us if circd(u/us[j])< TH)

for (Slo,Shi,label) in [(7,8,"hard band  S in [7,8]"),(8,12,"S in [8,12]"),(12,20,"S in [12,20]"),(20,40,"S in [20,40]")]:
    rng=random.Random(1234)
    hist={}; resid=[]
    N=6000
    for _ in range(N):
        us=sample(rng,Slo,Shi)
        k,j,rank=min_ek(us)
        if k is None: resid.append((us,None,None)); continue
        hist[k]=hist.get(k,0)+1
        if k>=3: resid.append((us,k,rank))
    tot=sum(hist.values())
    print(f"\n=== {label}   n = {tot} ===")
    cum=0
    print(f"   {'k':>3} {'settled':>8} {'cumulative':>12}")
    for k in sorted(hist):
        cum+=hist[k]
        print(f"   {k:>3} {hist[k]:>8} {cum/tot:>11.4f}")
    # which flank rank is used
    rng=random.Random(1234); ranks={}
    for _ in range(N):
        us=sample(rng,Slo,Shi)
        k,j,rank=min_ek(us)
        if rank is not None: ranks[rank]=ranks.get(rank,0)+1
    print(f"   flank rank from the LARGEST that supplies the instant: {dict(sorted(ranks.items()))}")
    if resid:
        ks=[k for _,k,_ in resid if k is not None]
        print(f"   residue (k >= 3): {len(resid)} of {tot}  ({len(resid)/tot:.5f})   max k = {max(ks) if ks else 'n/a'}")
        us,k,rank=max(((u,k,r) for u,k,r in resid if k is not None),key=lambda z:z[1])
        print(f"   worst residue member: k = {k}, flank rank {rank}")
        print(f"      readings {[round(float(u),4) for u in us]}")
        print(f"      near-integer ratios to each flank: {[near_int_count(us,j) for j in range(7)]}")
