"""CLAIM taking shape: for every profile with S > 7, the joint uncovered length is POSITIVE --
hence a clear point exists in [1,7] u [9,15], hence R < 16, hence band 2 is unreachable.

Near the AP it is quantitative: joint uncovered ~ (22/7)(S - 7).
Now test it WELL AWAY from the AP, with no cap on S and readings anywhere in (1, 40)."""
import sys; sys.path.insert(0,'experiments/n8')
import random
def uncovered(S, lo, hi):
    bad=[]
    for s in S:
        k=0
        while (8*k-1)/s <= hi+1:
            a,b=(8*k-1)/s,(8*k+1)/s
            if b>lo and a<hi: bad.append((max(a,lo),min(b,hi)))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    unc=hi-lo
    for a,b in merged: unc-=(b-a)
    return max(unc,0.0)
def joint(S): return uncovered(S,1.0,7.0)+uncovered(S,9.0,15.0)
rng=random.Random(31337)
print("  minimising joint uncovered subject to S > 7, readings free in (1, HI)\n")
print(f"  {'HI':>5} {'min joint uncovered':>21} {'S at min':>10}  readings")
for HI in (8.0, 10.0, 16.0, 24.0, 40.0):
    best=(99.0,None)
    for restart in range(700):
        mode=restart%3
        if mode==0:
            S=sorted([2.0,3.0,4.0,5.0,6.0,7.0+rng.uniform(1e-6,0.2)])
        elif mode==1:
            S=sorted(rng.uniform(1.02,min(HI,8.0)) for _ in range(5))+[rng.uniform(7.0001,HI)]
        else:
            S=sorted(rng.uniform(1.02,HI) for _ in range(6))
        S=sorted(S)
        if S[5]<=7.0: continue
        cur=joint(S); stall=0
        for _ in range(3000):
            W=list(S); k=rng.randrange(6); W[k]*= (1+rng.gauss(0,0.01))
            W=sorted(W)
            if W[0]<=1.02 or W[5]<=7.0 or W[5]>HI: continue
            v=joint(W)
            if v<cur: S,cur,stall=W,v,0
            elif v==cur: S,stall=W,stall+1
            else: stall+=1
            if stall>400: break
        if cur<best[0]: best=(cur,tuple(S))
    u,S=best
    print(f"  {HI:>5.0f} {u:>21.9f} {S[5]:>10.6f}  {[round(x,4) for x in S]}")
print()
print("  is the minimum always achieved by S -> 7+ ?  (i.e. hugging the AP)")
print("  and is joint uncovered ALWAYS > 0 when S > 7?")
zero=0; tot=0; worst=None
for _ in range(200000):
    S=sorted(rng.uniform(1.02,12.0) for _ in range(6))
    if S[5]<=7.0: continue
    tot+=1; u=joint(S)
    if u<=0.0: zero+=1; worst=S
print(f"    {tot} random profiles with S > 7 : joint uncovered == 0 in {zero}")
if worst: print(f"      WITNESS {worst}")
