"""If R < 16 for every profile then Existence at order 8 follows (R finite = CascadeCapped =
Existence, and the band theorem confines R to [1,7] u [9,15] u [17,23] u ...).

R >= 17 requires the six non-minimal readings to COVER [1,7] u [9,15] entirely -- 12 units.
Measure how close they ever get: maximise the covered fraction directly.

NOTE -- this is a covering formulation, which sec 6A bans in the cascade framework.  It is derived
from the framework's own objects rather than imported, but the ban is the owner's to interpret and
BS_TRANSFER_v1 sec 4's firewall question is still unruled.  Flagged, not assumed.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
import random
BANDS=[(1.0,7.0),(9.0,15.0)]
TOTAL=sum(b-a for a,b in BANDS)
def uncovered(S):
    """total length of [1,7] u [9,15] NOT covered by the bad sets of s in S (s != 1)"""
    iv=[]
    for a,b in BANDS: iv.append((a,b))
    bad=[]
    for s in S:
        k=0
        while (8*k+1)/s <= 15.5:
            lo=(8*k-1)/s; hi=(8*k+1)/s
            if hi>=1.0: bad.append((max(lo,0.0),hi))
            k+=1
    bad.sort()
    merged=[]
    for lo,hi in bad:
        if merged and lo<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],hi))
        else: merged.append((lo,hi))
    unc=0.0
    for a,b in iv:
        pos=a
        for lo,hi in merged:
            if hi<=pos: continue
            if lo>=b: break
            if lo>pos: unc+=min(lo,b)-pos
            pos=max(pos,hi)
            if pos>=b: break
        if pos<b: unc+=b-pos
    return unc
rng=random.Random(9090)
best=(TOTAL, None)
for restart in range(3000):
    S=sorted(rng.uniform(1.05,7.95) for _ in range(6))
    cur=uncovered(S); stall=0
    for _ in range(3000):
        W=list(S); k=rng.randrange(6)
        W[k]+=rng.gauss(0,0.06)
        W=sorted(W)
        if W[0]<=1.02 or W[5]>15.0 or any(W[i+1]-W[i]<0.02 for i in range(5)): continue
        v=uncovered(W)
        if v<cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>400: break
    if cur<best[0]: best=(cur,tuple(W))
unc,S=best
print(f"  target region [1,7] u [9,15], total length {TOTAL}")
print(f"  minimum UNCOVERED length found : {unc:.6f}   ({unc/TOTAL:.4%} of the region)")
print(f"  maximum covered fraction        : {1-unc/TOTAL:.4%}")
print(f"  best six readings: " + " ".join(f"{x:.4f}" for x in S))
print(f"\n  a counterexample (band 2) needs uncovered = 0 exactly.")
print(f"  available bad measure: 6 combs x 1/4 x 12 units = {6*0.25*12:.0f} units against 12 needed.")
print(f"  so the measure is there ({6*0.25*12/12:.2f}x) and the shortfall is pure interlocking.")
