"""Each region is separately coverable, by OPPOSITE profiles -- yet the AP covers the combined
region to 0.000211.  How does the AP resolve the tension, and what is its residual in each region?

Then: optimise the JOINT uncovered (both regions) and see whether anything beats the AP."""
import sys; sys.path.insert(0,'experiments/n8')
import random, statistics as st
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
AP=[2.0,3.0,4.0,5.0,6.0,7.0]
print(f"  THE AP, readings {AP}:")
print(f"    uncovered in [1, 7] : {uncovered(AP,1.0,7.0):.8f}")
print(f"    uncovered in [9,15] : {uncovered(AP,9.0,15.0):.8f}")
print(f"    joint               : {joint(AP):.8f}")
print(f"    -> it covers BOTH regions completely, up to measure zero.  The residual is the eight")
print(f"       protected odd integers, which have no length.\n")
print("  perturbing the AP: how fast does uncovered length appear?")
print(f"    {'delta':>8} {'unc [1,7]':>12} {'unc [9,15]':>12} {'joint':>10}")
for d in (0.0, 0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2):
    S=[2.0+d,3.0-d,4.0+d,5.0-d,6.0+d,7.0-d]
    print(f"    {d:>8.3f} {uncovered(S,1.0,7.0):>12.6f} {uncovered(S,9.0,15.0):>12.6f} {joint(S):>10.6f}")
print()
print("  joint optimisation -- can anything beat the AP?")
rng=random.Random(4242)
best=(joint(AP), tuple(AP), "AP")
for restart in range(600):
    if restart%3==0: S=[x+rng.gauss(0,0.15) for x in AP]
    else: S=sorted(rng.uniform(1.02,7.98) for _ in range(6))
    S=sorted(S)
    if S[0]<=1.02 or S[5]>7.98: continue
    cur=joint(S); stall=0
    for _ in range(3000):
        W=list(S); k=rng.randrange(6); W[k]+=rng.gauss(0,0.03)
        W=sorted(W)
        if W[0]<=1.02 or W[5]>7.98: continue
        v=joint(W)
        if v<cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>400: break
    if cur<best[0]: best=(cur,tuple(S),"search")
print(f"    best joint uncovered : {best[0]:.8f}   via {best[2]}")
print(f"    readings: {[round(x,5) for x in best[1]]}")
print(f"      in [1,7]:  {uncovered(list(best[1]),1.0,7.0):.8f}")
print(f"      in [9,15]: {uncovered(list(best[1]),9.0,15.0):.8f}")
