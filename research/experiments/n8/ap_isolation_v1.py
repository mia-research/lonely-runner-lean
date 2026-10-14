"""THE DECISIVE TEST.

A band-2 counterexample needs BOTH:
   (1) S > 7            -- else R = 1 by Corollary 6.21
   (2) cover [1,7] u [9,15]  -- else some point is clear and R < 16

The AP (readings 2..7) satisfies (2) exactly but has S = 7, failing (1).  So: does raising S alone
past 7 keep the covering?  Test single-coordinate perturbations, not the all-coordinate one."""
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
print("  raising ONLY the largest reading past 7 (readings 2,3,4,5,6,7+eps):\n")
print(f"    {'eps':>8} {'S':>8} {'unc [1,7]':>12} {'unc [9,15]':>12} {'joint':>11}")
for e in (0.0, 1e-6, 1e-4, 0.001, 0.01, 0.05, 0.1, 0.25, 0.45):
    S=[2.0,3.0,4.0,5.0,6.0,7.0+e]
    print(f"    {e:>8g} {7.0+e:>8.4f} {uncovered(S,1.0,7.0):>12.8f} {uncovered(S,9.0,15.0):>12.8f} {joint(S):>11.8f}")
print()
print("  and adding a NEW large reading instead (2,3,4,5,6,7 is six already, so replace one):")
for lab,S in (("7 -> 7.45",[2.0,3.0,4.0,5.0,6.0,7.45]),
              ("6 -> 7.45",[2.0,3.0,4.0,5.0,7.0,7.45]),
              ("2 -> 7.45",[3.0,4.0,5.0,6.0,7.0,7.45]),
              ("all +0.45",[2.45,3.45,4.45,5.45,6.45,7.45])):
    print(f"    {lab:>12}: joint uncovered {joint(S):.8f}   ([1,7] {uncovered(S,1.0,7.0):.6f}, [9,15] {uncovered(S,9.0,15.0):.6f})")
print()
print("  SEARCH, constrained to S > 7: minimise joint uncovered")
rng=random.Random(777)
best=(99.0,None)
for restart in range(800):
    if restart%2==0:
        S=[2.0,3.0,4.0,5.0,6.0,7.0]
        S=[x+rng.gauss(0,0.08) for x in S]
        S[5]=max(S[5], 7.0+1e-6)
    else:
        S=sorted(rng.uniform(1.02,7.98) for _ in range(5))+[rng.uniform(7.0+1e-6,7.98)]
    S=sorted(S)
    if S[5]<=7.0: continue
    cur=joint(S); stall=0
    for _ in range(4000):
        W=list(S); k=rng.randrange(6); W[k]+=rng.gauss(0,0.02)
        W=sorted(W)
        if W[0]<=1.02 or W[5]<=7.0 or W[5]>7.99: continue
        v=joint(W)
        if v<cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>500: break
    if cur<best[0]: best=(cur,tuple(S))
print(f"    minimum joint uncovered with S > 7 : {best[0]:.8f}")
print(f"    readings {[round(x,5) for x in best[1]]}   S = {best[1][5]:.6f}")
print(f"      [1,7] {uncovered(list(best[1]),1.0,7.0):.8f}   [9,15] {uncovered(list(best[1]),9.0,15.0):.8f}")
