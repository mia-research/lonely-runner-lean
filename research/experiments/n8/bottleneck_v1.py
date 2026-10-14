"""The split says [1,7] and [9,15] are independent problems on the SAME six readings.
Never measured: which one is the bottleneck?

For each profile, measure the UNCOVERED length in each region separately.  Band 2 needs both to hit
zero.  If one region is systematically the harder, that is where the obstruction lives."""
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
    unc=hi-lo; 
    for a,b in merged: unc-=(b-a)
    return max(unc,0.0)
rng=random.Random(20260919)
rows=[]
for _ in range(60000):
    S=sorted(rng.uniform(1.02,7.98) for _ in range(6))
    u1=uncovered(S,1.0,7.0); u2=uncovered(S,9.0,15.0)
    rows.append((u1,u2))
print(f"  {len(rows)} random profiles (six interior readings in (1.02, 7.98))\n")
print(f"  uncovered in [1, 7] : min {min(r[0] for r in rows):.5f}  mean {st.mean(r[0] for r in rows):.4f}")
print(f"  uncovered in [9,15] : min {min(r[1] for r in rows):.5f}  mean {st.mean(r[1] for r in rows):.4f}")
print(f"\n  which region is harder (larger uncovered)?")
h1=sum(1 for a,b in rows if a>b); h2=sum(1 for a,b in rows if b>a)
print(f"    [1,7] harder : {h1}  ({h1/len(rows):.4f})")
print(f"    [9,15] harder: {h2}  ({h2/len(rows):.4f})")
print(f"\n  profiles achieving uncovered < 0.01 in each region:")
n1=sum(1 for a,b in rows if a<0.01); n2=sum(1 for a,b in rows if b<0.01)
nb=sum(1 for a,b in rows if a<0.01 and b<0.01)
print(f"    [1,7] nearly covered  : {n1}")
print(f"    [9,15] nearly covered : {n2}")
print(f"    BOTH                  : {nb}")
print(f"\n  now optimise each region SEPARATELY and see the best achievable:")
def opt(lo,hi,restarts=400,steps=2500):
    best=(hi-lo,None)
    for _ in range(restarts):
        S=sorted(rng.uniform(1.02,7.98) for _ in range(6))
        cur=uncovered(S,lo,hi); stall=0
        for _ in range(steps):
            W=list(S); k=rng.randrange(6); W[k]+=rng.gauss(0,0.05)
            W=sorted(W)
            if W[0]<=1.02 or W[5]>7.98: continue
            v=uncovered(W,lo,hi)
            if v<cur: S,cur,stall=W,v,0
            elif v==cur: S,stall=W,stall+1
            else: stall+=1
            if stall>300: break
        if cur<best[0]: best=(cur,tuple(S))
    return best
b1=opt(1.0,7.0); b2=opt(9.0,15.0)
print(f"    best uncovered in [1, 7] : {b1[0]:.6f}   readings {[round(x,4) for x in b1[1]]}")
print(f"       that profile's uncovered in [9,15]: {uncovered(list(b1[1]),9.0,15.0):.6f}")
print(f"    best uncovered in [9,15] : {b2[0]:.6f}   readings {[round(x,4) for x in b2[1]]}")
print(f"       that profile's uncovered in [1, 7]: {uncovered(list(b2[1]),1.0,7.0):.6f}")
