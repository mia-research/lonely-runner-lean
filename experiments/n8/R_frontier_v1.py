"""At the R-maximiser the binding constraint is s_7.R = 89 = 8.11+1 exactly -- the LARGEST reading
on the lower edge of a clear band.  So R = 89/s_7, bounded above by 89/7 = 12.714 as s_7 -> 7.
But s_7 <= 7 clears immediately (S <= 7 => depth 0).  Map that tension: max R as a function of S.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
import random
def clear(S,R):
    for s in S:
        m=(s*R)%8.0
        if m<1.0 or m>7.0: return False
    return True
def Rdir(S, RMAX=40.0):
    c=[1.0]
    for s in S:
        k=1
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        if clear(S,R+1e-12): return R
    return None
rng=random.Random(777)
print(f"  {'S (=s_7)':>10} {'max R':>10} {'89/S':>9} {'(8k+1)/S at max':>16}  profile")
rows=[]
for Sfix in [7.02,7.05,7.1,7.15,7.2,7.3,7.4,7.45,7.5,7.6,7.7,7.8,7.9,7.95]:
    best=(0,None)
    for restart in range(400):
        S=[1.0]+sorted(rng.uniform(1.05,Sfix-0.02) for _ in range(5))+[Sfix]
        cur=Rdir(S) or 0; stall=0
        for _ in range(2500):
            W=list(S); k=rng.randrange(1,6)
            W[k]+=rng.gauss(0,0.05)
            W=[1.0]+sorted(W[1:6])+[Sfix]
            if W[1]<=1.02 or any(W[i+1]-W[i]<0.02 for i in range(6)): continue
            v=Rdir(W) or 0
            if v>cur: S,cur,stall=W,v,0
            elif v==cur: S,stall=W,stall+1
            else: stall+=1
            if stall>400: break
        if cur>best[0]: best=(cur,tuple(W))
    R=best[0]
    kk=round((R*Sfix-1)/8) if R else 0
    rows.append((Sfix,R))
    print(f"  {Sfix:>10.3f} {R:>10.5f} {89/Sfix:>9.4f} {(8*kk+1)/Sfix if R else 0:>16.5f}  "
          + " ".join(f"{x:.3f}" for x in (best[1] or [])))
print()
mx=max(rows,key=lambda r:r[1])
print(f"  max over the scan: R = {mx[1]:.6f} at S = {mx[0]}")
print(f"  R stays below 12 throughout: {all(r[1]<12 for r in rows)}")
print(f"\n  note the ceiling 89/S is only attainable if the other six readings can dodge;")
print(f"  as S -> 7 the whole configuration clears early instead, so the frontier is interior.")
