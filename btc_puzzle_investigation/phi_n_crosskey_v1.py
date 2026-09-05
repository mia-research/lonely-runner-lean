#!/usr/bin/env python3
"""
#2  Cross-key / pairwise structure — relations BETWEEN different keys' points,
not each key vs its own n/k/d.

Diagnostic 0: are constructed d's within a band consecutive? (if so, P_{i+1}=P_i+G
  trivially — an artifact to note, not puzzle structure).
Probe A (φ(n)-native, constructed): do keys sharing a position-denominator n have
  CORRELATED points? Collision rate X_i≡X_j mod q among same-n pairs vs random
  pairs; permutation null on the n-labels.
Probe B (real 82 solved keys): low-weight scalar relations d_i±d_j among the
  actual puzzle keys, and X-residue collisions vs random. Small n — honest.
Exact int throughout.
"""
import csv, random
from math import gcd
import knd_common as K
rnd=random.Random(20260710)

c=K.load_decomp(64); X=c["X"];NS=c["n"];DS=c["d"];BITS=c["bits"];M=len(X)

# ---- Diagnostic 0: consecutive d within a band? ----
band={}
for i in range(M):
    band.setdefault(BITS[i],[]).append(DS[i])
b=sorted(band)[len(band)//2]; ds=sorted(band[b])[:6]
print(f"Diagnostic: band {b} first 6 d (sorted): {ds}")
print(f"  consecutive-integer construction? {'YES' if ds==list(range(ds[0],ds[0]+6)) else 'no (random draws)'}")
diffs=sorted(set(sorted(band[b])[i+1]-sorted(band[b])[i] for i in range(len(band[b])-1)))[:5]
print(f"  smallest gaps in band {b}: {diffs}\n")

# ---- Probe A: same-n point coupling ----
by_n={}
for i in range(M):
    by_n.setdefault(NS[i],[]).append(i)
groups=[g for g in by_n.values() if len(g)>=2]
same_pairs=[]
for g in groups:
    for a in range(len(g)):
        for bb in range(a+1,len(g)):
            same_pairs.append((g[a],g[bb]))
            if len(same_pairs)>=200000: break
        if len(same_pairs)>=200000: break
    if len(same_pairs)>=200000: break
rand_pairs=[(rnd.randrange(M),rnd.randrange(M)) for _ in range(len(same_pairs))]
print(f"Probe A: same-n pairs={len(same_pairs)} vs equal random pairs")
print(f"{'q':>4} {'same-n coll':>12} {'random coll':>12} {'perm p':>8}")
for q in (3,5,7,11,16,256):
    sc=sum(1 for i,j in same_pairs if X[i]%q==X[j]%q)
    rc=sum(1 for i,j in rand_pairs if X[i]%q==X[j]%q)
    # null: resample L random pairs B times, count collisions mod q; two-sided p
    B=300; L=len(same_pairs)
    blocknulls=[sum(1 for _ in range(L) if X[rnd.randrange(M)]%q==X[rnd.randrange(M)]%q)
                for _ in range(B)]
    ge=sum(1 for v in blocknulls if v>=sc)
    pp=(min(ge,B-ge)+1)/(B+1)*2
    print(f"{q:>4} {sc:>12} {rc:>12} {pp:>8.3f}")

# ---- Probe B: real 82 keys, scalar relations ----
RB=[];RD=[];RX=[]
with open("puzzles_verified.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N>=20:
            RB.append(N); RD.append(int(r["private_key"],16)); RX.append(int(r["X"],16))
m=len(RD)
print(f"\nProbe B: {m} real solved keys (N>=20)")
# low-weight scalar relations d_i - d_j small, or d_i ~ 2 d_j etc.
hits=0
for i in range(m):
    for j in range(m):
        if i==j: continue
        # d_i ≈ 2*d_j (adjacent bit-length doubling)?
        if RB[i]==RB[j]+1 and abs(RD[i]-2*RD[j])<2**(RB[j]-4):
            hits+=1
print(f"  d_i ≈ 2·d_j across adjacent bit-lengths (within 2^(N-4)): {hits}/{m} "
      f"(expected ~{m*1.0/8:.1f} by chance if uniform)")
# X-residue collisions among real keys vs random expectation
for q in (7,256):
    coll=sum(1 for i in range(m) for j in range(i+1,m) if RX[i]%q==RX[j]%q)
    exp=m*(m-1)//2/q
    print(f"  real-key X collisions mod {q}: {coll}  (expected {exp:.1f})")
