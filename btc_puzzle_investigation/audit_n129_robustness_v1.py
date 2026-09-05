#!/usr/bin/env python3
"""
ADVERSARIAL SELF-AUDIT of this session's n=129 / consecutive-coupling result.
Attacking my own positive finding for the holes I glossed:

 H1. NMAX=256 is an ARBITRARY cap. best_nk searches n<=256. n=129 and n=256 sit
     near it. Does the 58/59/60 collision SURVIVE other caps, or is it a boundary
     artifact of choosing 256?  (recompute n under NMAX in {64,128,256,512,1024,4096}.)
 H2. best_nk vs a STANDARD implementation. Cross-check every key against
     Fraction((d-A),A).limit_denominator(NMAX) (stdlib, well-tested). Resolve the
     15 disagreements with the stored n_exact column: which pipeline is right?
 H3. Null-P stability vs POOL size (is p=0.001 an artifact of a 4000-sample pool?).
 H4. Re-derive the collision p-value using the STANDARD limit_denominator decomp,
     not my best_nk, to confirm the signal is not best_nk-specific.
 H5. Are the 58/59/60 private keys the actually-documented ones? (print them.)
"""
import csv, random
from fractions import Fraction
from knd_common import best_nk

def std_nk(d, N, NMAX):
    A = 1 << (N-1)
    fr = Fraction(d-A, A).limit_denominator(NMAX)
    return fr.denominator, fr.numerator

MASTER="btc_puzzle_master_exact.csv"
rows=[]
with open(MASTER) as fh:
    for r in csv.DictReader(fh):
        if r["status"]!="SOLVED": continue
        rows.append((int(r["puzzle"]),int(r["bits"]),int(r["priv_dec"]),
                     r.get("n_exact","")))
rows.sort()

print("H5. private keys for the collision run:")
for p,N,d,_ in rows:
    if p in (58,59,60,50,51,9,10):
        print(f"   #{p} bits={N} d={d} (hex {d:x})")

print("\nH1. n under different denominator caps (does 58/59/60 stay equal?):")
caps=[64,128,256,512,1024,4096]
print("   puzzle |", " ".join(f"N<={c:<5d}" for c in caps))
for p,N,d,_ in rows:
    if p in (12,22,50,51,58,59,60,9,10,90):
        ns=[best_nk(d,N)[0] if c==256 else std_nk(d,N,c)[0] for c in caps]
        # use std_nk for all caps for consistency (best_nk fixed at 256):
        ns=[std_nk(d,N,c)[0] for c in caps]
        print(f"   #{p:6d} |", " ".join(f"{x:<7d}" for x in ns))

print("\nH2. best_nk vs stdlib limit_denominator @256, and vs stored n_exact:")
dis_bestnk_std=0; dis_stored=0
for p,N,d,n_stored in rows:
    nb,_=best_nk(d,N); ns,_=std_nk(d,N,256)
    tag=""
    if nb!=ns: dis_bestnk_std+=1; tag+=f"  best_nk={nb} std={ns} DIFFER"
    if n_stored.split(".")[0].strip().lstrip("-").isdigit():
        if int(n_stored.split(".")[0])!=nb: dis_stored+=1; tag+=f"  stored={n_stored}"
    if tag: print(f"   #{p:3d} bits={N}{tag}")
print(f"   -> best_nk vs stdlib disagree on {dis_bestnk_std}/{len(rows)}")
print(f"   -> best_nk vs stored n_exact disagree on {dis_stored}/{len(rows)}")

print("\nH3+H4. collision p-value: best_nk vs stdlib decomp, and pool-size stability")
def maxrun(nvec,pvec):
    best=cur=1
    for i in range(1,len(pvec)):
        cur=cur+1 if (pvec[i]==pvec[i-1]+1 and nvec[i]==nvec[i-1]) else 1
        best=max(best,cur)
    return best
def consec(nvec,pvec):
    return sum(1 for i in range(1,len(pvec)) if pvec[i]==pvec[i-1]+1 and nvec[i]==nvec[i-1])

sub=[(p,N,d) for p,N,d,_ in rows if N>=20]
pvec=[p for p,_,_ in sub]
for decomp_name, fn in (("best_nk", lambda d,N: best_nk(d,N)[0]),
                        ("stdlib256", lambda d,N: std_nk(d,N,256)[0])):
    nvec=[fn(d,N) for _,N,d in sub]
    obs_run=maxrun(nvec,pvec); obs_con=consec(nvec,pvec)
    for POOL in (2000, 8000):
        random.seed(20260711)
        pools={}
        for _,N,_ in sub:
            if N in pools: continue
            lo,hi=1<<(N-1),1<<N
            pools[N]=[fn(random.randrange(lo,hi),N) for _ in range(POOL)]
        R=100000; ge_run=ge_con=0
        for _ in range(R):
            sim=[random.choice(pools[N]) for _,N,_ in sub]
            if maxrun(sim,pvec)>=obs_run: ge_run+=1
            if consec(sim,pvec)>=obs_con: ge_con+=1
        print(f"   {decomp_name:9s} POOL={POOL:5d}: maxrun obs={obs_run} p={ge_run}/{R}"
              f"   consec obs={obs_con} p={ge_con}/{R}")
