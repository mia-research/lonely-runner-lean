"""Intersect the -7 opening requirement with the blocker maximum at the largest flank.

Setting (framework's own objects, no imports):
  subject has 7 positive integer differences; the LARGEST is the flank e.
  openings of flank e are indexed k = 0..e-1  (period e, Theorem 6.13).
  mover d is in the way at opening k  iff  min(r, 8e-r) < e,  r = d*(8k+1) mod 8e.
  flank e is SHADOWED iff every k in 0..e-1 is blocked by some mover.

Two halves to intersect:
  (A) -7 requirement.  flank_clear_of_no_tiny: with |d| <= e and e | L*d for all d,
      the -7 opening is clear unless some mover is TINY: 7*|d| < e.
      So a shadowed flank REQUIRES a tiny mover.
  (B) blocker maximum.  How many movers actually do the covering.

Question: is {shadowed} inter {<= B blockers} inter {tiny present} empty for small B?
"""
import itertools, sys
from math import gcd

def blocked_ks(d, e):
    """set of opening indices k in [0,e) at which mover d is in the way at flank e"""
    out=set()
    M=8*e
    for k in range(e):
        r=(d*(8*k+1))%M
        if min(r, M-r) < e: out.add(k)
    return out

def analyse(e, movers):
    """returns (shadowed, min_blockers_needed, has_tiny, cover_per_mover)"""
    cov={d:blocked_ks(d,e) for d in movers}
    union=set().union(*cov.values()) if cov else set()
    shadowed = len(union)==e
    tiny = any(7*d < e for d in movers)
    mb=None
    if shadowed:
        for size in range(1,len(movers)+1):
            if any(len(set().union(*[cov[d] for d in sub]))==e
                   for sub in itertools.combinations(movers,size)):
                mb=size; break
    return shadowed, mb, tiny, {d:len(cov[d]) for d in movers}

if __name__=="__main__":
    EMAX=int(sys.argv[1]) if len(sys.argv)>1 else 24
    NMOV=6                      # 7 differences, one is the flank e itself
    tot=shad=0
    shad_no_tiny=[]
    by_blockers={}
    cover_lt_e=[]
    for e in range(2,EMAX+1):
        for movers in itertools.combinations(range(1,e+1), NMOV):
            if gcd(gcd(*movers), e)!=1: continue
            tot+=1
            sh,mb,tiny,cov=analyse(e,movers)
            if not sh: continue
            shad+=1
            by_blockers[mb]=by_blockers.get(mb,0)+1
            if not tiny: shad_no_tiny.append((e,movers))
            if sum(cov.values())<e: cover_lt_e.append((e,movers))
    print(f"flank e = 2..{EMAX}, {NMOV} movers, gcd(movers,e)=1")
    print(f"  difference sets examined : {tot:,}")
    print(f"  largest flank SHADOWED   : {shad:,}")
    print(f"  shadowed with NO tiny    : {len(shad_no_tiny)}   <-- must be 0 if (A) holds")
    if shad_no_tiny[:5]: print("      e.g.", shad_no_tiny[:5])
    print(f"  shadowed with sum(cover) < e : {len(cover_lt_e)}  <-- must be 0 (counting bound)")
    print("  minimum blockers needed to shadow:")
    for b in sorted(by_blockers): print(f"      {b} blockers : {by_blockers[b]:,}")
