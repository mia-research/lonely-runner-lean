"""OOS retest of the group-law k=128 candidate. Fresh seeds for pool AND arms. Same design."""
import random, sys
from interval_multireadout_v3 import (pool_pts, pool_table, counts_from_table, stats,
                                      group_classes, counts_of, jmul, N)
KS=(40,64,96,128,135,160,200); M,R,NP=160,3000,600
print("OOS retest -- group-law difference, fresh seeds. In-sample fire was k=128 @ 99.4 pctile.\n")
print(f"{'seed':>6} | " + " | ".join(f"k={k}" for k in KS))
fires={k:0 for k in KS}
for seed in (11,22,33,44,55):
    rng=random.Random(seed)
    pool=pool_pts(NP,rng); T=pool_table(pool,"group")
    idx=list(range(NP))
    nl=[stats(counts_from_table(T,rng.sample(idx,M)))[1] for _ in range(R)]
    nl.sort(); q99=nl[int(.99*R)]
    row=[]
    for k in KS:
        lo,hi=2**(k-1),2**k
        e=stats(counts_of(group_classes([jmul(rng.randrange(lo,hi)) for _ in range(M)])))[1]
        pc=100.0*sum(1 for z in nl if z<e)/len(nl)
        if e>=q99: fires[k]+=1
        row.append(f"{pc:5.1f}%" + ("*" if e>=q99 else " "))
    print(f"{seed:>6} | " + " | ".join(row), flush=True)
print(f"\nfires out of 5 fresh seeds: " + ", ".join(f"k={k}: {v}/5" for k,v in fires.items()))
print("(* = at or above that seed's own 99th percentile)")
