# MECHANISM: making a runner the flank NEUTRALISES it -- at its own openings it sits exactly on
# the band edge and never blocks.  So choose as flank the runner that otherwise blocks MOST.
# That is parameterised by ds and has a reason, unlike 'largest'.
from math import gcd
from itertools import combinations
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    return any(all(clear(a,b,k) for a in ds) for k in range(b))
def blocks_at(ds,b,a):   # openings of flank b that runner a blocks
    return sum(1 for k in range(b) if not clear(a,b,k))
def worst_blocker_global(ds):
    # summed over all flanks, which runner blocks most openings?
    sc={a: sum(blocks_at(ds,b,a) for b in ds if b!=a) for a in ds}
    return max(sc, key=lambda a:(sc[a], a))
def worst_blocker_at_nearest(ds):
    m=min(ds)
    sc={a: blocks_at(ds,m,a) for a in ds if a!=m}
    return max(sc, key=lambda a:(sc[a], a)) if sc else m
RULES={
 "nearest (R1)":                lambda ds: min(ds),
 "largest (fitted)":            lambda ds: max(ds),
 "worst blocker, global":       worst_blocker_global,
 "worst blocker at nearest flank": worst_blocker_at_nearest,
}
for V in (14, 17):
    n=0; cov={k:0 for k in RULES}; comb1=0; comb2=0; left=[]
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        n+=1
        w={name: works(ds,f(ds)) for name,f in RULES.items()}
        for name in RULES:
            if w[name]: cov[name]+=1
        if w["nearest (R1)"] or w["worst blocker, global"]: comb1+=1
        else: left.append(ds)
        if w["nearest (R1)"] or w["largest (fitted)"]: comb2+=1
    print(f"[1,{V}]  {n} primitive sets")
    for name in RULES:
        print(f"    {name:34s} {cov[name]:6d}  ({cov[name]/n:.4f})")
    print(f"    {'R1 OR worst-blocker-global':34s} {comb1:6d}  ({comb1/n:.4f})   uncovered {len(left)}")
    print(f"    {'R1 OR largest (fitted)':34s} {comb2:6d}  ({comb2/n:.4f})")
    if left: print(f"      uncovered examples: {left[:4]}")
    print()
