import itertools,random,sys
from math import gcd
from collections import Counter
def blocked(d,e):
    M=8*e; return {k for k in range(e) if min((d*(8*k+1))%M, M-(d*(8*k+1))%M)<e}

# (1) max coverage by a SINGLE mover -> the counting floor
print("=== single-mover coverage, fraction of the e openings ===")
worst=0; arg=None
for e in range(2,121):
    for d in range(1,e+1):
        f=len(blocked(d,e))/e
        if f>worst: worst,arg=f,(d,e)
print(f"  max over e<=120, d<=e : {worst:.4f}  at (d,e)={arg}")
print(f"  counting floor on blockers = ceil(1/{worst:.4f}) = {-(-1//worst) if worst else 0}"
      f" -> at least {int(1/worst)+ (0 if abs(1/worst-int(1/worst))<1e-12 else 1)} movers")

# (2) is min-blockers >= 5 robust?  exhaustive small e, random large e
print("\n=== minimum blockers to shadow the largest flank ===")
def minblock(e,mv):
    cov={d:blocked(d,e) for d in mv}
    if len(set().union(*cov.values()))!=e: return None
    for s in range(1,len(mv)+1):
        if any(len(set().union(*[cov[d] for d in c]))==e for c in itertools.combinations(mv,s)):
            return s
mn=Counter(); shad=0
for e in range(2,27):
    for mv in itertools.combinations(range(1,e+1),6):
        if gcd(gcd(*mv),e)!=1: continue
        b=minblock(e,mv)
        if b: shad+=1; mn[b]+=1
print(f"  exhaustive e=2..26 : {shad:,} shadowed, min-blockers {dict(sorted(mn.items()))}")
random.seed(11); mn2=Counter(); shad2=0; tries=0
while shad2<4000 and tries<4_000_000:
    tries+=1
    e=random.randint(27,160)
    mv=tuple(sorted(random.sample(range(1,e+1),6)))
    if gcd(gcd(*mv),e)!=1: continue
    b=minblock(e,mv)
    if b: shad2+=1; mn2[b]+=1
print(f"  random  e=27..160 : {shad2:,} shadowed of {tries:,} draws, min-blockers {dict(sorted(mn2.items()))}")

# (3) the -7 requirement, restated as a ratio, at the same scale
print("\n=== e / d_min over shadowed flanks (the -7 requirement needs > 7) ===")
lo=99.0
for e in range(2,27):
    for mv in itertools.combinations(range(1,e+1),6):
        if gcd(gcd(*mv),e)!=1: continue
        if minblock(e,mv): lo=min(lo, e/min(mv))
print(f"  exhaustive e=2..26 : min e/d_min = {lo:.4f}   (clear-at--7 holds whenever <= 7)")
