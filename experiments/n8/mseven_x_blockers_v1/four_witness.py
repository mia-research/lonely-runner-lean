import itertools,random
from math import gcd
from collections import Counter
def blocked(d,e):
    M=8*e; return {k for k in range(e) if min((d*(8*k+1))%M, M-(d*(8*k+1))%M)<e}
# For every 4-subset of movers, find which openings survive. Is there a UNIFORM witness?
print("=== 4 movers: which openings survive? ===")
allsurv=Counter(); nsurv=[]; fails=0; tot=0
for e in range(2,23):
    for mv in itertools.combinations(range(1,e+1),4):
        tot+=1
        u=set().union(*[blocked(d,e) for d in mv])
        s=set(range(e))-u
        nsurv.append(len(s))
        if not s: fails+=1
        else:
            for k in s: allsurv[k]+=1
print(f"  4-mover configs e=2..22 : {tot:,}")
print(f"  configs with NO surviving opening : {fails}")
print(f"  survivors per config: min={min(nsurv)} mean={sum(nsurv)/len(nsurv):.2f}")
print(f"  most frequent surviving opening index k: {allsurv.most_common(6)}")
# is k = e-1 (the -7 opening) always a survivor for 4 movers?
print("\n=== is the -7 opening (k = e-1) always clear against 4 movers? ===")
bad=[]
for e in range(2,31):
    for mv in itertools.combinations(range(1,e+1),4):
        if all(k!=e-1 for k in (set(range(e))-set().union(*[blocked(d,e) for d in mv]))):
            bad.append((e,mv))
            if len(bad)>=4: break
    if len(bad)>=4: break
print(f"  counterexamples: {bad if bad else 'NONE found e=2..30'}")
# and against 5?
print("\n=== smallest number of movers that can cover k = e-1 AND everything else ===")
for e in range(2,23):
    found=None
    for r in range(1,7):
        for mv in itertools.combinations(range(1,e+1),r):
            if len(set().union(*[blocked(d,e) for d in mv]))==e: found=(r,mv); break
        if found: break
    if found and e<=14: print(f"   e={e:3d} -> {found[0]} movers {found[1]}")
