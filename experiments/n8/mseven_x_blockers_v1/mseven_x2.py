import itertools,sys
from math import gcd
from collections import Counter
def blocked(d,e):
    M=8*e; return {k for k in range(e) if min((d*(8*k+1))%M, M-(d*(8*k+1))%M)<e}
EMAX=int(sys.argv[1])
minb=Counter(); active=Counter(); tinyratio=[]; ex5=[]
shad=0
for e in range(2,EMAX+1):
    for mv in itertools.combinations(range(1,e+1),6):
        if gcd(gcd(*mv),e)!=1: continue
        cov={d:blocked(d,e) for d in mv}
        if len(set().union(*cov.values()))!=e: continue
        shad+=1
        nact=sum(1 for d in mv if cov[d])          # movers that block ANY opening
        active[nact]+=1
        mb=next(s for s in range(1,7)
                if any(len(set().union(*[cov[d] for d in c]))==e
                       for c in itertools.combinations(mv,s)))
        minb[mb]+=1
        t=min(mv)
        tinyratio.append(e/t)
        if mb==5 and len(ex5)<6: ex5.append((e,mv,round(e/t,2)))
print(f"e=2..{EMAX}: shadowed largest flanks = {shad:,}")
print(" min blockers needed :", dict(sorted(minb.items())))
print(" movers that block at all :", dict(sorted(active.items())))
print(f" e/d_min over shadowed cases: min={min(tinyratio):.2f}  max={max(tinyratio):.1f}")
print(f"   (-7 clear needs e/d_min <= 7; shadowed needs > 7)")
print(" examples needing exactly 5 blockers (e, movers, e/d_min):")
for x in ex5: print("   ",x)
