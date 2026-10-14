"""Are the conditions of section 10 jointly exhaustive at order 8?
Exhibit, or fail to exhibit, a difference set on which ALL of R1-R7 fail.
Each rule tested by its stated condition, exactly."""
from math import gcd
from itertools import combinations
N=8
def clear_at(ds,e,j):
    a=N*j+1
    return all(e<=(d*a)%(N*e)<=(N-1)*e for d in ds)
def R1(ds): return max(ds)<=(N-1)*min(ds)
def R6(ds): return any(all(d%q for d in ds) for q in range(2,N+1))
def R3(ds): return all(d%N for d in ds) and any(gcd(e,N)==1 for e in ds)
def R5(ds): return sum(1 for d in ds if d%N)<=1
def R4(ds):
    if N not in (2,3,5,7,11,13): return False          # n=8 is not prime
    return False
def R2(ds):
    # band ladder: some flank e, index j, lap L with every disparity in the band
    for e in ds:
        for j in range(e):
            for L in range(0, 3*max(ds)//max(1,e)+3):
                lo=(N*L+1)*e; hi=(N*L+N-1)*e; q=N*j+1
                if all(lo<=d*q<=hi for d in ds): return True
    return False
def R7(ds):
    # one disparity off the lattice the rest share, rest at most three -- integer sets share Z
    return False
def any_rule(ds): return R1(ds) or R2(ds) or R3(ds) or R4(ds) or R5(ds) or R6(ds) or R7(ds)
found=[]
for ds in combinations(range(1,26),7):
    if ds[0]!=1: continue
    L=list(ds)
    if not any_rule(L):
        cert=None
        for e in L:
            for j in range(e):
                if clear_at(L,e,j): cert=(e,j); break
            if cert: break
        found.append((ds,cert))
        if len(found)>=5: break
print(f"  difference sets on which every condition of section 10 fails: {'FOUND' if found else 'none in range'}")
for ds,c in found:
    print(f"    {ds}    a certificate does exist: (e,j) = {c}")
print()
print("  R4 is vacuous at order 8 (it carries n prime); R7 is vacuous on integer sets")
print("  (it needs a disparity off the lattice the others share).")
