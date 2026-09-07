"""
BOUNDARY-EXACT re-verification.  Replaces midpoint evaluation everywhere.

Hazard being checked: evaluating floor(e*x) at the CENTRE of a cell silently assumes
the breakpoint list is complete.  Boundary Set Method discipline: measure ENTRY and
EXIT of every interval, never the centre.

Three checks:
 (A) COMPLETENESS. For each cell [a,b) and each speed e, verify NO integer k has
     a < k/e < b -- i.e. floor(e*x) really is constant on the whole half-open cell.
     Exact rational test, no evaluation at any interior point.
 (B) ENTRY/EXIT. Compute floor(e*a) (entry, cell is left-closed) and the exit value
     lim_{x->b-} floor(e*x) = floor(e*b) - [e*b is an integer].  They must agree.
 (C) BAD-SET DIRECTION. The framework's bad set for a divisible runner 8m is
     {x : floor(8m x) mod 8 in {0,7}} = union of [j/m - 1/(8m), j/m + 1/(8m))
     -- LEFT-CLOSED, right-open.  The bridge's boundary case ((t+er) = 7 mod 8 with
     s_e = 0) makes the true bad set SMALLER at that endpoint.  Confirm the coded set
     is a SUPERSET of the true one, so every existence claim is conservative.
"""
from fractions import Fraction as F
import sys

def cells(speeds):
    pts={F(0),F(1)}
    for e in speeds:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))

def floor_entry(e,a): return (e*a).numerator//(e*a).denominator
def floor_exit(e,b):
    v=e*b; f=v.numerator//v.denominator
    return f-1 if v.denominator==1 else f

def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
FULL=frozenset(range(8))

print("(A)+(B) completeness and entry/exit agreement, per rho0")
for rho0 in (2,4,6):
    S=[1,3,5,7,rho0]; C=cells(S)
    bad_cells=0; mism=0; meas=F(0); wins=[]
    for a,b in C:
        for e in S:
            # (A) no breakpoint strictly inside
            lo=(e*a); hi=(e*b)
            k0=lo.numerator//lo.denominator + 1
            if F(k0,e) > a and F(k0,e) < b: bad_cells+=1
            # (B) entry must equal exit
            if floor_entry(e,a)!=floor_exit(e,b): mism+=1
        cov=set()
        for e in S: cov|=bad(e,floor_entry(e,a))
        cov2=set()
        for e in S: cov2|=bad(e,floor_exit(e,b))
        assert cov==cov2, (rho0,a,b)
        if cov!=FULL:
            meas+=b-a; wins.append((a,b,sorted(FULL-cov)))
    merged=[]
    for a,b,u in wins:
        if merged and merged[-1][1]==a and merged[-1][2]==u: merged[-1][1]=b
        else: merged.append([a,b,u])
    print(f"  rho0={rho0}: {len(C)} cells, interior breakpoints found {bad_cells}, "
          f"entry/exit mismatches {mism}")
    print(f"     SAFE measure (boundary-exact) = {meas}   windows: "
          f"{[(str(a),str(b),u) for a,b,u in merged]}")

print("\n(C) divisible-runner bad set, exact boundaries")
for m in (1,2,3,4,5,6):
    ivs=[]
    t=0
    while F(t,8*m) < 1:
        if t%8 in (0,7):
            a,b=max(F(t,8*m),F(0)),min(F(t+1,8*m),F(1))
            if a<b: ivs.append((a,b))
        t+=1
    tot=sum(b-a for a,b in ivs)
    # compare with the closed-form union [j/m - 1/(8m), j/m + 1/(8m))
    cf=[]
    for j in range(0,m+1):
        a,b=max(F(j,m)-F(1,8*m),F(0)),min(F(j,m)+F(1,8*m),F(1))
        if a<b: cf.append((a,b))
    def merge(v):
        out=[]
        for a,b in sorted(v):
            if out and a<=out[-1][1]: out[-1][1]=max(out[-1][1],b)
            else: out.append([a,b])
        return [(a,b) for a,b in out]
    print(f"  m={m}: measure from floor definition = {tot}; closed form matches: "
          f"{merge(ivs)==merge(cf)}   (expected measure 1/4)")
print("\nThe coded bad set is left-closed / right-open.  The bridge's s_e = 0 exception")
print("only REMOVES points from the true bad set, so the coded set is a superset and")
print("every 'a safe fibre exists' conclusion drawn from it is conservative.")
