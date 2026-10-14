"""
n=8, Case 2, Unit-Complete, representative speeds: E_non = {1,3,5,7,rho0}.
Exact map of the SAFE set in x = b/L, using each runner's ACTUAL bad set
(not merely its parity).  Exact rational arithmetic.

Corrected framework (see reports/n8_agent_bridge.md): with k = b + rL,
   (e*k) mod 8L = L*(((t_e + e*r) mod 8)) + s_e,  t_e = floor(e*b/L),
so runner e is satisfied iff (e*r + t_e) mod 8 in {1,...,6}, i.e. iff
   r not in bad(e,t_e) = {r : e*r + t_e = 0 or 7 (mod 8)}.
The union must run over ALL of E, divisible runners included.
"""
from fractions import Fraction as F
import sys

def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
FULL=frozenset(range(8))

def cells(speeds):
    pts={F(0),F(1)}
    for e in speeds:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts)
    return list(zip(p,p[1:]))

for rho0 in (2,4,6):
    S=[1,3,5,7,rho0]
    C=cells(S)
    safe=[]; meas=F(0)
    for a,b in C:
        x=(a+b)/2
        cov=set()
        for e in S: cov|=bad(e,int(e*x))
        if cov!=FULL:
            safe.append((a,b,sorted(FULL-cov)))
            meas+=b-a
    # merge adjacent safe cells with identical uncovered set
    merged=[]
    for a,b,u in safe:
        if merged and merged[-1][1]==a and merged[-1][2]==u: merged[-1][1]=b
        else: merged.append([a,b,u])
    print(f"rho0={rho0}: E_non={S}   SAFE measure = {meas} = {float(meas):.4f} of x in [0,1)")
    print(f"   {len(merged)} maximal safe windows:")
    for a,b,u in merged:
        print(f"      x in [{a},{b})  length {b-a} = {float(b-a):.4f}   uncovered r = {u}")
    print()
