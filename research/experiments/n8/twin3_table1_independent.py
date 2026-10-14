"""twin3_table1_independent.py -- recompute Table 1 by pure integer enumeration
in b-coordinates (no Fractions, no interval algebra), as an independent control."""
from math import lcm
FULL=frozenset(range(8))
def bad_int(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
for rho0 in (2,4,6):
    Lb = lcm(1,3,5,7,rho0)
    runs=[]
    for b in range(Lb):
        cov=set()
        for e in (1,3,5,7,rho0): cov |= bad_int(e,(e*b)//Lb)
        U=frozenset(FULL-cov)
        if runs and runs[-1][2]==U: runs[-1][1]=b+1
        else: runs.append([b,b+1,U])
    print(f"rho0={rho0}  L_base={Lb}")
    for a,b,U in runs:
        if U: print(f"   b in [{a},{b})  x in [{a}/{Lb}, {b}/{Lb})  U={sorted(U)}")
