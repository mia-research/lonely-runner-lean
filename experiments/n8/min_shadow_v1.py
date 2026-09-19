"""Minimum number of movers that can shadow a flank, split by regime.
At a general flank any ratio is allowed; at the LARGEST flank |rho| <= 1.
A mover is its residue d mod 8e; enumerate by (p,q) with rho = p/q and d = e*p/q."""
from math import gcd, lcm
from itertools import combinations_with_replacement
def blocked(a,q):
    """k-classes mod q blocked by rho = a/q (a any integer, lowest terms)"""
    e=q; M=8*e
    return frozenset(k for k in range(q) if (lambda r: min(r,M-r)<e)((a*(8*k+1))%M))
def shadows(ms):
    L=lcm(*[q for _,q in ms])
    cov=set()
    for a,q in ms:
        b=blocked(a,q)
        cov|={k for k in range(L) if k%q in b}
    return len(cov)==L
QMAX=8
gen=[(a,q) for q in range(1,QMAX+1) for a in range(0,8*q) if gcd(a,q)==1]
gen=[(a,q) for a,q in gen if not (q==1 and a%8==0)]          # drop the dead mover
lar=[(a,q) for a,q in gen if a<=q or a>=8*q-q]               # |rho| <= 1  (rho mod 8 in [0,1]u[7,8])
for name,pool in (("general flank",gen),("largest flank (|rho|<=1)",lar)):
    found=None
    for size in range(1,8):
        for ms in combinations_with_replacement(pool,size):
            if shadows(ms): found=(size,ms); break
        if found: break
    print(f"{name:26s}: pool {len(pool):4d}, minimum shadowing size = {found[0]}  e.g. {found[1]}")
