import sympy as sp
from sympy import symbols, Poly
from sympy.abc import T
Q5 = T**5+155*T**4+6138*T**3+92070*T**2+555861*T+1060975
try:
    from sympy.polys.numberfields.galoisgroups import galois_group
    G,alt = galois_group(Poly(Q5,T))
    print("Galois group:", G, " (order via len? )")
    print("name:", getattr(G,'name',G))
except Exception as e:
    print("galois_group err:", e)
# Chebotarev cycle-type census: factor Q5 mod many primes, collect degree-partitions
from sympy import factor_list, GF
import sympy
census={}
for ell in sympy.primerange(2,400):
    if ell in (5,):  # skip ramified-ish; check disc
        pass
    try:
        fl = Poly(Q5, T, modulus=ell).factor_list()
    except Exception:
        continue
    degs = tuple(sorted(f.degree() for f,m in fl[1] for _ in range(m)))
    # skip if repeated factors (ramified)
    reps = any(m>1 for f,m in fl[1])
    if reps: 
        continue
    census[degs]=census.get(degs,0)+1
print("\ncycle-type census (partition -> count) over primes<400:")
for k in sorted(census): print("  ",k, census[k])
print("\nInterpretation: C5 shows only (1,1,1,1,1) and (5).")
print("D5 would add (1,2,2); A5 would add (1,1,3) and (1,2,2).")
