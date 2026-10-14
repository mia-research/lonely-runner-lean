"""I claimed the rho-construction is "a search, not a rule".  Test that.

Setup: flank e coprime to n, exactly one disparity m = n*m' divisible by n, gcd(m',e)=1.
a is fixed by CRT from rho = a mod e (and a = 1 mod n).  The multiple's reading is
n*(m'*rho mod e), so rho = m'^{-1} * v mod e places it at n*v.

If v has to be searched, no single formula for v works everywhere.  Candidates tested, each a
CLOSED FORM with no search in it.
"""
from itertools import combinations
import math
def readings_ok(ds, e, a, n):
    M = n*e
    return all(e <= (d*a) % M <= (n-1)*e for d in ds)
def a_from_rho(rho, e, n):
    einv = pow(e, -1, n); w = ((1-rho)*einv) % n
    return rho + e*w
def cands(ds, e, n):
    """closed-form choices of v, no search"""
    m = [d for d in ds if d % n == 0]
    if len(m) != 1: return None
    m = m[0]; mp = m // n
    if math.gcd(mp, e) != 1 or math.gcd(e, n) != 1: return None
    minv = pow(mp, -1, e)
    out = {}
    out["v = e//2"]        = (minv * (e//2)) % e
    out["v = (e+1)//2"]    = (minv * ((e+1)//2)) % e
    out["rho = e//2"]      = e//2
    out["rho = m'^-1"]     = minv
    out["v = e//2 (ceil)"] = (minv * -(-e//2)) % e
    return out
for n, HI in ((5,40), (6,30), (7,24)):
    k = n-1
    tot = 0; hit = {}; anyv = 0
    for c in combinations(range(1,HI+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g,x)
        if g != 1: continue
        e = c[-1]
        cd = cands(c, e, n)
        if cd is None: continue
        tot += 1
        # does SOME v work at all (the search version)?
        m = [d for d in c if d % n == 0][0]; mp = m//n; minv = pow(mp,-1,e)
        if any(readings_ok(c, e, a_from_rho((minv*v) % e, e, n), n) for v in range(1, e)):
            anyv += 1
        for name, rho in cd.items():
            a = a_from_rho(rho, e, n)
            hit[name] = hit.get(name,0) + (1 if readings_ok(c, e, a, n) else 0)
    print(f"n={n}  [1,{HI}]  applicable sets (largest flank coprime to n, exactly one multiple): {tot}")
    print(f"   SOME v works (the search)            : {anyv}")
    for name in hit:
        print(f"   closed form  {name:<18}: {hit[name]}")
    print()
