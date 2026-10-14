"""P6: the k-construction at a 5-MULTIPLE flank, with the flank not necessarily the largest.

Flank e' with 5 | e', a = k*e' + 1.  For any disparity d write d = c*e' + s, 0 <= s < e'.
   d*a mod 5e' = e' * ((d*k + c) mod 5) + s
so d is clear iff  (d*k + c) mod 5 in {1,2,3}   (or = 4 with s = 0).
When d < e' we have c = 0 and this is the old condition; each d then forbids ONE k.
When d > e' the offset c is nonzero and each d can forbid TWO k (the residues 0 and 4),
so the pigeonhole is weaker -- which is why this is not automatic.

Measure: for how many residue sets does some k work at some 5-multiple flank?
"""
import math
from itertools import combinations

def k_ok(ds, ep, k, n=5):
    for d in ds:
        if d == ep: continue
        c, s = divmod(d, ep)
        r = (d*k + c) % n
        if r in (1,2,3): continue
        if r == (n-1) and s == 0: continue
        return False
    return True

def construction_works(ds, n=5):
    for ep in ds:
        if ep % n: continue
        for k in range(1, n):
            if k_ok(ds, ep, k, n): return True
    return False

def flank_works(ds, e, n=5):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in ds) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 34
tot = cw = bad = 0
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]; nf = c[:-1]
    if all(d % 5 != 0 for d in nf) or e <= 4*c[0] or e <= 15: continue
    tot += 1
    if construction_works(c):
        cw += 1
        # soundness: the claimed flank must really work
        okf = any(ep % 5 == 0 and any(k_ok(c, ep, k) for k in range(1,5)) and not flank_works(c, ep)
                  for ep in c)
        if okf: bad += 1
print(f"residue sets (outside P1'/P2/P3) in [1,{hi}]: {tot}")
print(f"   P6: some k works at some 5-multiple flank : {cw}  ({100*cw/tot:.2f}%)")
print(f"   soundness violations                      : {bad}")
