"""Verification of the 3-walker residue-intersection claims (owner, other session, 2026-09-18).
Position of a ratio rho at flank opening k is rho*(k + 1/8); clear iff circDist >= 1/8.
Note rho = A + f: the WHOLE PART A is part of the configuration, not just the fractional part f."""
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations, product
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def clear(rho,k): return circd(rho*(F(k)+TH))>=TH
def shadows(rhos,K=6): return not any(all(clear(r,k) for r in rhos) for k in range(K+1))

FS=[F(a,b) for b in range(2,9) for a in range(1,b) if gcd(a,b)==1]
print(f"reduced fractions a/b, b<=8: {len(FS)}   C(21,3) = {len(list(combinations(FS,3)))}")
print()
print("=== A. the four claimed triples, with rho = f  (i.e. whole part A = 0) ===")
for t in [(F(1,2),F(1,3),F(4,5)),(F(1,2),F(2,3),F(4,5)),(F(1,2),F(4,5),F(2,7)),(F(1,2),F(4,5),F(5,8))]:
    print(f"   {tuple(str(x) for x in t)}  shadows k in 0..6 ? {shadows(t)}")
print()
print("=== B. exhaustive over C(21,3) with A = 0, as the claim scopes it ===")
sh=[t for t in combinations(FS,3) if shadows(t)]
print(f"   3-subsets shadowing k in 0..6: {len(sh)}")
for t in sh: print(f"      {tuple(str(x) for x in t)}   denominators {tuple(x.denominator for x in t)}")
print(f"   all contain 1/2 ? {all(F(1,2) in t for t in sh)}")
print()
print("=== C. the SAME question with the whole part A free (rho = A + f, A in 0..7) ===")
sh2=set(); no_half=[]
for fs in combinations(FS,3):
    for As in product(range(8),repeat=3):
        rhos=tuple(F(A)+f for A,f in zip(As,fs))
        if shadows(rhos):
            sh2.add((tuple(str(x) for x in fs),As))
            if F(1,2) not in fs: no_half.append((fs,As))
print(f"   shadowing configurations with A free: {len(sh2)}")
print(f"   of those, WITHOUT any f = 1/2: {len(no_half)}")
if no_half:
    seen=set()
    for fs,As in no_half:
        key=tuple(str(x) for x in fs)
        if key not in seen:
            seen.add(key); print(f"      e.g. f={key}  A={As}")
        if len(seen)>=6: break
