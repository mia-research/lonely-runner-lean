"""WHY does the counterexample exist?
A mover p/8 blocks k iff t = pk mod 8 is in {0,7}, i.e. k = 0 or 7*p^{-1} mod 8.
The units mod 8 are SELF-INVERSE (klein_self_inverse), so p^{-1} = p and the blocked odd residue
is 7p mod 8.  For p = 1,3,5,7 that gives 7,5,3,1 -- ALL FOUR odd residues.
Halves cover the evens.  Prediction: shadowing at q <= 8 REQUIRES all four eighths."""
from math import gcd
from itertools import combinations_with_replacement
from math import lcm

def blocks(p, A, q):
    M = 8*q; r = (p*A) % M
    return min(r, M-r) < q
def blocked_res(p, q):
    return sorted({k % q for k in range(4*q) if blocks(p, 8*k+1, q)})

print("1. blocked k-residues mod 8 for the eighths:")
for p in (1,3,5,7):
    inv = next(x for x in range(1,8,2) if (p*x) % 8 == 1)
    print(f"   p/8 = {p}/8   p^-1 = {inv} (self-inverse: {inv==p})   7*p^-1 mod 8 = {(7*inv)%8}"
          f"   blocked: {blocked_res(p,8)}")
print(f"   union of the four: {sorted(set().union(*[set(blocked_res(p,8)) for p in (1,3,5,7)]))}")
print(f"   halves block: {blocked_res(1,2)} mod 2  -> evens {{0,2,4,6}} mod 8")
print(f"   => evens from the halves + odds from the four eighths = all of Z/8\n")

print("2. do all 21 shadowing multisets at q <= 8 contain all four eighths?")
pool=[(p,q) for q in range(2,9) for p in range(1,q) if gcd(p,q)==1]
def shadowed(m):
    L=lcm(*[q for _,q in m]); return all(any(blocks(p,8*k+1,q) for p,q in m) for k in range(L))
sh=[m for m in combinations_with_replacement(pool,6) if shadowed(m)]
print(f"   shadowing multisets: {len(sh)}")
allfour = sum(1 for m in sh if all((p,8) in m for p in (1,3,5,7)))
print(f"   containing all four eighths (1/8,3/8,5/8,7/8): {allfour} of {len(sh)}")
for m in sh[:4]: print(f"      {m}")
missing = [m for m in sh if not all((p,8) in m for p in (1,3,5,7))]
if missing:
    print(f"   NOT containing all four: {len(missing)}")
    for m in missing[:4]: print(f"      {m}  blocked-union check")
