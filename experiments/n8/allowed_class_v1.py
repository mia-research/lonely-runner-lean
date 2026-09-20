"""Is the u-reformulation required? No -- the real requirement is: round t to the nearest integer
in an ALLOWED residue class, and pay a larger rounding error.
Allowed = q != 0 mod 2, q != 0 mod 3, q != 7 mod 8, q != 8 mod 9 (for the moduli present).
Compute the allowed set, its largest gap, and the resulting band->window threshold."""
from fractions import Fraction as F
from itertools import combinations
def allowed_set(mods):
    P=1
    for m in (2,3,8,9):
        if m in mods: P = P*m//__import__('math').gcd(P,m)
    A=[q for q in range(P) if ((2 not in mods or q%2) and (3 not in mods or q%3)
        and (8 not in mods or q%8!=7) and (9 not in mods or q%9!=8))]
    return A,P
def maxgap(A,P):
    if not A: return None
    if len(A)==1: return P          # a single admissible residue: the cyclic gap is P
    return max((A[(i+1)%len(A)]-A[i])%P for i in range(len(A)))
print("subset of {2,3,8,9} present -> allowed residues, largest gap, rounding error E = gap/2")
rows=[]
for k in range(5):
    for mods in combinations((2,3,8,9),k):
        A,P=allowed_set(set(mods))
        g=maxgap(A,P)
        if g is None: continue
        rows.append((mods,len(A),P,g))
        print(f"   {str(mods):16s} allowed {len(A):3d}/{P:3d}  max gap {g}  E = {F(g,2)}")
print()
print("band->window threshold as a function of the rounding error E:")
print("   with |q - t| <= E the band is  b - 6E <= 6r <= 5b + 6E  (from dist(t/b,Z) >= 1/6)")
print("   and integrality is kept, so the threshold is the least b with both ends holding.")
def thresh(E):
    # E a Fraction; band: 6r >= b - 6E, 6r <= 5b + 6E ; window: b <= 8r+1 <= 7b
    for b in range(2,4001):
        lo=-((-(b-6*E)).__ceil__()) if False else None
        import math
        rmin=math.ceil(float(b-6*E)/6); rmax=math.floor(float(5*b+6*E)/6)
        if 8*rmin+1 >= b and 8*rmax+1 <= 7*b: return b
    return None
for mods,n,P,g in rows:
    E=F(g,2)
    print(f"   {str(mods):16s} E = {E}  ->  band implies window from b >= {thresh(E)}")
