"""For each rounding error E, which moduli b does 'band implies window' FAIL at?
Not a threshold -- a finite exceptional set, as FourResidues showed for E = 1/2."""
from fractions import Fraction as F
import math
from itertools import combinations
def fails(E, bmax=5000):
    out=[]
    for b in range(2,bmax+1):
        rmin=math.ceil((b-6*E)/6); rmax=math.floor((5*b+6*E)/6)
        if not (8*rmin+1 >= b and 8*rmax+1 <= 7*b): out.append(b)
    return out
def allowed_set(mods):
    import math as M
    P=1
    for m in (2,3,8,9):
        if m in mods: P = P*m//M.gcd(P,m)
    A=[q for q in range(P) if ((2 not in mods or q%2) and (3 not in mods or q%3)
        and (8 not in mods or q%8!=7) and (9 not in mods or q%9!=8))]
    return A,P
def maxgap(A,P):
    if len(A)==1: return P
    return max((A[(i+1)%len(A)]-A[i])%P for i in range(len(A)))
print(" E      failing moduli b (band does NOT imply window)")
seen={}
for k in range(5):
    for mods in combinations((2,3,8,9),k):
        A,P=allowed_set(set(mods)); E=F(maxgap(A,P),2)
        if E in seen: continue
        f=fails(E)
        seen[E]=f
        print(f" {str(E):5s}  count {len(f):3d}:  {f[:22]}{' ...' if len(f)>22 else ''}")
print()
print("the point: each E gives a FINITE exceptional set, not a threshold.")
print("for the worst case E = 5 (all four exclusions present):")
f=seen[F(5)]
print(f"   {len(f)} failing moduli, largest {max(f)}")
print(f"   all of them: {f}")
