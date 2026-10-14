"""Does the ISOLATION SET deform with the speed, even where its minimum jumps?
L(v) = { u in (0,U] : all readings clear }.  Exact rational arithmetic on the endpoints."""
from fractions import Fraction as F
N=8
def lonely_set(S,U):
    """exact union of maximal clear intervals of u in (0,U]; each reading s is clear when
       s*u mod 8 in [1,7], i.e. u in [(8k+1)/s,(8k+7)/s]."""
    ivs=None
    for s in S:
        blocks=[]
        k=0
        while F(8*k+1,1)/s <= U:
            a=F(8*k+1)/s; b=F(8*k+7)/s
            blocks.append((max(a,F(0)),min(b,U)))
            k+=1
        blocks=[(a,b) for a,b in blocks if b>a]
        ivs=blocks if ivs is None else [ (max(a,c),min(b,d)) for a,b in ivs for c,d in blocks if min(b,d)>max(a,c) ]
    return ivs or []
def measure(ivs): return sum(b-a for a,b in ivs)
U=F(20)
print("  deform s7 = 7 + e.   |L| = total measure of the isolation set on (0,20]")
print("   e          #intervals   |L|            first point")
for num in [0,1,2,5,10,20,40,60,80,120]:
    e=F(num,200)
    S=[F(1),F(2),F(3),F(4),F(5),F(6),F(7)+e]
    L=lonely_set(S,U)
    m=measure(L)
    first=L[0][0] if L else None
    print(f"  {str(e):9s} {len(L):10d}   {float(m):.8f}   {float(first) if first is not None else None}")
print()
print("  note e=0 is the AP: measure zero, isolated points -- the manuscript's own record.")
