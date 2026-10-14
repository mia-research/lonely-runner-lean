"""Owner: the guards relate to the patterns of the AP's global isolation.

CLAIM to check: the protected points are R = 8k + p for p a unit mod 8, guarded by the reading = p.
The AP's global isolation occurs at the phi(8) = 4 grid instants p/8, where the binding pair is at
offset +-p (v11 Corollary 4.15).  Same index p.  So the runner that BINDS at instant p is the same
reading that GUARDS the protected points congruent to p.

And the AP's isolation has "two patterns and two inversions": p = 1,3 give two patterns, p = 7,5
their inversions, because 7 = -1 and 5 = -3 mod 8.  The protected points should pair the same way.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
def frac(x): return x-floor(x)
v=speeds((1,2,3,4,5,6,7,8))
print("  AP speeds", list(v), "-- subject 1, readings = disparities / d_min = 1..7\n")
print(f"  {'instant p':>10} {'binding pair (offsets)':>24} {'inverse of':>12}")
for p in (1,3,5,7):
    t=F(p,8)
    rel=[(frac(F(v[j]-v[0])*t), j) for j in range(1,8)]
    a=min(rel)[1]; b=max(rel)[1]
    offs=((v[a]-v[0])%8, (v[b]-v[0])%8)
    inv=[q for q in (1,3,5,7) if (p*q)%8==1][0]
    print(f"  {p:>10} {str(offs):>24} {f'p={inv}':>12}")
print()
print(f"  {'protected R':>12} {'R mod 8':>9} {'guard reading':>15} {'= binding runner at instant p?':>32}")
for R in (1,3,5,7,9,11,13,15):
    p=R%8
    guard=[s for s in range(1,8) if (s*R)%8==1]
    g=guard[0] if guard else None
    t=F(p,8)
    rel=[(frac(F(v[j]-v[0])*t), j) for j in range(1,8)]
    binder=(v[min(rel)[1]]-v[0])%8
    print(f"  {R:>12} {p:>9} {str(g):>15} {str(g==binder):>32}")
print()
print("  pairing: 1<->7 and 3<->5 are inverse under multiplication mod 8 (Klein),")
print("  so the four instants are two patterns and two inversions, and the eight protected")
print("  points pair the same way: {1,9}&{7,15} and {3,11}&{5,13}.")
print()
print("  and the NON-units 2,4,6 -- the cage's barred offsets -- guard nothing:")
for s in (2,4,6):
    hits=[R for R in (1,3,5,7,9,11,13,15) if (s*R)%8==1]
    print(f"    reading {s}: guards {hits if hits else 'nothing'}")
