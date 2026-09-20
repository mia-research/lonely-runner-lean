"""WHY the one open step is open, and whether it is a real obstruction.
At modulus b the band (margin 1/6) is  b-3 <= 6r <= 5b+3 ; the window is  b <= 8r+1 <= 7b.
Where does the band admit a BLOCKED residue?"""
from fractions import Fraction as F
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def band(b): return [r for r in range(b) if b-3 <= 6*r <= 5*b+3]
def window(b): return [r for r in range(b) if L(b) <= r <= U(b)]
print("b :  band residues            window residues        band-only (BLOCKED, admitted anyway)")
for b in range(2,20):
    bd,wd=band(b),window(b)
    bad=[r for r in bd if r not in wd]
    print(f"{b:2d}: {str(bd):22s} {str(wd):22s} {bad if bad else '-'}")
print()
print("so the band fails to imply the window exactly at b <= 9, and the surplus is the")
print("blocked residue 0 (and b-1 at b = 8,9) -- precisely the reduced obligation.")
print()
print("margin needed to FORCE the rounded parity at b = 2:")
print("   rounding q = round(t) is odd  <=>  dist(t, 2Z) > 1/2  <=>  dist(t/2, Z) > 1/4")
for n,a in ((3,F(1,3)),(4,F(1,4)),(5,F(1,5)),(6,F(1,6)),(7,F(1,7)),(8,F(1,8))):
    print(f"   order {n}: margin {a} -> {'SUFFICES' if a > F(1,4) else 'does NOT suffice'}")
print("   order 6 is what 5 blockers licenses, and 1/6 < 1/4.")
print("   => the nearest-integer rounding CANNOT force the parity from a margin bound alone.")
