"""Task 2 detail: exact bad sets on [3/5,5/7), and Task 4: integer existence in [3L/5, 5L/7)."""
from fractions import Fraction as F
n=8
def Sol(e,j,n): return frozenset(r for r in range(n) if (e*r-j)%n==0)
def bad(e,t,n): return Sol(e,(-t)%n,n)|Sol(e,(-(t+1))%n,n)

print("=== exact endpoint arithmetic on [3/5, 5/7) ===")
for e in (1,3,5,7):
    a,b = e*F(3,5), e*F(5,7)
    print(f" e={e}: e*3/5 = {a}, e*5/7 = {b}   -> floor at left = {a.numerator//a.denominator},"
          f"  sup of floor just below right = {b.numerator//b.denominator - (1 if b.denominator==1 else 0)}")
print("  t_5: 5*(3/5)=3 exactly and 5*(5/7)=25/7 < 4  (25/7 vs 28/7)  => t_5 = 3 throughout   OK")
print("  t_7: 7*(3/5)=21/5 >= 4 (21/5 vs 20/5) and 7*(5/7)=5 EXCLUDED => t_7 = 4 throughout   OK")
print("  t_3: 3*(3/5)=9/5 in [1,2), 3*(5/7)=15/7 in [2,3) => t_3 in {1,2}, splits at x=2/3  OK")
print()
for (e,t) in [(1,0),(3,1),(3,2),(5,3),(7,4)]:
    print(f"  bad({e},{t},8) = {sorted(bad(e,t,8))}")
U1 = bad(1,0,8)|bad(3,1,8)|bad(5,3,8)|bad(7,4,8)
U2 = bad(1,0,8)|bad(3,2,8)|bad(5,3,8)|bad(7,4,8)
print(f"  union (t3=1) = {sorted(U1)}  uncovered {sorted(set(range(8))-U1)}")
print(f"  union (t3=2) = {sorted(U2)}  uncovered {sorted(set(range(8))-U2)}")

print("\n=== Task 4: integer in [3L/5, 5L/7) ===")
print(" window length = 5L/7 - 3L/5 = (25L-21L)/35 = 4L/35")
print(" a half-open [a,a+len) contains an integer whenever len >= 1, i.e. L >= 35/4 = 8.75, i.e. L >= 9.")
print(" hypotheses give 8|L and L>16 => L >= 24 => len >= 96/35 = 2.742...")
worst=None
for L in range(24, 24*4000, 8):
    a, b = F(3*L,5), F(5*L,7)
    cnt = sum(1 for x in range(-(-a.numerator//a.denominator), b.numerator//b.denominator + (0 if b.denominator==1 else 1)) if a<=x<b)
    if worst is None or cnt < worst[1]: worst=(L,cnt)
    if cnt==0: print("  *** NO INTEGER at L =",L); break
else:
    print(f" checked every L = 24,32,...,{L}: minimum integer count in the window = {worst[1]} (attained first at L={worst[0]})")
L=24; a,b=F(3*24,5),F(5*24,7)
print(f" smallest admissible L=24: window = [{a}, {b}) = [14.4, 17.142857...) -> integers 15,16,17  (3 of them)")
print(" exact worst case: L=24 gives length 96/35=2.742..., the minimum over all admissible L; count never drops below 2.")
