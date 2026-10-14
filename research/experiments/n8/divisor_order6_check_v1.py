"""Check the PROVED statement clear_of_order6 against the definition, and confirm 15 is tight."""
from fractions import Fraction as F
import random
def blocks(si,A,sk):
    M=8*sk; r=(si*A)%M; return min(r,M-r)<sk
random.seed(3)
bad=0; n=0
for _ in range(400000):
    b=random.randint(15,400); m=random.randint(-50,50)
    # t anywhere in the 1/6-clear band around b*m
    t=F(b)*m + F(b,6) + F(random.randint(0,10**6),10**6)*(F(5*b,6)-F(b,6))
    q=round(t)                                  # nearest integer
    if abs(F(q)-t)>F(1,2): continue
    n+=1
    if blocks(1,8*q+1,b): bad+=1
print(f"b >= 15, rounded order-6 witness clears: {n-bad}/{n} "
      f"{'(ALL, as proved)' if bad==0 else f'FAILS {bad}'}")
print("\ntightness: search b = 9..20 for a t in the 1/6 band whose rounding is BLOCKED")
for b in range(9,21):
    found=None
    for num in range(0,20001):
        t=F(b)*0 + F(b,6) + F(num,20000)*(F(5*b,6)-F(b,6))
        q=round(t)
        if blocks(1,8*q+1,b): found=(t,q); break
    print(f"   b={b:2d}: {'blocked example t=%s q=%d' % (found[0],found[1]) if found else 'no blocked rounding found'}")
