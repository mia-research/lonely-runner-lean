r"""
ok_fourier_v3 -- how much cancellation is there?  SIGNED vs ABSOLUTE support-2 families.

The support-2 family for a pair sums in CLOSED FORM.  With fhat(k) = -sin(pi k/4)/(pi k),

  sum_{m != 0} fhat(mb) fhat(ma)
     = (2/(pi^2 ab)) sum_{m>=1} sin(pi m b/4) sin(pi m a/4) / m^2
     = (1/(pi^2 ab)) sum_{m>=1} [ cos(pi m (b-a)/4) - cos(pi m (b+a)/4) ] / m^2 ,

and sum_{m>=1} cos(m x)/m^2 = pi^2/6 - pi x/2 + x^2/4 on [0, 2pi] (Clausen / Bernoulli B_2),
so each family is an explicit RATIONAL multiple of 1/(ab) -- no numerics needed in principle.
This is the same phenomenon as Ray(p) being rational in the O_RESONANCE work.

Question measured here: how big is |signed| against absolute?  That ratio is exactly the
cancellation the absolute bound throws away.
"""
from itertools import combinations
from functools import reduce
from math import gcd, sin, cos, pi

def fhat(k):
    if k==0: return 0.75
    if k%4==0: return 0.0
    return -sin(pi*k/4)/(pi*k)

def clausen2(x):
    """sum_{m>=1} cos(m x)/m^2  for x in [0, 2pi]"""
    x = x % (2*pi)
    return pi*pi/6 - pi*x/2 + x*x/4

def pair_signed_closed(a,b):
    """closed form of sum_{m != 0} fhat(mb) fhat(ma)"""
    return (clausen2(pi*(b-a)/4) - clausen2(pi*(b+a)/4)) / (pi*pi*a*b)

def pair_signed_num(a,b,M=20000):
    return 2*sum(fhat(m*b)*fhat(m*a) for m in range(1,M+1))
def pair_abs_num(a,b,M=20000):
    return 2*sum(abs(fhat(m*b)*fhat(m*a)) for m in range(1,M+1))

print("closed form vs direct summation, on the pairs (a,b) that actually occur:")
print(f"  {'(a,b)':10} {'closed':>12} {'numeric':>12} {'agree?':>8} {'absolute':>12} {'|signed|/abs':>13}")
for (a,b) in [(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(3,4),(3,5),(2,7),(5,7)]:
    c=pair_signed_closed(a,b); n=pair_signed_num(a,b); ab=pair_abs_num(a,b)
    print(f"  {str((a,b)):10} {c:12.8f} {n:12.8f} {str(abs(c-n)<2e-6):>8} {ab:12.8f} "
          f"{(abs(c)/ab if ab else 0):13.4f}")

print("\nper-tuple: signed support-2 total vs absolute support-2 total")
tests=[(2,6,7,8,10,13,14),(1,3,4,5,7,11,24),(1,3,5,7,13,15,24),
       (2,12,13,14,16,19,20),(3,10,14,15,16,19,21)]
print(f"{'E':28} {'signed T2':>12} {'absolute T2':>12} {'ratio':>8}")
for E in tests:
    s=0.0; t=0.0
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
        s+=pair_signed_closed(a,b)*(0.75**5)
        t+=pair_abs_num(a,b,4000)*(0.75**5)
    print(f"{str(E):28} {s:12.6f} {t:12.6f} {abs(s)/t:8.3f}")
