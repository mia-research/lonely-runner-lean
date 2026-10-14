"""
Two settlements, both by construction rather than by more search.

(A) D(T) IS UNBOUNDED -- the "finite residue check" route is dead, and for a reason
    that is one line.  If q | v for some v in T then ||v * a/q|| = 0 for every a, so
    level q is dead outright.  Taking v = lcm(2..Q) kills every level q <= Q at once,
    so D(T) > Q.  Since lcm(2..Q) ~ e^Q, this only forces D to grow like log(max T) --
    which matches the exhaustive max D (23 at V=20, 28 at V=28).

(B) LARGE-SPEED LEMMA [PROVED from LRC(7)].  If some v in T has
        v >= 28 * max(T \\ {v}),
    then M(T) >= 1/8.
    Proof.  LRC(7) on the other six gives t0 with ||v_i t0|| >= 1/7.  On
    J = [t0 - d, t0 + d], d = (1/7 - 1/8)/m = 1/(56 m), m = max(T\\{v}), all six stay
    >= 1/8, and |J| = 1/(28 m) >= 1/v is a full period of v.  Every period of v
    contains a sub-interval of length 3/(4v) on which ||v t|| >= 1/8, so J holds a
    point good for all seven.  []
    This is exactly the regime that (A) exploits, so the two are complementary.
"""
from math import gcd, lcm
from fractions import Fraction as F
import sys

def D(T,qmax):
    for q in range(2,qmax+1):
        for a in range(1,q):
            if gcd(a,q)!=1: continue
            if all(8*min((v*a)%q, q-(v*a)%q) >= q for v in T): return q
    return None

print("(A) D unbounded by construction: a single speed lcm(2..Q) kills every level <= Q")
print(f"{'Q':>3} {'lcm(2..Q)':>12} {'T':>50} {'D(T)':>6}  {'D > Q?':>7}")
for Q in (8,10,12,14,16,18):
    L=lcm(*range(2,Q+1))
    T=tuple(sorted([L, L+1, L+2, L+3, L+5, L+7, L+11]))
    g=0
    for v in T: g=gcd(g,v)
    d=D(T,120)
    print(f"{Q:>3} {L:>12} {str((T[0],'...',T[-1])):>50} {str(d):>6}  {str(d is not None and d>Q):>7}"
          f"   gcd={g}")

print("\n(B) large-speed lemma: v >= 28*max(rest) => M(T) >= 1/8, checked on instances")
def M_lower(T):
    """witness search over q <= 4000, returns a q that certifies M >= 1/8 or None"""
    return D(T,4000)
m=13
for factor in (28,40,100):
    T=tuple(sorted([1,4,5,6,7,11,factor*m]))
    d=D(T,4000)
    print(f"   rest max = {max(T[:-1])}, big speed = {T[-1]} = {factor}x13 : "
          f"witness denominator {d} -> M >= 1/8 certified" if d else "   *** no witness found")
