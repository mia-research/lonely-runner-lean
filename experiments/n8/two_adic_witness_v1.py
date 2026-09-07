"""
n=8: does the 2-ADIC witness family settle the residual hard case?

Exact statement being tested.  Write v = 2^e u with u odd.  For t = a/2^k, a odd:
      ||v a / 2^k|| = ||u a / 2^(k-e)|| = c / 2^(k-e),  c odd, 1 <= c <= 2^(k-e-1)
      (and = 0 when e >= k).
So  ||v t|| >= 1/8  iff   c >= 2^(k-e-3).
  * e >= k        -> ||vt|| = 0.        FAILS.
  * k-3 <= e < k  -> c >= 1 always.     AUTOMATIC (this is where n = 8 = 2^3 pays).
  * e < k-3       -> a genuine condition on  u a  mod 2^(k-e).
Rung k = 3 is exactly the q = 8 rung of the witness ladder: every T with no speed
divisible by 8 is settled by t = 1/8.  This script asks what the higher rungs add.

Residual hard case (all four levels forced by the ladder): T contains a multiple
of 5, of 6, of 7 and of 8.  Exact arithmetic; no floating point.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def v2(x):
    e=0
    while x%2==0: x//=2; e+=1
    return e, x

def two_adic_ok(T, k, a):
    """||v a/2^k|| >= 1/8 for every v in T?  Exact, integer arithmetic only."""
    mod=1<<k
    for v in T:
        r=(v*a)%mod
        d=min(r, mod-r)           # 2^k * ||v a / 2^k||
        if d*8 < mod: return False
    return True

def settled_by_2adic(T, kmax):
    for k in range(3, kmax+1):
        for a in range(1, 1<<k, 2):
            if two_adic_ok(T,k,a): return (k,a)
    return None

def main(V, kmax):
    LV=(5,6,7,8)
    tot=0; unsettled=[]; byk={}
    for T in combinations(range(1,V+1),7):
        if not all(any(v%q==0 for v in T) for q in LV): continue
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        tot+=1
        r=settled_by_2adic(T,kmax)
        if r is None: unsettled.append(T)
        else: byk[r[0]]=byk.get(r[0],0)+1
    print(f"V={V}, kmax={kmax}: {tot} residual hard-case sets "
          f"(multiples of 5,6,7,8; gcd 1)")
    print(f"settled by rung k: {dict(sorted(byk.items()))}")
    print(f"NOT settled by any 2-adic witness a/2^k, k<={kmax}: {len(unsettled)}"
          f"  ({100*len(unsettled)/tot:.2f}%)")
    for T in unsettled[:25]: print("   ", T)
    return unsettled

if __name__=="__main__":
    main(int(sys.argv[1]) if len(sys.argv)>1 else 26,
         int(sys.argv[2]) if len(sys.argv)>2 else 10)
