"""Prime, or odds and evens?  Neither.  It is the totient.

The criterion's real hypothesis is gcd(e,n)=1 -- the flank NON-RESONANT -- not n prime and not n
odd.  At prime n the two coincide (n does not divide e iff gcd(e,n)=1), which is why primality
looked load-bearing.  My own earlier measurement could not separate them: 5 and 7 are BOTH prime
and odd, 6 is BOTH composite and even.  Order 9 is the case that separates, and 10 confirms.
"""
import math
from itertools import combinations
def totient(n): return sum(1 for k in range(1,n+1) if math.gcd(k,n)==1)
def flankWorks(ds,e,n):
    M=n*e
    for j in range(e):
        if all(e <= (d*(n*j+1))%M <= (n-1)*e for d in ds): return True
    return False
print(f"{'n':>3} {'parity':>6} {'primality':>12} {'phi(n)/n':>9} {'usable flanks':>14}"
      f" {'criterion fires':>16}")
for n in (5,6,7,8,9,10,11,12,15,16):
    k=n-1; HI = 14 if n<=8 else (11 if n<=11 else 10)
    tot=0; fires=0
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1
        hit=False
        for i in range(k):                        # any flank, as lonely_iff_exists_flank permits
            e=c[i]; L=[c[j] for j in range(k) if j!=i]
            if math.gcd(e,n)==1 and all(d%n for d in L): hit=True; break
        if hit: fires+=1
    par = "odd" if n%2 else "even"
    isp = all(n%r for r in range(2,n))
    pp  = any(n==p**j for p in (2,3,5,7,11,13) for j in (1,2,3,4))
    prim = "prime" if isp else ("prime power" if pp else "composite")
    print(f"{n:>3} {par:>6} {prim:>12} {totient(n)}/{n}"
          f"{'':>{max(0,6-len(str(totient(n))+str(n)))}} {totient(n)/n:>14.3f} "
          f"{fires:>7}/{tot:<8}")
