"""Do the order-5 RULES transfer to 6 and 7?  Counts, not shares.

Obligation form transfers for free: doors_agree is general n (checked in Lean).  A subject at
order n has n-1 disparities, so n-2 blockers at a flank.  What is already free:
exists_lonely_of_card_le_four needs n >= 6, so at BOTH 6 and 7 every subject with card <= 4 is
settled unconditionally.  The open part is card = n-1 exactly (5 at n=6; 5 and 6 at n=7).
"""
from fractions import Fraction as F
from itertools import combinations
import math
def flankWorks(ds, e, n):
    M = n*e
    for j in range(e):
        if all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in ds): return True
    return False
def anyflank(ds, n):  return any(flankWorks(ds, e, n) for e in ds)
def R_prime(ds, n):                      # P1' -- needs n PRIME (Euclid's lemma)
    if not all(n % p for p in range(2, n)): return False
    return all(d % n for d in ds[:-1])
def R_ratio(ds, n):  return ds[-1] <= (n-1)*ds[0]
def R_self(ds, n):   return all(d % n == 0 for d in ds[:-1])
def R_rat(ds, n, Q=25):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            if all(F(1,n) <= min(F((d*a)%q,q), 1-F((d*a)%q,q)) for d in ds): return True
    return False
for n, HI in ((5,26),(6,20),(7,15)):
    k = n-1
    tot=0; maxflank=0; anyf=0; prime=0; ratio=0; self_=0; rat=0; union=0; left=[]
    for c in combinations(range(1,HI+1), k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1
        if flankWorks(c, c[-1], n): maxflank+=1
        if anyflank(c, n): anyf+=1
        p,r,s,t = R_prime(c,n), R_ratio(c,n), R_self(c,n), R_rat(c,n)
        prime+=p; ratio+=r; self_+=s; rat+=t
        if p or r or s or t: union+=1
        else: left.append(c)
    print(f"n={n}  ({k} disparities, {n-2} blockers)   primitive {k}-sets in [1,{HI}]: {tot}")
    print(f"   LARGEST flank works                 : {maxflank}   ({'ALL' if maxflank==tot else 'NOT all'})")
    print(f"   SOME flank works (the obligation)   : {anyf}   ({'ALL' if anyf==tot else 'NOT all'})")
    print(f"   rule P1' (prime, no mult of n)      : {prime}"
          f"   {'[n composite -- rule does not apply]' if any(n%p==0 for p in range(2,n)) else ''}")
    print(f"   rule P2  (d_max <= (n-1) d_min)     : {ratio}")
    print(f"   rule P5  (all non-flank mult of n)  : {self_}")
    print(f"   rule RAT (rational a/q, q <= 25)    : {rat}")
    print(f"   UNION                               : {union}    LEFT {len(left)}  {left[:4]}")
    print()
