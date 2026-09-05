#!/usr/bin/env python3
"""Checks F6 (strata) and F7 (mu6 class counts) -- exact integer computation."""
import sys
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import is_prime, curve_order

def scan(lo, hi):
    out=[]
    p=lo
    while p<=hi:
        if is_prime(p) and p>3:
            n=curve_order(p)
            if is_prime(n):
                out.append((p,n))
        p+=1
    return out

allp = scan(101, 7000)
forty = allp[:40]
print("smallest 40 primes p>100 with #E(F_p) prime, E: y^2=x^3+7")
print("  range: [%d, %d]"%(forty[0][0], forty[-1][0]))
print("  list:", [p for p,_ in forty])
print("  all p = 1 mod 3 :", all(p%3==1 for p,_ in forty))
sin_ = [p for p,_ in forty if p%12==7]
cos_ = [p for p,_ in forty if p%12==1]
other= [p for p,_ in forty if p%12 not in (1,7)]
print("  p=7 mod 12 (SIN, p=3 mod 4): %d  -> %s"%(len(sin_),sin_))
print("  p=1 mod 12 (COS, p=1 mod 4): %d  -> %s"%(len(cos_),cos_))
print("  other:",other)
tot=sum((n-1)//6 for _,n in forty)
tsin=sum((n-1)//6 for p,n in forty if p%4==3)
tcos=sum((n-1)//6 for p,n in forty if p%4==1)
print("  F7 totals: mu6 classes = %d   SIN = %d   COS = %d   (raw a-cells = %d)"%(tot,tsin,tcos,sum(n-1 for _,n in forty)))

above = [ (p,n) for p,n in allp if p>4513 ][:10]
print("\nsmallest 10 with #E prime above 4513:", [p for p,_ in above])
spec2 = [4549,4597,4831,5107,5197,5281,5791,5923,5953,6007]
print("  spec's replacement stratum       :", spec2)
print("  MATCH:", [p for p,_ in above]==spec2)
print("  disjoint from the 40:", set(spec2).isdisjoint({p for p,_ in forty}))
print("  # with p = 3 mod 4:", sum(1 for p in spec2 if p%4==3), [p for p in spec2 if p%4==3])
print("  n and (n-1)/6 for stratum 2:", [(p,n,(n-1)//6) for p,n in above])

# v1's claim check: smallest 10 above 2000
ab2000=[p for p,_ in allp if p>2000][:10]
print("\nv1's 'smallest 10 above 2000':",ab2000," all inside the 40:",set(ab2000)<= {p for p,_ in forty})
print("\nfull (p,n,(n-1)/6) for the 40:")
for p,n in forty: print("   p=%5d n=%5d (n-1)/6=%4d  %s"%(p,n,(n-1)//6, "SIN" if p%4==3 else "COS"))
