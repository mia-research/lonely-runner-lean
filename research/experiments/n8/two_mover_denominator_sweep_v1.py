from math import gcd
from fractions import Fraction as F
import collections
def clear(p,q,A): return q <= (p*A) % (8*q) <= 7*q
def lcm(a,b): return a*b//gcd(a,b)
def minclear(u1,u2):
    p1,q1=u1.numerator,u1.denominator; p2,q2=u2.numerator,u2.denominator
    P=lcm(q1,q2)
    for k in range(P):
        A=8*k+1
        if clear(p1,q1,A) and clear(p2,q2,A): return k
    return None

print("1) FULL characterisation of two-mover failures (no early stop)")
bad=collections.Counter(); badex=[]
QM=30
for q1 in range(2,QM):
  for q2 in range(q1,QM):
    for p1 in range(1,8*q1):
      if gcd(p1,q1)!=1: continue
      for p2 in range(1,8*q2):
        if gcd(p2,q2)!=1: continue
        u1,u2=F(p1,q1),F(p2,q2)
        if u2<u1: continue
        if minclear(u1,u2) is None:
            bad[(q1,q2)]+=1
            if len(badex)<12: badex.append((u1,u2))
print(f"   failing (q1,q2) denominator pairs: {dict(bad)}")
print(f"   examples: {[(str(a),str(b)) for a,b in badex]}")

print("\n2) the q=2 failures, exactly")
print("   u = p/2 is BLOCKED iff p*A = +/-1 (mod 16).  A = 8k+1 is 1 or 9 (mod 16).")
b1=[p for p in range(1,17,2) if (p)%16 in (1,15)]
b9=[p for p in range(1,17,2) if (9*p)%16 in (1,15)]
print(f"   blocked when A=1  (mod 16): p = {b1} (mod 16)")
print(f"   blocked when A=9  (mod 16): p = {b9} (mod 16)")
print("   -> a pair fails iff one is blocked at A=1 and the other at A=9.")

print("\n3) MINIMAL clearing k over all NON-failing pairs -- can k be named by a bound?")
hist=collections.Counter(); worst=None
for q1 in range(2,26):
  for q2 in range(q1,26):
    for p1 in range(1,8*q1):
      if gcd(p1,q1)!=1: continue
      for p2 in range(1,8*q2):
        if gcd(p2,q2)!=1: continue
        u1,u2=F(p1,q1),F(p2,q2)
        if u2<u1: continue
        k=minclear(u1,u2)
        if k is None: continue
        hist[k]+=1
        if worst is None or k>worst[0]: worst=(k,u1,u2)
tot=sum(hist.values())
run=0
print(f"   {'k':>3} {'count':>9} {'cumulative %':>13}")
for k in sorted(hist):
    run+=hist[k]
    if k<=8 or run==tot: print(f"   {k:>3} {hist[k]:>9} {100*run/tot:>12.4f}%")
print(f"   largest minimal k anywhere in range: {worst[0]} at u1={worst[1]}, u2={worst[2]}")
