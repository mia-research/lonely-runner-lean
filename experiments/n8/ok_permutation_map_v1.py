#!/usr/bin/env python3
"""MAP THE PERMUTATIONS between grid points, for INDIVIDUAL isolation.

At t = a/m the sites are permuted by multiplication by a in (Z/m)*. Runner i is lonely iff
that permutation carries its difference set D into the band [ceil(m/8), m - ceil(m/8)].
Define A(D,m) = { a in (Z/m)* : all d*a mod m in band }.  |A| is how many of the phi(m)
permutations work.
"""
from math import gcd
from fractions import Fraction as F

def band_ok(d,a,m): 
    r=(d*a)%m
    return min(r,m-r)*8>=m
def A(D,m): return [a for a in range(1,m) if gcd(a,m)==1 and all(band_ok(d,a,m) for d in D)]

CASES=[("E* runner 0",(2,6,7,8,10,13,14)),
       ("the K=2 set",(1,5,6,7,8,11,13)),
       ("T1 runner 0 (tight)",(1,2,3,4,5,6,7)),
       ("an easy runner",(1,2,3,5,7,9,11))]
for lab,D in CASES:
    print(f"{lab}:  D = {D}")
    rows=[]
    for m in range(2,41):
        a=A(D,m)
        if a: rows.append((m,len(a),a,len([x for x in range(1,m) if gcd(x,m)==1])))
    if not rows:
        print("   no modulus <= 40 works"); print(); continue
    print(f"   {'m':>4} {'phi(m)':>7} {'|A|':>5} {'|A|/phi':>8}   working a")
    for m,k,a,ph in rows[:7]:
        print(f"   {m:>4} {ph:>7} {k:>5} {k/ph:>8.3f}   {a[:8]}")
    m0=rows[0][0]
    print(f"   smallest working modulus: {m0}")
    print()

print("SYMMETRY CHECK: is A always closed under a -> -a (i.e. m-a)?")
import random; random.seed(5); bad=0; n=0
for _ in range(3000):
    D=tuple(sorted(random.sample(range(1,40),7))); m=random.randint(9,40)
    a=A(D,m)
    if not a: continue
    n+=1
    if sorted(a)!=sorted((m-x)%m for x in a): bad+=1
print(f"   {n} nonempty A's: not closed under negation in {bad}   "
      f"{'PASS -- the action factors through (Z/m)*/{+-1}' if bad==0 else '*** FAIL ***'}")
print()
print("COUNT vs the independence heuristic  |A| ~ phi(m) * rho(m)^|D|,  rho(m)=(m-2ceil(m/8)+1)/m")
import statistics
for m in (9,11,13,15,16,17,24,31):
    rho=(m-2*((m+7)//8)+1)/m; ph=len([x for x in range(1,m) if gcd(x,m)==1])
    obs=[]
    for _ in range(2000):
        D=tuple(sorted(random.sample(range(1,60),7)))
        obs.append(len(A(D,m)))
    print(f"   m={m:>3} phi={ph:>3} rho={rho:.3f}  predicted {ph*rho**7:>6.2f}   observed mean {statistics.mean(obs):>6.2f}")
