"""What is the BALANCE -- the subjects that do NOT clear at d_min -- made of?

Criterion: clear <=> every disparity has  c <= a mod 8c <= 7c,  c = d_min/g.
Failure needs some a with  a mod 8c < c  or  a mod 8c > 7c.  Note a >= c always.

Structural prediction, straight from the criterion:
  * a mod 8c > 7c  with a < 8c  needs  7c < a < 8c   -- reading in (7,8)
  * a mod 8c < c   with a >= c  needs  a >= 8c       -- reading >= 8
  BOTH require the reading a/c > 7.  So:

      S = d_max/d_min <= 7   ==>   CLEAR AT d_min, always.

which is exactly Theorem 4.8's constant.  The criterion SUBSUMES it and extends past S > 7.
Test the implication, then decompose the balance.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
rng=random.Random(4321)
tot=clear=0; S_le7=0; S_le7_clear=0
viol=0
nfail=Counter(); side=Counter(); readings=Counter(); Sband=Counter()
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[abs(v[j]-v[i])//g for j in range(8) if j!=i]
        c=min(ds); S=F(max(ds),c)
        bad=[a for a in ds if not (c <= a%(8*c) <= 7*c)]
        ok = not bad
        tot+=1; clear+=ok
        if S<=7:
            S_le7+=1; S_le7_clear+=ok
            if not ok: viol+=1
        if not ok:
            nfail[len(bad)]+=1
            for a in bad:
                r=a%(8*c)
                side['r < c  (reading >= 8)' if r<c else 'r > 7c (reading in (7,8) mod 8)']+=1
                readings[min(int(F(a,c)),12)]+=1
            Sband[min(int(S),12)]+=1
print(f"  {tot} subject-instances")
print(f"  clear at d_min                       : {clear}  ({clear/tot:.4f})")
print(f"  BALANCE (do not clear)               : {tot-clear}  ({(tot-clear)/tot:.4f})\n")
print(f"  subjects with S <= 7                 : {S_le7}  ({S_le7/tot:.4f})")
print(f"  of those, clear at d_min             : {S_le7_clear}/{S_le7}  ({S_le7_clear/S_le7:.6f})")
print(f"  VIOLATIONS of 'S <= 7 => clear'      : {viol}")
print(f"\n  balance decomposition")
print(f"    number of failing disparities      : {dict(sorted(nfail.items()))}")
print(f"    which side                         : {dict(side)}")
print(f"    reading a/c of failing disparities : {dict(sorted(readings.items()))}")
print(f"    S of failing subjects (floored)    : {dict(sorted(Sband.items()))}")
