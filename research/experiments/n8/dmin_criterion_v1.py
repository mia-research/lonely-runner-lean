"""Audit item: I reported "63.8% / 66.7% clear at scale d_min with zero cascade moves" repeatedly
and never gave a criterion -- and I refuted the parallel session's theorem for exactly this case
without supplying the right one.  Derive it.

At scale D = d_min the reading of disparity d is s = d/d_min.  In reduced units d = a.g and
d_min = c0.g, so s = a/c0, and

    BAD  <=>  |a/c0 - 8M| < 1  for some M
         <=>  |a - 8M.c0| < c0
         <=>  a mod 8c0  <  c0   or   a mod 8c0  >  7c0

so, with the threshold counting as clear:

    CLEAR AT d_min  <=>  for every disparity a:  c0 <= (a mod 8c0) <= 7c0

Note a = c0 itself gives c0 mod 8c0 = c0, on the boundary, clear -- consistent.
This is the correct k=0 statement; theirs was "unique residue", which is the criterion at scale g,
not at scale d_min.  Verify exhaustively against the cascade.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
agree=tot=0; clear_n=0
uniq_agree=0
rng=random.Random(4321)
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        dmin=min(ds); c0=dmin//g
        # ground truth: no blocker at t = 1/(8 d_min)
        truth=all(circd(F(d)*TH/dmin)>=TH for d in ds)
        # criterion
        crit=all(c0 <= (d//g) % (8*c0) <= 7*c0 for d in ds)
        tot+=1; agree += (truth==crit); clear_n += truth
        # for contrast, the parallel session's predicate (scale g, not d_min)
        uniq=all((d//g)%8!=0 for d in ds)
        uniq_agree += (truth==uniq)
print(f"  {tot} subject-instances\n")
print(f"  clear at scale d_min (zero cascade moves) : {clear_n}  ({clear_n/tot:.4f})")
print(f"  CRITERION agrees with the cascade         : {agree}/{tot}   ({agree/tot:.6f})")
print(f"  'unique residue' agrees (their predicate) : {uniq_agree}/{tot}   ({uniq_agree/tot:.6f})")
print()
print("  criterion: for every disparity a (reduced),  c0 <= a mod 8c0 <= 7c0,  where c0 = d_min/g")
