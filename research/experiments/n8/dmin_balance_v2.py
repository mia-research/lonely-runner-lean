"""Sample maximum was 5 failing disparities.  d_min always clears, so the ceiling is 6 -- but a
sample maximum is not a bound (established twice today: the M <= 7 artifact, and a parallel
session's "max 3 per slot" forced by its enumeration cap).  Construct, do not sample.

With c = 1 the bad bands are  a mod 8 in [0,1) or (7,8);  for integers that is exactly  8 | a.
So take disparities {1, 8, 16, 24, 32, 40, 48}: six multiples of 8 plus the minimum.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def report(v,i):
    v=speeds(v); g=gcd_all(v)
    ds=[abs(v[j]-v[i])//g for j in range(8) if j!=i]
    c=min(ds)
    bad=[a for a in ds if not (c <= a%(8*c) <= 7*c)]
    truth=all(circd(F(a)*TH/c)>=TH for a in ds)
    print(f"  v = {str(list(v)):<36} subject {v[i]}")
    print(f"    reduced disparities {sorted(ds)}   c = {c}   S = {max(ds)/c:g}")
    print(f"    failing disparities : {sorted(bad)}   count = {len(bad)}")
    print(f"    cascade agrees clear = {truth}, criterion says clear = {not bad}   {'OK' if truth==(not bad) else 'MISMATCH'}")
print("  constructed witness for 6 failing disparities:")
report([1,2,9,17,25,33,41,49], 0)
print()
print("  can all 7 fail?  d_min itself has a = c, residue c, on the lower boundary -- clear.")
print("  So 6 is the ceiling and it is ATTAINED.  The sample maximum of 5 was a sampling artifact.")
print()
print("  check the ceiling is real: try to force the minimum to fail")
v=speeds([1,2,9,17,25,33,41,49]); g=gcd_all(v)
ds=[abs(v[j]-v[0])//g for j in range(8) if j!=0]; c=min(ds)
print(f"    c = {c},  c mod 8c = {c%(8*c)},  band = [{c}, {7*c}]  -> clear: {c <= c%(8*c) <= 7*c}")
