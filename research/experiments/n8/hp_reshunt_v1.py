r"""
Targeted counterexample hunt for (H''):  o <= 1/3 outside {(1,3,5,7), (1,11,5,7)}.

Random sampling is the WRONG instrument here -- it lands on non-resonant tuples where
o -> 3/32.  The danger zone is RESONANT tuples at moderate speeds: far enough from the
limit that o has not yet settled, large enough to be outside the exhaustive q <= 8 sweep.

The only +-1 relations possible are
   A:  e1 + e7 = e3 + e5     (sign vector (1,-1,-1,1))
   B:  e1 + e3 = e5 + e7     (sign vector (1,1,-1,-1))
and (1,-1,1,-1) is impossible since 1-3+5-7 = -4 is not 0 mod 8.  A and B are mutually
exclusive: together they force e1 = e5, impossible as e1 = 1 and e5 = 5 mod 8.
With e_rho = 8*(a,b,c,d) + (1,3,5,7):   A <=> d = b+c-a ;   B <=> d = a+b-c-1.

Exact Fractions throughout; cells evaluated at their ENTRY point.
"""
import sys, itertools
from math import gcd, lcm
from functools import reduce
from fractions import Fraction as F
from hp_omax_v1 import ou

THIRD = F(1,3)
CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 14
EXC = {(1,3,5,7), (1,11,5,7)}

best = {}
hits = []
n = 0
for fam, dfun in (("A", lambda a,b,c: b+c-a), ("B", lambda a,b,c: a+b-c-1)):
    for a,b,c in itertools.product(range(CAP+1), repeat=3):
        d = dfun(a,b,c)
        if d < 0: continue
        sp = (8*a+1, 8*b+3, 8*c+5, 8*d+7)
        if len(set(sp)) != 4: continue
        if reduce(gcd, sp) != 1: continue
        n += 1
        o,u = ou(sp)
        if o > THIRD and sp not in EXC: hits.append((o,u,sp,fam))
        if fam not in best or o > best[fam][0]: best[fam] = (o,u,sp)
print(f"resonant primitive tuples scanned (a,b,c <= {CAP}, both families): {n}")
print(f"   max speed reachable: {8*2*CAP+7}")   # d = b+c-a <= 2*CAP, NOT 3*CAP
print(f"   NOTE: this is a PARAMETER box (a,b,c <= CAP), not a speed box.")
for fam in ("A","B"):
    o,u,sp = best[fam]
    print(f"   family {fam}: max o = {o} = {float(o):.6f}  at {sp}  (u = {u})")
print(f"\n   tuples with o > 1/3 outside the two known exceptions: {len(hits)}")
for o,u,sp,fam in sorted(hits, reverse=True)[:10]:
    print(f"      {sp}  fam {fam}  o = {o} = {float(o):.6f}  u = {u}")
if not hits:
    print("      none -- (H'') survives this sweep")
