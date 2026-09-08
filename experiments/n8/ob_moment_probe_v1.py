r"""Probe: how do E C, E C^2 and the collision statistics behave for LARGE generic
tuples?  If they converge to the equidistributed 3/2 and 27/8 the moment bound is
asymptotically 5/16; if not, the bound is structurally wrong."""
import random, sys
from fractions import Fraction as F
from functools import reduce
from math import gcd
from ob_core_v1 import MUV, _cellpts_t, o_torus, relations
from ob_moment_v1 import sweep, bound, PAIRS

random.seed(20260908)
print(f"{'tuple':>28} {'o':>9} {'E C':>9} {'E C^2':>9} {'bound':>9}   rel")
def rnd(qmax):
    while True:
        e = tuple(8*random.randrange(qmax//2, qmax)+r for r in (1,3,5,7))
        if reduce(gcd, e) == 1 and len(set(e)) == 4:
            return e
for qmax in (10, 25, 60, 150):
    for _ in range(3):
        e = rnd(qmax)
        o, EC, EC2, dist = sweep(e)
        B = bound(EC, EC2)
        print(f"{str(e):>28} {float(o):>9.5f} {float(EC):>9.5f} {float(EC2):>9.5f} {float(B):>9.5f}   {relations(e)}")
print("\nequidistributed reference:  o = 3/32 = 0.09375, E C = 1.5, E C^2 = 3.375, bound = 0.3125")
print("\ndistribution of C for a large tuple vs the equidistributed one (24,144,36,48,4)/256:")
e = rnd(150)
o, EC, EC2, dist = sweep(e)
print("  ", e, {c: (float(w), round(float(w)*256,2)) for c, w in sorted(dist.items())})
print("   reference:", {0:24/256, 1:144/256, 2:36/256, 3:48/256, 6:4/256})
