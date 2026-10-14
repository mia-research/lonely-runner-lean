r"""
nr2_o_sweep  --  exact sweep of  o = |O|,  O = { x : the four unit runners
e_rho = 8 q_rho + rho (rho = 1,3,5,7) already cover all four ODD residues }.

By Lemma P1 (nr2_parity_reduction.py),  o <= 1/4  =>  |S| >= 1/2  =>  the leaf closes.
So the object of interest is the EXCEPTIONAL SET  X = { unit tuples : o > 1/4 }.

o is invariant under odd dilation (o(lam*E) = o(E), lam odd) -- checked in
nr2_dilation_check.py -- so X is a union of dilation orbits and we report the
gcd-reduced representative of each hit.

Exact integer arithmetic; cells evaluated at their ENTRY point.
Usage:  python3 nr2_o_sweep.py QMAX
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from collections import Counter
from nr2_core import o_measure, v_measure, u_measure

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
RH = (1, 3, 5, 7)

hits = []
mx = None
tot = 0
half = 0
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, RH))
    if len(set(sp)) != 4:
        continue
    tot += 1
    o = o_measure(sp)
    if mx is None or o > mx[0]:
        mx = (o, sp)
    if o >= F(1, 2):
        half += 1
    if o > F(1, 4):
        g = 0
        for e in sp:
            g = gcd(g, e)
        hits.append((o, sp, g, tuple(e // g for e in sp)))

print(f"unit tuples with q <= {QMAX} (speeds <= {8*QMAX+7}) : {tot}")
print(f"   MAX o = {mx[0]} = {float(mx[0]):.6f} at {mx[1]}")
print(f"   tuples with o >= 1/2 : {half}")
print(f"   tuples with o  > 1/4 : {len(hits)}")

orb = {}
for o, sp, g, red in hits:
    orb.setdefault((o, tuple(sorted(red))), []).append((sp, g))
print(f"   distinct (o, sorted reduced tuple) classes : {len(orb)}")
print("\n   the exceptional classes, by descending o:")
for (o, red), members in sorted(orb.items(), key=lambda kv: -kv[0][0]):
    gs = sorted({g for _, g in members})
    print(f"      o = {str(o):>16} = {float(o):.6f}   reduced (sorted) = {red}"
          f"   dilations present: {gs[:8]}{'...' if len(gs) > 8 else ''}"
          f"   #tuples = {len(members)}")
    if len(members) <= 6:
        print(f"            members: {[m[0] for m in members]}")
sys.stdout.flush()
