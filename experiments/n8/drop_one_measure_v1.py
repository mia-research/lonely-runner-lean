#!/usr/bin/env python3
"""The "nearest prime below" reduction, made quantitative with the Boundary Set Method.

IDEA.  LRC(8) asks: 7 integer speeds, is some t lonely at level 1/8?
Drop one speed.  The remaining SIX have lonely set L6 at level 1/8.  The dropped speed v
has bad set {t : ||tv|| < 1/8} of measure EXACTLY 2/8 = 1/4, for every v.  So

        |L6| > 1/4   =>   L6 is not covered by the 7th speed   =>   LRC(8) holds for T.

Therefore the ONLY 7-tuples that can threaten LRC(8) are those where EVERY 6-subset has
|L6| <= 1/4.  This measures min |L6| exactly.

FRAME, fixed before running (deterministic exhaustive minimum, so the frame IS the spec):
  T a 6-subset of [1, M], M = 24, all C(24,6) = 134596 of them; no gcd restriction (a
  tuple with gcd g rescales t and has the SAME measure, so including them costs nothing
  and guards the enumeration).  Level 1/8.  Exact rationals throughout; measure is the
  exact sum of component lengths, reported as a Fraction.
OUTPUT: min |L6|, the minimising tuples, and the count with |L6| <= 1/4.
"""
import sys, os, io, contextlib
from fractions import Fraction as F
from itertools import combinations
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):
    from exact_phi_n_ap_v1 import lonely_set          # BSM, exact, event-complete

M, K, LEVEL = 24, 6, 8
THRESH = F(1, 4)                                       # measure of one speed's bad set

def measure(T):
    pts, ivs = lonely_set(list(T), LEVEL)
    return sum((c - a for a, c in ivs), F(0))

def job(first):
    best, arg, le = None, [], 0
    for rest in combinations(range(first + 1, M + 1), K - 1):
        T = (first,) + rest
        m = measure(T)
        if m <= THRESH: le += 1
        if best is None or m < best: best, arg = m, [T]
        elif m == best: arg.append(T)
    return best, arg, le

if __name__ == "__main__":
    with Pool(6) as pool:
        res = pool.map(job, range(1, M - K + 2))
    best = min(r[0] for r in res)
    arg = [T for r in res if r[0] == best for T in r[1]]
    le = sum(r[2] for r in res)
    tot = sum(1 for _ in combinations(range(1, M + 1), K))
    print(f"frame: all C({M},{K}) = {tot} six-subsets of [1,{M}], level 1/{LEVEL}, exact")
    print(f"threshold that decides LRC(8) by this route: |L6| > 1/4")
    print()
    print(f"MIN |L6| = {best} = {float(best):.6f}   ({len(arg)} minimising tuples)")
    for T in arg[:10]:
        print(f"    {list(T)}")
    print()
    print(f"tuples with |L6| <= 1/4 (i.e. NOT decided by this route): {le} of {tot} "
          f"= {le*100.0/tot:.3f}%")
    print(f"tuples with |L6| >  1/4 (LRC(8) holds for every 7-tuple containing them): "
          f"{tot-le} of {tot} = {(tot-le)*100.0/tot:.3f}%")
