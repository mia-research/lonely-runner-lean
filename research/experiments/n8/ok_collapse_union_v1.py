#!/usr/bin/env python3
"""THE ODD-COLLAPSE SET AND A UNION BOUND.  Exact Fraction, no float.

C  = { t : some odd residue is left free by the ODD runners }          (odd runners only)
B_e= { t in C : runner e blocks the freed residue }   for each v2>=1 runner e

    |C| > sum_e |B_e|   =>   C is not covered  =>  a witness.      (union bound; no
independence, no search, and the converse is false so it is not forced.)

Why this is the right object: by the quarter dichotomy the failure set is 1/4-periodic, so
the whole of C matters, not one near-zero window.  And the window route is dead for a
structural reason -- |W| is O(1/e^2) while each obstacle component is 1/(4e), O(1/e).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

LVL = F(1, 8)
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)
def blocked(e, t):
    return {j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < LVL}
def v2(e):
    k = 0
    while e % 2 == 0: e //= 2; k += 1
    return k
ODD = (1, 3, 5, 7)

def cells(T):
    cuts = sorted({F(m, 8*e) for e in T for m in range(0, 8*e+1)} | {F(0), F(1)})
    return [(cuts[i], cuts[i+1]) for i in range(len(cuts)-1) if cuts[i] < cuts[i+1]]

def analyse(T):
    odd = [e for e in T if e % 2]
    obst = [e for e in T if v2(e) >= 1]
    mC = F(0); mB = {e: F(0) for e in obst}
    for lo, hi in cells(T):
        t = (lo + hi) / 2; w = hi - lo
        free = [v for v in ODD if not any(v in blocked(e, t) for e in odd)]
        if not free: continue
        mC += w
        # SOUNDNESS: designate ONE free residue v* = min(free).  t fails  =>  some e
        # blocks v*.  So F is inside the union of B*_e and the union bound is valid for
        # every a.  (Requiring e to block ALL free residues would be UNSOUND: different
        # runners may block different free residues.)
        vstar = min(free)
        for e in obst:
            if vstar in blocked(e, t): mB[e] += w
    return mC, sum(mB.values()), mB

def run(box=16, cap=300):
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    fires = fails = 0
    from collections import Counter
    bya = Counter(); fa = Counter()
    worst = None
    for T in tuples:
        a = sum(1 for e in T if e % 2)
        mC, mB, _ = analyse(list(T))
        bya[a] += 1
        if mC > mB:
            fires += 1; fa[a] += 1
        else:
            fails += 1
            if worst is None or (mC - mB) > worst[0]: worst = (mC - mB, T, mC, mB)
    n = len(tuples)
    print(f"UNION BOUND |C| > sum|B_e| over {n} Case-2 tuples from [1..{box}]")
    print(f"  fires : {fires}  ({100*fires//n}%)      fails : {fails}   (not forced)")
    print(f"  by a = #odd speeds:")
    for a in sorted(bya):
        print(f"    a={a}: fires {fa[a]:>4} / {bya[a]:>4}")
    if worst:
        d, T, mC, mB = worst
        print(f"  closest miss: {T}  |C|={float(mC):.4f}  sum|B|={float(mB):.4f}")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 16)
