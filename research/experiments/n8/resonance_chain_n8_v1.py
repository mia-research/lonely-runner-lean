#!/usr/bin/env python3
"""Proposition 3.1 / 3.2 of lrc_n11_algebraic_lemma_v1.md, translated to n = 8.

At n=11: I_1's left edge 6/55 is closable only by runners 8,9, at the LEFT-EDGE RESONANCE
a = 25/3; its right edge 21/110 only at the RIGHT-EDGE RESONANCE a = 40/7.  Fixing those,
the Coupling Principle determines the ENTIRE chain, and Prop 3.1 finds that runner 9 at
a_9 = 25/3 SKIPS slot I_6 completely -- a forced gap.

Translated: at n=8, I_1 = [9,15]/56 has left edge 9/56 and right edge 15/56, so
   left  resonance   (n-1)/(n a) = 9/56   =>  a = 7*56/(8*9)  = 49/9
   right resonance   (n+1)/(n a) = 15/56  =>  a = 9*56/(8*15) = 21/5
This computes, for each resonance, the whole chain and which slots receive ZERO coverage.
Exact Fraction; no float.  Runs at n=11 as a reference check.
"""
import sys
from fractions import Fraction as F

def run(n, a, label):
    U = n*(n-1)                                   # report in units of 1/U
    S = {s: (F(n*s+1), F(n*s+n-1)) for s in range(1, n-1)}   # numerators over U
    print(f"  {label}:  a = {a}")
    hits = {s: [] for s in S}
    k = 0
    while True:
        lo, hi = F(n*k+n-1, n)/a*U, F(n*k+n+1, n)/a*U
        if lo > U: break
        touched = [s for s,(sl,sr) in S.items() if lo < sr and hi > sl]
        print(f"     B_{k} = [{lo}, {hi}]  ~ [{float(lo):.3f}, {float(hi):.3f}]"
              f"   touches {['I_'+str(s) for s in touched] if touched else '-- (gap)'}")
        for s in touched: hits[s].append(k)
        k += 1
    skipped = [s for s in S if not hits[s]]
    print(f"     => slots receiving ZERO coverage from this runner: "
          f"{['I_'+str(s) for s in skipped] if skipped else 'none'}")
    return skipped

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    if n == 8:
        print("n = 8, slots I_s = [8s+1, 8s+7] in units of 1/56")
        run(8, F(49,9),  "LEFT-edge resonance for I_1  (a = 49/9)")
        print()
        run(8, F(21,5),  "RIGHT-edge resonance for I_1 (a = 21/5)")
    else:
        print("n = 11, slots I_s = [11s+1, 11s+10] in units of 1/110  [reference check]")
        run(11, F(25,3), "LEFT-edge resonance for I_1  (a = 25/3)  -- Prop 3.1 says it skips I_6")
        print()
        run(11, F(40,7), "RIGHT-edge resonance for I_1 (a = 40/7)  -- Prop 3.2")
