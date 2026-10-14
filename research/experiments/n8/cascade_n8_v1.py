#!/usr/bin/env python3
"""Next links of the n=8 cascade: what the two I_1-closers COST, over their whole ranges.

Frame (large ratio): a_7 = 7 pacemaker, free runners 2..6, a_j in (j-1, j+1),
slots I_s = [8s+1, 8s+7] in units of 1/56, chain B_{j,k}(a) = [7(8k+7)/a, 7(8k+9)/a] (same units).

Closing I_1's LEFT edge 9/56 needs B_{j,0} ∋ 9/56, i.e. a in [49/9, 7]  (only k=0 qualifies).
Closing I_1's RIGHT edge 15/56 needs a in [49/15, 21/5]                 (only k=0 qualifies).
Since 49/9 > 21/5 these ranges are disjoint: the two closers are DISTINCT runners.

For a closer with a in [lo,hi], B_k meets I_s iff  7(8k+7)/a < 8s+7  and  7(8k+9)/a > 8s+1,
i.e.  a > 7(8k+7)/(8s+7)  and  a < 7(8k+9)/(8s+1).  Intersecting with [lo,hi] gives the
sub-range where that runner touches I_s.  A slot whose union of sub-ranges misses part of
[lo,hi] is NOT covered by this runner there -- and must be covered by someone else.
Exact Fraction only.
"""
import sys
from fractions import Fraction as F

def touch_ranges(lo, hi, s, kmax=40):
    """Sub-intervals of [lo,hi] where the chain touches slot I_s."""
    sl, sr = F(8*s+1), F(8*s+7)
    out = []
    for k in range(kmax):
        l, h = max(lo, F(7*(8*k+7), 1)/sr), min(hi, F(7*(8*k+9), 1)/sl)
        if l < h: out.append((l, h))
    out.sort()
    merged = []
    for l, h in out:
        if merged and l <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], h)
        else: merged.append([l, h])
    return merged

def gaps(lo, hi, cov):
    g, cur = [], lo
    for l, h in cov:
        if l > cur: g.append((cur, l))
        cur = max(cur, h)
    if cur < hi: g.append((cur, hi))
    return g

def report(name, j, lo, hi):
    print(f"  {name}: runner {j}, a in [{lo}, {hi}]  (~[{float(lo):.4f}, {float(hi):.4f}])")
    for s in range(1, 7):
        cov = touch_ranges(lo, hi, s)
        gp = gaps(lo, hi, cov)
        if not gp:
            print(f"     I_{s}: touched throughout")
        else:
            tot = sum(h-l for l,h in gp)
            print(f"     I_{s}: NOT touched on " +
                  ", ".join(f"[{l},{h}]" for l,h in gp) +
                  f"   (measure {tot} = {float(tot):.4f} of {float(hi-lo):.4f})")

if __name__ == "__main__":
    print("LEFT closers of I_1 (need a >= 49/9):")
    report("L", 5, F(49,9), F(6));  report("L", 6, F(49,9), F(7))
    print()
    print("RIGHT closers of I_1 (need a <= 21/5):")
    report("R", 3, F(49,15), F(4)); report("R", 4, F(49,15), F(21,5)); report("R", 5, F(4), F(21,5))
