#!/usr/bin/env python3
"""Where is slot coverage BOTTLENECKED onto a single runner?

A completely blocking configuration must cover every point of every slot.  For a point p
(units of 1/56) runner j can cover it iff for some k the window [7(8k+7)/p, 7(8k+9)/p] meets
j's sign range (j-1, j+1).  The able-set is piecewise constant in p, changing only at
   p = 7(8k+7)/c  and  p = 7(8k+9)/c   for c in {1,...,7} (the sign-range endpoints).
Points whose able-set is a SINGLETON {j} FORCE runner j into the window covering them --
this is exactly how the n=11 proof gets "closing I_4 requires a_2 >= 20/9".
If one runner is forced by two points into disjoint windows, the configuration is impossible.
Exact Fraction only; no float on any decision.
"""
import sys
from fractions import Fraction as F

SLOT = {s: (F(8*s+1), F(8*s+7)) for s in range(1, 7)}
RUNNERS = list(range(2, 7))
def sign_range(j): return (F(j-1), F(j+1))

def windows(j, p):
    """a-windows (within j's sign range) that let runner j cover point p."""
    lo, hi = sign_range(j); out = []
    for k in range(0, 40):
        l, h = max(lo, F(7*(8*k+7))/p), min(hi, F(7*(8*k+9))/p)
        if l < h: out.append((l, h))
    return out

# breakpoints
BP = set()
for c in range(1, 8):
    for k in range(0, 40):
        for num in (7*(8*k+7), 7*(8*k+9)):
            p = F(num, c)
            if 9 <= p <= 55: BP.add(p)
BP = sorted(BP)

print("Slot-coverage bottlenecks at n = 8 (units of 1/56), sign ranges a_j in (j-1,j+1)")
forced = {}
for s,(sl,sr) in SLOT.items():
    pts = [p for p in BP if sl < p < sr]
    cells = []
    prev = sl
    for p in pts + [sr]:
        mid = (prev + p) / 2
        if prev < p:
            able = [j for j in RUNNERS if windows(j, mid)]
            cells.append((prev, p, able))
        prev = p
    singles = [(a,b,ab[0]) for a,b,ab in cells if len(ab) == 1]
    print(f"  I_{s} = [{sl},{sr}]: {len(cells)} cells; "
          f"min able-set size {min(len(ab) for _,_,ab in cells)}")
    for a,b,j in singles:
        w = windows(j, (a+b)/2)
        print(f"     cell [{a},{b}] reachable ONLY by runner {j}"
              f"  -> forces a_{j} into {[(str(l),str(h)) for l,h in w]}")
        forced.setdefault(j, []).append((s, a, b, w))
print()
print("Runners forced by more than one slot:")
for j, lst in sorted(forced.items()):
    ss = sorted({s for s,_,_,_ in lst})
    if len(ss) > 1:
        print(f"  runner {j} forced by slots {ss}")
        for s,a,b,w in lst:
            print(f"     I_{s} cell [{a},{b}] -> a_{j} in {[(str(l),str(h)) for l,h in w]}")
if not forced: print("  (none: every cell of every slot is reachable by >= 2 runners)")
