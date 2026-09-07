#!/usr/bin/env python3
"""Next link: with the two I_1-closers pinned, can every boundary still be covered?

Established: closing I_1's left edge 9/56 needs a_j in [49/9, 7] (only k=0 reaches it), so
L in {5,6}; closing the right edge 15/56 needs a_j in [49/15, 21/5], so R in {3,4,5}.
49/9 > 21/5, so L != R: I_1 alone pins TWO of the five free runners.

For each admissible (L,R) this computes, for every one of the 12 slot boundaries, which
runners can still reach it given a_L in [49/9, min(L+1,7)] and a_R in [49/15, min(21/5,R+1)],
the other three free in (j-1, j+1).  A boundary with NO available coverer kills that (L,R).
Exact Fraction only; no float on any decision.
"""
import sys
from fractions import Fraction as F

N = 8
SLOT = {s: (F(8*s+1), F(8*s+7)) for s in range(1, 7)}          # units of 1/56
def window(b, k):                                              # a-range where B_{j,k} ∋ b/56
    return (F(7*(8*k+7), 1)/b, F(7*(8*k+9), 1)/b)

def reach(j, b, lo, hi):
    """Sub-ranges of [lo,hi] where runner j can cover boundary b (any k)."""
    out = []
    for k in range(0, 40):
        wl, wh = window(b, k)
        l, h = max(lo, wl), min(hi, wh)
        if l < h: out.append((l, h))
    return out

BOUNDS = []
for s,(bl,br) in SLOT.items():
    BOUNDS += [(s, "L", bl), (s, "R", br)]

Lrange = {5: (F(49,9), F(6)), 6: (F(49,9), F(7))}
Rrange = {3: (F(49,15), F(4)), 4: (F(49,15), F(21,5)), 5: (F(4), F(21,5))}

print("boundary coverage with the two I_1-closers pinned (units of 1/56)")
for L, (Ll, Lh) in Lrange.items():
    for R, (Rl, Rh) in Rrange.items():
        if L == R: continue
        rng = {}
        for j in range(2, 7):
            if j == L:   rng[j] = (Ll, Lh)
            elif j == R: rng[j] = (Rl, Rh)
            else:        rng[j] = (F(j-1), F(j+1))
        print(f"\n  L = {L} (a in [{Ll},{Lh}]),  R = {R} (a in [{Rl},{Rh}])")
        dead = []
        for s, side, b in BOUNDS:
            able = [j for j in range(2,7) if reach(j, b, *rng[j])]
            if not able: dead.append((s, side, b))
            flag = "   <== NO COVERER" if not able else ("   <-- only " + str(able) if len(able)<=1 else "")
            print(f"     I_{s}{side} b={b}: runners {able}{flag}")
        print(f"     => boundaries with no available coverer: {len(dead)}"
              + (f"   {[(f'I_{s}{d}') for s,d,_ in dead]}   ** (L,R) ELIMINATED **" if dead else ""))
