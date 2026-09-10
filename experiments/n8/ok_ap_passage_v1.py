#!/usr/bin/env python3
"""THE AP GRID AND THE PASSAGE OF ONE RUNNER.  Exact Fraction, no float.

The AP (1,...,7) is the tight instance: its four witnesses t = r/8 (r odd) are each pinned
by EXACTLY TWO runners, those with j = +-r mod 8 -- {1,7} at r=1,7 and {3,5} at r=3,5.
Runners 2,4,6 are never tight.  Deform a_j = j + eps_j and put t = r/8 + delta: the runner
with e*r = 1 mod 8 needs delta > 0, the one with e*r = 7 mod 8 needs delta < 0, so to first
order the windows open iff

    t=1/8 : eps_7 < 7 eps_1        t=7/8 : 7 eps_1 < eps_7
    t=3/8 : 3 eps_5 < 5 eps_3      t=5/8 : 5 eps_3 < 3 eps_5

-- complementary in pairs, degenerate exactly on a_7 = 7 a_1 and 5 a_3 = 3 a_5.

This script drops the linearisation and sweeps one speed EXACTLY across its whole passage
from its slower neighbour to its faster one, reporting |G| and which witness carries it.
|G| is dilation invariant, so a_j = k/q is run as the integer tuple q*a.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import sys

LVL = F(1, 8)

def good_measure(E):
    """|{t in [0,1): ||e t|| > 1/8 for all e}|, exact; also the good intervals."""
    iv = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = F(8 * k - 1, 8 * e), F(8 * k + 1, 8 * e)
            iv.append((max(lo, F(0)), min(hi, F(1))))
    iv = sorted(x for x in iv if x[0] < x[1])
    merged = []
    for lo, hi in iv:
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    good, cur, tot = [], F(0), F(0)
    for lo, hi in merged:
        if cur < lo: good.append((cur, lo)); tot += lo - cur
        cur = max(cur, hi)
    if cur < 1: good.append((cur, F(1))); tot += 1 - cur
    return tot, good

def which_witness(good):
    """which of the four AP witnesses r/8 does each good component sit nearest?"""
    out = []
    for lo, hi in good:
        mid = (lo + hi) / 2
        r = min((1, 3, 5, 7), key=lambda r: abs(mid - F(r, 8)))
        out.append(r)
    return sorted(set(out))

def sweep(j, q=60, span=None):
    """vary a_j across (a_{j-1}, a_{j+1}); everything else stays on the AP."""
    base = [1, 2, 3, 4, 5, 6, 7]
    lo_n = base[j - 2] if j >= 2 else 0
    hi_n = base[j] if j <= 6 else 8
    zeros, rows = [], []
    for k in range(lo_n * q + 1, hi_n * q):
        a = list(base); a[j - 1] = F(k, q)
        E = [int(x * q) for x in a]
        g = reduce(gcd, E)
        E = sorted(set(x // g for x in E))
        if len(E) != 7: continue                      # collision with a neighbour
        m, good = good_measure(E)
        if m == 0: zeros.append(F(k, q))
        rows.append((F(k, q), m, which_witness(good)))
    return zeros, rows

if __name__ == "__main__":
    q = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print(f"AP = (1,...,7).  Sweeping one speed at a time, step 1/{q}, exact.\n")
    for j in (1, 2, 3, 4, 5, 6, 7):
        zeros, rows = sweep(j, q)
        print(f"runner {j}: a_{j} from {rows[0][0]} to {rows[-1][0]}, "
              f"{len(rows)} admissible values")
        print(f"   |G| = 0 at a_{j} = {[str(z) for z in zeros]}")
        nz = [r for r in rows if r[1] > 0]
        if nz:
            mn = min(nz, key=lambda r: r[1])
            print(f"   smallest positive |G| = {mn[1]} at a_{j} = {mn[0]}"
                  f"  (carried by witness {mn[2]})")
            # which witnesses carry the good set on either side of the AP point
            left = [r for r in nz if r[0] < j][-1:] ; right = [r for r in nz if r[0] > j][:1]
            if left:  print(f"   just BELOW a_{j}={j}: |G|={left[0][1]}  witness {left[0][2]}")
            if right: print(f"   just ABOVE a_{j}={j}: |G|={right[0][1]}  witness {right[0][2]}")
        print()
