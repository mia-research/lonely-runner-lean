"""Probe the zero-slack configurations. classify(s) returns:
   'empty'    -- no isolation instant in the window  (a COUNTEREXAMPLE to the first-interval claim)
   'tight'    -- isolation instants exist but only as isolated points (zero slack)
   'interior' -- the good set has positive length
Exact rationals; the good set is closed, bad intervals open, boundary points kept."""
from fractions import Fraction as F

def classify(s):
    lo, hi = F(1, 8), F(7, 8)
    bad = []
    for x in s:
        k = 0
        while F(8*k - 1, 8) / x <= hi:
            a, b = F(8*k - 1, 8) / x, F(8*k + 1, 8) / x
            if b > lo and a < hi:
                bad.append((max(a, lo), min(b, hi)))
            k += 1
    bad.sort()
    cur = lo
    for a, b in bad:
        if a > cur:
            return 'interior'
        cur = max(cur, b)
        if cur > hi:
            break
    else:
        if cur < hi:
            return 'interior'
    pts = {lo, hi} | {a for a, b in bad} | {b for a, b in bad}
    good = [p for p in pts if lo <= p <= hi
            and all(min((x*p) % 1, 1 - (x*p) % 1) >= F(1, 8) for x in s)]
    return 'tight' if good else 'empty'
