"""Is the widest clear component always >= 5/(8m)?  (observed min ratio exactly 0.625 = 5/8)
Test on a wider range, and on NON-divisor-closed profiles too."""
from fractions import Fraction as F
from itertools import combinations
import random

def widest(speeds):
    bad = []
    for s in speeds:
        k = 0
        while F(8*k-1, 8*s) < 1:
            lo, hi = F(8*k-1, 8*s), F(8*k+1, 8*s)
            if hi > 0 and lo < 1: bad.append((max(lo, F(0)), min(hi, F(1))))
            k += 1
    bad.sort(); merged = []
    for a, b in bad:
        if merged and a <= merged[-1][1]: merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else: merged.append((a, b))
    w, cur = F(0), F(0)
    for a, b in merged:
        if a > cur: w = max(w, a - cur)
        cur = max(cur, b)
    if cur < 1: w = max(w, 1 - cur)
    return w

mn = None; arg = None; tot = 0
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        tot += 1
        r = widest([1]+list(c)) * m
        if mn is None or r < mn: mn, arg = r, (m, sorted(m//s for s in c))
print(f"DIVISOR-CLOSED, m < 320 : {tot:,} profiles")
print(f"  min (widest clear component) x m = {mn} = {float(mn):.6f}   at m={arg[0]} b={arg[1]}")
print(f"  is it exactly 5/8 ? {mn == F(5,8)}")

# non-divisor-closed: arbitrary 6 speeds
rng = random.Random(20260919); mn2 = None; arg2 = None
for _ in range(20000):
    S = sorted(rng.sample(range(2, 200), 5))
    m = max(S)
    r = widest([1]+S) * m
    if mn2 is None or r < mn2: mn2, arg2 = r, S
print(f"\nARBITRARY 6 speeds (scaled by max), 20,000 samples")
print(f"  min (widest) x max(S) = {mn2} = {float(mn2):.6f}   at S={arg2}")

# what does the gap rule predict as a floor?
print(f"\n  gap rule floor for a pair (s,s'): 1/(8 s s').  With s,s' <= m/2 that is 1/(2m^2),")
print(f"  far below 5/(8m).  So the 5/8 floor is NOT the gap rule -- something else sets it.")
