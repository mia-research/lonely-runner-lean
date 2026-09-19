"""Derived from OUR gap rule, not from rounding.

At order 7 the clear intervals between bad sets have width >= 1/(s_i s_j) (GapRule.gap_ge).
The witness must be a grid point q/m, so a clear interval contains one once its width >= 1/m:

        1/(s_i s_j) >= 1/m    <=>    s_i * s_j <= m     for every pair.

Test: (a) does that condition imply the profile is settled by a grid point, and
      (b) how much of the divisor-closed category does it cover?
"""
from itertools import combinations
from fractions import Fraction as F

def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

def has_grid_witness(S, m):
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    for q in range(lo, hi+1):
        if not any(blocks(si, 8*q+1, m) for si in S): return True
    return False

tot = cond = cond_fail = nocond = nocond_clear = 0
for m in range(24, 400):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        S = (1,) + c + (m,)
        tot += 1
        ok = all(a*b <= m for a, b in combinations(c, 2))
        if ok:
            cond += 1
            if not has_grid_witness(S, m): cond_fail += 1
        else:
            nocond += 1
            if has_grid_witness(S, m): nocond_clear += 1
print(f"ALL divisor-closed, exhaustive m < 400 : {tot:,}\n")
print(f"  pairs satisfy s_i*s_j <= m           : {cond:,}  ({100*cond/tot:.2f}%)")
print(f"     of those, NO grid witness         : {cond_fail:,}   (the derivation says 0)")
print(f"  condition fails                      : {nocond:,}")
print(f"     of those, grid witness anyway     : {nocond_clear:,}  "
      f"({100*nocond_clear/max(nocond,1):.2f}%)  -- sufficient, not necessary")
