"""The facet: small b (<= 7) obey an EXACT law (b | q blocks), large b need rounding.
Rounding error 1/(2b) is useless at b = 2.  So: round for the LARGE readings only, then shift q
by multiples of lcm(large b) -- which preserves every large condition -- to satisfy the small
congruences exactly.
"""
from fractions import Fraction as F
from itertools import combinations
from math import lcm

def norm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)
def witnesses(speeds, n):
    out = []
    for s in sorted(set(speeds)):
        A = s + ((1-s) % n)
        while A <= (n-1)*s:
            t = F(A, n*s)
            if all(norm(sp*t) >= F(1,n) for sp in speeds): out.append(t)
            A += n
    return out
def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

def settled(S, m, sub):
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    small = [s for s in sub if m//s <= 7]
    large = [s for s in sub if m//s >= 8]
    Plarge = lcm(*[m//s for s in large]) if large else 1
    speed_sets = []
    if large: speed_sets += [(6, list(large)), (7, [1]+list(large))]
    speed_sets += [(6, list(sub)), (7, [1]+list(sub))]
    for n, sp in speed_sets:
        for t in witnesses(sp, n):
            q0 = round(t*m)
            k0 = (lo - q0)//Plarge - 1
            for k in range(k0, k0 + (hi-lo)//Plarge + 3):
                q = q0 + k*Plarge
                if lo <= q <= hi and not any(blocks(si, 8*q+1, m) for si in S):
                    return True
    return False

tot = fail = 0; exs = []
for m in range(24, 400):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        S = (1,) + c + (m,)
        tot += 1
        if not settled(S, m, c):
            fail += 1
            if len(exs) < 6: exs.append((m, sorted(m//s for s in c)))
print(f"ALL divisor-closed, exhaustive m < 400 : {tot:,}")
print(f"  previous route NOT settled           : 603")
print(f"  COMBINED route NOT settled           : {fail:,}")
for m, b in exs: print(f"     m={m:<4} b={b}")
