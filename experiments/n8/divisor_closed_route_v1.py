"""THE test: does the combined route settle EVERY divisor-closed profile, mixed b included?

Route: enumerate the normalised witnesses of the order-6 instance (speeds = the 5 middle readings)
and the order-7 instance (speeds = {1} + those five); round each to q = round(t*m); shift by the
period lcm(b_i) into the admissible range; check.
No threshold on b, no restriction on lcm.
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
    P = lcm(*[m//s for s in sub])
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    for n, speeds in ((6, list(sub)), (7, [1]+list(sub))):
        for t in witnesses(speeds, n):
            q0 = round(t*m)
            k0 = (lo - q0)//max(P,1) - 1
            for k in range(k0, k0 + (hi-lo)//max(P,1) + 3):
                q = q0 + k*P
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
            if len(exs) < 5: exs.append((m, c))
print(f"ALL divisor-closed profiles, exhaustive m < 400 : {tot:,}")
print(f"  NOT settled by the combined route             : {fail:,}")
for e in exs: print("     m=%d  middle=%s" % e)
