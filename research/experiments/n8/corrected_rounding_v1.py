"""Why the route didn't work: I rounded to q/m, but the candidate is tau = (8q+1)/(8m).
They differ by 1/(8m), costing an extra 1/(8 b_i).  Correct rounding: q = round(t*m - 1/8),
which gives |tau - t| <= 1/(2m) and margin 1/(2 b_i)  ->  threshold b_i >= 28 as derived.
"""
from fractions import Fraction as F
from math import lcm
import random

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

def route(S, m, sub, mode):
    ws = witnesses([1]+list(sub), 7)
    if not ws: return "no_t"
    for t in ws:
        q = round(t*m) if mode == "old" else round(t*m - F(1,8))
        A = 8*q + 1
        if m <= A <= 7*m and not any(blocks(si, A, m) for si in S): return "ok"
    return "fail"

rng = random.Random(20260919)
print(f"{'arm':<46} {'profiles':>8} {'OLD fail':>9} {'NEW fail':>9}")
for lo_b in (8, 16, 28, 35):
    for eq in (True, False):
        tot = o = nn = 0
        for m in range(8, 2500):
            ds = [d for d in range(2, m) if m % d == 0 and m//d >= lo_b]
            if len(ds) < 5: continue
            for _ in range(4):
                sub = tuple(sorted(rng.sample(ds, 5)))
                if (lcm(*[m//s for s in sub]) == m) != eq: continue
                S = tuple(sorted({1, m} | set(sub)))
                if len(S) != 7: continue
                tot += 1
                if route(S, m, sub, "old") != "ok": o += 1
                if route(S, m, sub, "new") != "ok": nn += 1
            if tot > 500: break
        lab = f"b_i >= {lo_b}, lcm {'=' if eq else '!='} m"
        print(f"  {lab:<44} {tot:>8} {o:>9} {nn:>9}")
