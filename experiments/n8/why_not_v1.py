"""Full exhaustive re-test with the corrected rounding + all normalised witnesses.
Then: WHERE does it still fail, and why."""
from fractions import Fraction as F
from itertools import combinations
from collections import Counter

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
    for n, sp in ((7, [1]+list(sub)), (6, list(sub))):
        for t in witnesses(sp, n):
            for q in (round(t*m - F(1,8)), round(t*m), round(t*m - F(1,8)) + 1,
                      round(t*m - F(1,8)) - 1):
                A = 8*q + 1
                if m <= A <= 7*m and not any(blocks(si, A, m) for si in S): return True
    return False

tot = fail = 0; fb = Counter(); ok_b = Counter(); exs = []
for m in range(24, 400):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        S = (1,) + c + (m,); tot += 1
        B = sorted(m//s for s in c)
        if settled(S, m, c): ok_b[min(B)] += 1
        else:
            fail += 1; fb[min(B)] += 1
            if len(exs) < 6: exs.append((m, B))
print(f"ALL divisor-closed, exhaustive m < 400 : {tot:,}")
print(f"  earlier route (round t*m, no 1/8)    : 603 not settled")
print(f"  CORRECTED route                      : {fail:,} not settled\n")
n = max(fail,1)
print(f"  failures by smallest b : " + "  ".join(f"{k}:{100*v/n:.1f}%" for k,v in sorted(fb.items())))
s = sum(ok_b.values())
print(f"  successes by smallest b: " + "  ".join(f"{k}:{100*v/s:.1f}%" for k,v in sorted(ok_b.items())[:6]))
print()
for m, B in exs: print(f"     m={m:<4} b={B}")
