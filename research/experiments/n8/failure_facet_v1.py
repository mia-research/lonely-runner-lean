"""What do the 603 failures share?  Exact arithmetic, so these are real boundaries."""
from fractions import Fraction as F
from itertools import combinations
from math import lcm
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
    P = lcm(*[m//s for s in sub]); lo, hi = -(-(m-1)//8), (7*m-1)//8
    for n, sp in ((6, list(sub)), (7, [1]+list(sub))):
        for t in witnesses(sp, n):
            q0 = round(t*m); k0 = (lo-q0)//max(P,1) - 1
            for k in range(k0, k0 + (hi-lo)//max(P,1) + 3):
                q = q0 + k*P
                if lo <= q <= hi and not any(blocks(si, 8*q+1, m) for si in S): return True
    return False

fails, oks = [], []
for m in range(24, 400):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        S = (1,) + c + (m,)
        (fails if not settled(S, m, c) else oks).append((m, c))

def bs(m, c): return sorted(m//s for s in c)
print(f"failures {len(fails):,}   successes {len(oks):,}\n")
for lab, pop in (("FAIL", fails), ("OK", oks)):
    small = Counter()
    minb = Counter()
    for m, c in pop:
        B = bs(m, c)
        small[sum(1 for b in B if b <= 7)] += 1
        minb[min(B)] += 1
    n = len(pop)
    print(f"{lab:<5} how many b_i <= 7 : " +
          "  ".join(f"{k}:{100*v/n:5.1f}%" for k, v in sorted(small.items())))
    print(f"{lab:<5} smallest b_i      : " +
          "  ".join(f"{k}:{100*v/n:5.1f}%" for k, v in sorted(minb.items())[:8]))
    print()
print("does EVERY failure contain a b_i <= 7 ?",
      all(any(b <= 7 for b in bs(m,c)) for m,c in fails))
print("does every failure contain b_i = 2 ?",
      all(2 in bs(m,c) for m,c in fails))
print("\nfailures with their b-multisets (first 8):")
for m, c in fails[:8]: print(f"   m={m:<4} b = {bs(m,c)}")
