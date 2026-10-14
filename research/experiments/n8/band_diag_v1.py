"""Look at the ACTUAL failures of the order-7 rounding route on lcm(b_i) = m."""
from fractions import Fraction as F
from math import lcm
import random

def norm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)
def find_t(speeds, thr, D):
    for j in range(1, D):
        t = F(j, D)
        if all(norm(s*t) >= thr for s in speeds): return t
    return None
def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

rng = random.Random(20260919)
fails = []
tot = 0
for m in range(8, 2500):
    ds = [d for d in range(2, m) if m % d == 0 and m//d >= 28]
    if len(ds) < 5: continue
    for _ in range(4):
        sub = tuple(sorted(rng.sample(ds, 5)))
        bs = [m//s for s in sub]
        if lcm(*bs) != m: continue
        S = tuple(sorted({1, m} | set(sub)))
        if len(S) != 7: continue
        tot += 1
        t = find_t([1]+list(sub), F(1,7), 8*m)
        q = round(t*m); A = 8*q+1
        lo, hi = -(-(m-1)//8), (7*m-1)//8
        inrange = lo <= q <= hi
        viol = [si for si in S if blocks(si, A, m)]
        if not inrange or viol:
            fails.append((m, sub, t, q, lo, hi, inrange, viol))
    if tot > 601: break
print(f"lcm(b_i)=m, all b_i>=28 : {tot} profiles, {len(fails)} failures\n")
for m, sub, t, q, lo, hi, inr, viol in fails[:6]:
    print(f"  m={m}  sub={sub}")
    print(f"     t={t}={float(t):.6f}  q=round(t*m)={q}   range [{lo},{hi}]  in-range={inr}")
    if viol:
        for si in viol:
            M=8*m; r=(si*(8*q+1))%M
            print(f"     violated by s_i={si}: residue {r}, dist {min(r,M-r)} < m={m}"
                  f"   b_i={m//si}   ||s_i t|| = {float(norm(si*t)):.6f}")
    print()
