"""The split is lcm(b_i) = m or not.  Map each half to its own route and find the real thresholds."""
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

def route(S, m, sub, use_one):
    speeds = ([1] if use_one else []) + list(sub)
    thr = F(1,7) if use_one else F(1,6)
    t = find_t(speeds, thr, 8*m)
    if t is None: return "no_t"
    q = round(t*m); P = lcm(*[m//s for s in sub])
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    for k in range(-(m//max(P,1))-2, m//max(P,1)+3):
        qq = q + k*P
        if lo <= qq <= hi and not any(blocks(si, 8*qq+1, m) for si in S): return "ok"
    return "fail"

rng = random.Random(20260919)
def sweep(lo_b, want_lcm_eq_m, use_one, cap=600):
    tot = fail = 0
    for m in range(8, 2500):
        ds = [d for d in range(2, m) if m % d == 0 and m//d >= lo_b]
        if len(ds) < 5: continue
        for _ in range(4):
            sub = tuple(sorted(rng.sample(ds, 5)))
            bs = [m//s for s in sub]
            if (lcm(*bs) == m) != want_lcm_eq_m: continue
            S = tuple(sorted({1, m} | set(sub)))
            if len(S) != 7: continue
            tot += 1
            if route(S, m, sub, use_one) != "ok": fail += 1
        if tot > cap: break
    return tot, fail

print("HALF 1  lcm(b_i) != m   -- order 6 (thr 1/6) + shift by the period")
for b in (2, 3, 4, 6, 8, 12):
    t, f = sweep(b, False, False)
    print(f"   all b_i >= {b:<3}  {t:>5} profiles   fail {f:>4}")
print("\nHALF 2  lcm(b_i) = m    -- order 7 (thr 1/7, speed 1 supplies the range)")
for b in (8, 12, 16, 20, 24, 28):
    t, f = sweep(b, True, True)
    print(f"   all b_i >= {b:<3}  {t:>5} profiles   fail {f:>4}")
