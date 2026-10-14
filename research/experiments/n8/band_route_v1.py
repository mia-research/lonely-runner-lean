"""Refined route.  Order 7 (speeds {1,s_i}) bought the range condition but cost margin, giving
b >= 28.  Get the range from PERIODICITY instead and use order 6 (5 speeds, threshold 1/6):
margin 1/6 - 1/8 = 1/24, so rounding survives iff b_i >= 12.

Period of the constraints = lcm(b_i), which divides m.  Range length is 3m/4.  A divisor of m
exceeding m/2 must be m itself, so lcm(b_i) != m  =>  lcm <= m/2 < 3m/4  =>  a full period fits.
"""
from fractions import Fraction as F
from math import lcm, gcd
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

def try_route(S, m, sub, thr, use_one):
    """Round the LRC witness, then shift by the period into the admissible range."""
    speeds = ([1] if use_one else []) + list(sub)
    t = find_t(speeds, thr, 8*m)
    if t is None: return "no_t"
    q = round(t * m)
    P = lcm(*[m//s for s in sub])
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    for k in range(-(m//max(P,1)) - 2, m//max(P,1) + 3):
        qq = q + k*P
        if lo <= qq <= hi:
            A = 8*qq + 1
            if not any(blocks(si, A, m) for si in S): return "ok"
    return "fail"

rng = random.Random(20260919)
print(f"{'arm':<48} {'profiles':>8} {'fail':>6} {'no_t':>6}")
for lo_b, thr, use_one, lcm_ne_m, label in (
    (12, F(1,6), False, True,  "order 6, b_i >= 12, lcm(b_i) != m  (derived)"),
    (12, F(1,6), False, False, "order 6, b_i >= 12, lcm(b_i) = m   (the hard case)"),
    ( 8, F(1,6), False, True,  "order 6, b_i >= 8,  lcm(b_i) != m  (below threshold)"),
):
    tot = fail = not_ = 0
    for m in range(8, 2500):
        ds = [d for d in range(2, m) if m % d == 0 and m//d >= lo_b]
        if len(ds) < 5: continue
        for _ in range(4):
            sub = tuple(sorted(rng.sample(ds, 5)))
            bs = [m//s for s in sub]
            if (lcm(*bs) != m) != lcm_ne_m: continue
            S = tuple(sorted({1, m} | set(sub)))
            if len(S) != 7: continue
            tot += 1
            r = try_route(S, m, sub, thr, use_one)
            if r == "fail": fail += 1
            elif r == "no_t": not_ += 1
        if tot > 700: break
    print(f"  {label:<46} {tot:>8} {fail:>6} {not_:>6}")
