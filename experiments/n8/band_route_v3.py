"""v2 conflated 'my grid missed the witness' with 'the route failed'.  Use our own
witness_normalised to enumerate the order-7 / order-6 witnesses exactly, not a grid."""
from fractions import Fraction as F
from math import lcm
import random

def norm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)

def witnesses(speeds, n):
    """All t = A/(n*s), A = 1 mod n, s in speeds -- the normalised candidate set at order n."""
    out = []
    for s in set(speeds):
        A = s + ((1-s) % n)
        while A <= (n-1)*s:
            t = F(A, n*s)
            if all(norm(sp*t) >= F(1,n) for sp in speeds): out.append(t)
            A += n
    return out

def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

def route(S, m, sub, use_one):
    n = 7 if use_one else 6
    speeds = ([1] if use_one else []) + list(sub)
    ws = witnesses(speeds, n)
    if not ws: return "no_t"
    P = lcm(*[m//s for s in sub])
    lo, hi = -(-(m-1)//8), (7*m-1)//8
    for t in ws:
        q0 = round(t*m)
        for k in range(-(m//max(P,1))-2, m//max(P,1)+3):
            q = q0 + k*P
            if lo <= q <= hi and not any(blocks(si, 8*q+1, m) for si in S): return "ok"
    return "fail"

rng = random.Random(20260919)
def sweep(lo_b, eq, use_one, cap=500):
    tot = fail = no_t = 0
    for m in range(8, 2000):
        ds = [d for d in range(2, m) if m % d == 0 and m//d >= lo_b]
        if len(ds) < 5: continue
        for _ in range(4):
            sub = tuple(sorted(rng.sample(ds, 5)))
            if (lcm(*[m//s for s in sub]) == m) != eq: continue
            S = tuple(sorted({1, m} | set(sub)))
            if len(S) != 7: continue
            tot += 1
            r = route(S, m, sub, use_one)
            if r == "fail": fail += 1
            elif r == "no_t": no_t += 1
        if tot > cap: break
    return tot, fail, no_t

print("HALF 1  lcm(b_i) != m  -- order 6 witnesses + period shift")
for b in (2, 4, 8, 12):
    t,f,nt = sweep(b, False, False)
    print(f"   b_i >= {b:<3} {t:>5} profiles   FAIL {f:>4}   no-witness {nt:>4}")
print("\nHALF 2  lcm(b_i) = m   -- order 7 witnesses (speed 1 supplies the range)")
for b in (8, 12, 20, 28):
    t,f,nt = sweep(b, True, True)
    print(f"   b_i >= {b:<3} {t:>5} profiles   FAIL {f:>4}   no-witness {nt:>4}")
