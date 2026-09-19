"""Random sampling cannot reach band 1 (the manuscript says so, and it did not).
Hill-climb on the DISPARITIES to maximise R, per order, with exact endpoint computation."""
from fractions import Fraction as F
import random

def clear(S, x, n):
    for s in S:
        y = s*x
        if abs(y - n*round(y/n)) < 1: return False
    return True
def R_exact(S, n, hi):
    c = {F(1)}
    for s in S:
        k = 0
        while F(n*k+1,1)/s <= hi:
            for num in (n*k+1, n*k-1):
                if num > 0:
                    x = F(num,1)/s
                    if 1 <= x <= hi: c.add(x)
            k += 1
    for x in sorted(c):
        if clear(S, x, n): return x
    return None
def R_of(d, n, hi):
    S = [F(x, d[0]) for x in d]
    if len(set(S)) != len(d) or min(S) != 1: return None
    return R_exact(S, n, hi)

rng = random.Random(20260919)
print(f"{'n':>3} {'best R':>11} {'R/n':>7} {'laps':>5} {'2n':>4}   best disparities")
for n in range(5, 10):
    k = n - 1; hi = F(4*n)
    best = (F(0), None)
    for restart in range(140):
        d = sorted(rng.sample(range(1, 2000), k))
        cur = R_of(d, n, hi)
        if cur is None: continue
        for _ in range(700):
            e = list(d); i = rng.randrange(1, k)
            e[i] += rng.choice([-7,-5,-3,-2,-1,1,2,3,5,7])
            e = sorted(set(e))
            if len(e) != k or e[0] != d[0] or e[0] < 1: continue
            v = R_of(e, n, hi)
            if v is not None and v > cur: d, cur = e, v
        if cur > best[0]: best = (cur, list(d))
    R, d = best
    print(f"{n:>3} {float(R):>11.4f} {float(R)/n:>7.4f} {int(R//n):>5} {2*n:>4}   {d}")
