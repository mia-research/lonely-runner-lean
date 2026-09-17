"""The own-AP residue rule at reading denominator q.
Readings s_l = c_l/q.  h_l = gcd(c_l, 8q), m'_l = 8q/h_l, u_l = c_l/h_l.  Own-AP instant n (odd) is lonely iff for every l
the residue n*u_l mod m'_l is at least m'_l/8 from 0.  The rule's set of lonely odd n mod 8q (built from the residue classes
of each runner, no instant evaluated) is compared with direct evaluation of n*s_l against 8Z, for every odd n mod 8q."""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
def lcm(a, b): return a * b // gcd(a, b)
def dist8(x): y = x - 8 * floor(x / 8); return min(y, 8 - y)
def rule_lonely_set(C, q):
    N = 8 * q
    allowed = set(range(1, N, 2))
    for c in C:
        h = gcd(c, N); mp = N // h; u = c // h
        if mp == 1: return set()
        uinv = pow(u % mp, -1, mp) if mp > 1 else 0
        band = [rho for rho in range(-(mp // 2), mp // 2 + 1) if 8 * abs(rho) < mp]     # strictly within m'/8 of 0
        classes = {(uinv * rho) % mp for rho in band}
        allowed -= {n for n in allowed if n % mp in classes}
    return allowed
def direct_lonely_set(S, q):
    return {n for n in range(1, 8 * q, 2) if all(dist8(n * s) >= 1 for s in S)}
def job(V):
    out = []
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        S = [d / m for d in ds]
        q = reduce(lcm, [s.denominator for s in S]); C = [int(s * q) for s in S]
        R = rule_lonely_set(C, q); D = direct_lonely_set(S, q)
        out.append((q, R == D, len(D) == 0, min(D) if D else None, min(R) if R else None))
    return out
if __name__ == "__main__":
    rng = random.Random(31); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    arrs = []
    for qq in (3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 25):
        n = 0
        while n < 400:
            V = ok([AP[j] + F(rng.randint(-(45 * qq) // 100, (45 * qq) // 100), qq) for j in range(8)])
            if V: arrs.append(V); n += 1
    for _ in range(600):
        arrs.append([F(v) for v in sorted(rng.sample(range(1, 200), 8))])
    with Pool(8) as p: R = [x for r in p.map(job, arrs, chunksize=16) for x in r]
    agree = sum(1 for x in R if x[1]); none = [x for x in R if x[2]]
    print(f"runners {len(R)} | rule's lonely set = direct lonely set: {agree}")
    print(f"   no lonely own-AP instant: {len(none)}, rule agrees on those: {sum(1 for x in none if x[1])}")
    print(f"   first lonely instant from the rule = direct: {sum(1 for x in R if x[3] == x[4])}")
    print("   by reading denominator q (runners, agreements):", {q: (sum(1 for x in R if x[0] == q), sum(1 for x in R if x[0] == q and x[1])) for q in sorted({x[0] for x in R}) if q <= 30})
