"""Largest-flank failure RATE vs range, per order. (Corrects section 4 of
largestflank_audit_v1.py, which reused the n=6 threshold on 7-element sets.)

The n=8 record measured flank RANK on 35,872 sets drawn from [1,20], [1,30], [1,45], [1,70]
plus primitive APs: rank 1 in 35,785 of them, i.e. the largest flank worked 99.76% of the time.
An exhaustive sweep of a SMALL range is a different population, so the rates should be compared
at matched ranges, not across them.
"""
import math, random
from fractions import Fraction as F
from itertools import combinations

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
    def fo(e, j): return (F(j) + INV)/e
    return lonely, fo

def rate_exhaustive(N, hi):
    lonely, fo = mk(N); k = N - 1
    cnt = bad = 0
    for c in combinations(range(1, hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]; e = F(max(c))
        if not any(lonely(ds, fo(e, j)) for j in range(int(e))): bad += 1
    return cnt, bad

def rate_sampled(N, hi, draws):
    lonely, fo = mk(N); k = N - 1
    cnt = bad = 0
    for _ in range(draws):
        c = tuple(sorted(random.sample(range(1, hi+1), k)))
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]; e = F(max(c))
        if not any(lonely(ds, fo(e, j)) for j in range(int(e))): bad += 1
    return cnt, bad

print("=== exhaustive, per order (each uses its OWN threshold 1/n) ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'fail':>7} {'rate':>9}")
for N, hi in [(5,16),(5,20),(5,30),(6,16),(6,20),(6,26),(7,16),(7,20),(8,14),(8,16),(8,18),(8,20)]:
    cnt, bad = rate_exhaustive(N, hi)
    print(f"{N:>3} {('[1,'+str(hi)+']'):>9} {cnt:>9} {bad:>7} {100*bad/cnt:>8.3f}%")

random.seed(8)
print()
print("=== n=8 at the RANGES THE RECORD USED (record: largest flank worked 99.76%) ===")
for hi in [20, 30, 45, 70]:
    cnt, bad = rate_sampled(8, hi, 60000)
    print(f"   [1,{hi}]  sets {cnt:>6}  failures {bad:>5}  largest flank works {100*(1-bad/cnt):.3f}%")
tot_c = tot_b = 0
for hi in [20, 30, 45, 70]:
    c, b = rate_sampled(8, hi, 60000); tot_c += c; tot_b += b
print(f"   pooled over the four ranges: works {100*(1-tot_b/tot_c):.3f}%   (record 99.76%)")
