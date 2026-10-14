"""Is there a threshold T with: s_max > T  =>  W(S, s_max) nonempty?

If so, Branch B splits into a rule (s_max > T) plus a FINITE check (s_max <= T).
Find the largest s_max admitting a failure.  Exhaustive where feasible, heavy sampling above.
"""
from itertools import combinations
import random

def Wsize(S, s):
    M, c = 8*s, 0
    A = s + ((1 - s) % 8)
    while A <= 7*s:
        if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S): c += 1
        A += 8
    return c

print("EXHAUSTIVE by s_max  (profile = {1} + 5 readings below s_max + s_max)")
print(f"{'s_max':>6} {'profiles':>12} {'failures':>10} {'min|W|':>7}  worst profile")
last_fail = None
for M in range(8, 41):
    tot = fails = 0; mn = 10**9; worst = None
    for combo in combinations(range(2, M), 5):
        S = (1,) + combo + (M,)
        if not any(x % 8 == 0 for x in S[1:]): continue
        tot += 1
        w = Wsize(S, M)
        if w < mn: mn, worst = w, S
        if w == 0: fails += 1
    if tot == 0: continue
    if fails: last_fail = M
    print(f"{M:>6} {tot:>12,} {fails:>10,} {mn:>7}  {worst if fails else ''}")
print(f"\nlargest s_max admitting a failure, exhaustive to 40: {last_fail}")

print("\nSAMPLED above 40 (300k profiles per s_max, readings drawn from [2, s_max))")
rng = random.Random(20260919)
for M in [41, 48, 56, 64, 80, 100, 128, 200, 512, 2048]:
    fails = 0; mn = 10**9; N = 300000
    for _ in range(N):
        combo = tuple(sorted(rng.sample(range(2, M), 5)))
        S = (1,) + combo + (M,)
        if not any(x % 8 == 0 for x in S[1:]): continue
        w = Wsize(S, M)
        if w < mn: mn = w
        if w == 0: fails += 1
    print(f"{M:>6} {N:>12,} {fails:>10,} {mn:>7}")
