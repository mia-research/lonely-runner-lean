"""Two questions.
 (1) Of the 78.06% NOT blocked by the minimum speed, what happens to them?
 (2) WHY does the minimum block the 21.94% -- what is the mechanism, in (alpha,beta)?
"""
from fractions import Fraction as F
from math import gcd
from collections import Counter
import random

def blocks(sb, k, a):
    """Does speed sb block the candidate (8k+1)/(8a)?"""
    M = 8*a; r = (sb*(8*k+1)) % M
    return min(r, M-r) < a

rng = random.Random(20260919)
tally = Counter(); tot = 0
for _ in range(8000):
    A = sorted(rng.sample(range(2, 200), 7))
    a0 = A[0]
    for a in A:
        k = 0
        while F(8*k+1, 8*a) <= F(7,8):
            if F(8*k+1, 8*a) >= F(1,8):
                tot += 1
                bymin = blocks(a0, k, a)
                byoth = any(blocks(s, k, a) for s in A if s != a0)
                tally[(bymin, byoth)] += 1
            k += 1
print(f"(1) candidate accounting, {tot:,} candidates over 8,000 unit-free speed sets\n")
lbl = {(True,True):"blocked by the min AND by others",
       (True,False):"blocked ONLY by the min",
       (False,True):"blocked by others, not the min",
       (False,False):"CLEAR -- a witness"}
for k_, v in sorted(tally.items(), key=lambda kv: -kv[1]):
    print(f"    {lbl[k_]:<34} {v:>10,}  ({100*v/tot:6.2f}%)")
m = tally[(True,True)] + tally[(True,False)]
print(f"\n    blocked by the min at all        : {m:,} ({100*m/tot:.2f}%)  -- the 21.94% figure")
print(f"    of those, the min is the ONLY blocker: {tally[(True,False)]:,} "
      f"({100*tally[(True,False)]/max(m,1):.2f}% of them)")

print(f"\n(2) mechanism: blocking depends only on the coprime parts (gcd_covariant).")
print(f"    rate of blocking as a function of beta = a/gcd(a0,a):\n")
rate = Counter(); cnt = Counter()
for _ in range(4000):
    A = sorted(rng.sample(range(2, 300), 7)); a0 = A[0]
    for a in A:
        g = gcd(a0, a); al, be = a0//g, a//g
        k = 0
        while F(8*k+1, 8*a) <= F(7,8):
            if F(8*k+1, 8*a) >= F(1,8):
                cnt[be] += 1
                if blocks(a0, k, a): rate[be] += 1
            k += 1
print(f"      {'beta':>6} {'candidates':>12} {'blocked':>9}")
for be in sorted(cnt)[:12]:
    print(f"      {be:>6} {cnt[be]:>12,} {100*rate[be]/cnt[be]:>8.2f}%")
big = sum(cnt[b] for b in cnt if b >= 20); bigb = sum(rate[b] for b in cnt if b >= 20)
print(f"      {'>=20':>6} {big:>12,} {100*bigb/max(big,1):>8.2f}%")
