"""The bulk (non-integer readings) is NOT unproved: TwoWalker covers <=1 and 2 non-integer ratios.
So sub-partition the bulk by the NUMBER of non-integer ratios -- that locates the real frontier."""
from math import gcd
from functools import reduce
from collections import Counter
import random
rng = random.Random(20260919)
print(f"{'range':<12} {'sets':>8}  distribution of # non-integer readings (d_i/d_min not an integer)")
for N in (100, 400, 2000, 20000):
    c = Counter(); tot = 0
    for _ in range(120000):
        A = sorted(rng.sample(range(1, N), 7))
        g = reduce(gcd, A); red = [x//g for x in A]
        dmin = min(red); tot += 1
        k = sum(1 for x in red if x % dmin != 0)
        c[k] += 1
    row = "  ".join(f"{k}:{100*c[k]/tot:5.2f}%" for k in sorted(c))
    print(f"[1,{N}){'':<5} {tot:>8,}  {row}")
print()
print("  0 non-integer      = integer readings   -> Branch A proved / Branch B open")
print("  1 or 2 non-integer = TwoWalker           -> PROVED (Thm 6.9, 6.18)")
print("  3+ non-integer     = THE FRONTIER        -> open")
tot=0; front=0
for _ in range(200000):
    A = sorted(rng.sample(range(1, 20000), 7))
    g = reduce(gcd, A); red=[x//g for x in A]; dmin=min(red); tot+=1
    if sum(1 for x in red if x % dmin != 0) >= 3: front += 1
print(f"\n  share of instances in the OPEN frontier, speeds < 20000: {100*front/tot:.2f}%")
