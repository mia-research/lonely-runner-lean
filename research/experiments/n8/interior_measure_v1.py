"""Apply the loop to the open case: measure the INTERIOR witnesses exactly.

For each divisor-closed profile where the extremal supply is exhausted, take every witness q and
record, for each modulus b, where q mod b sits inside I(b) = [L,U] -- normalised to [0,1].
Extremal witnesses sit at a named endpoint; interior ones sit somewhere.  Where?
"""
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def sols(m, bs):
    c = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return [q for q in range(m) if all(lo <= q % b <= hi for b,lo,hi in c)]
def extremal_exists(m, bs):
    if m % 8 == 0:
        for u in (1,3,5,7):
            q = u*m//8
            if all(I(b)[0] <= q % b <= I(b)[1] for b in bs+[m]): return True
    for b in bs:
        if b % 8: continue
        k = 0
        while b*(8*k+1)//8 < m:
            q = b*(8*k+1)//8
            if all(I(bb)[0] <= q % bb <= I(bb)[1] for bb in bs+[m]): return True
            k += 1
    return False

pos = Counter(); tot = 0; prof = 0
mid_hits = 0; mid_tot = 0
for m in range(24, 200):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c)
        if extremal_exists(m, bs): continue      # only the interior-only profiles
        S = sols(m, bs)
        if not S: continue
        prof += 1
        for q in S:
            tot += 1
            for b in bs + [m]:
                L, U = I(b)
                r = q % b
                if U > L:
                    x = F(r - L, U - L)          # normalised position in the interval
                    pos[min(int(x*10), 9)] += 1
                    if F(3,10) <= x <= F(7,10): mid_hits += 1
                    mid_tot += 1
print(f"interior-only profiles: {prof:,}   witnesses: {tot:,}   (residue samples {mid_tot:,})\n")
print("  normalised position of q mod b inside I(b), by decile:")
s = sum(pos.values())
for d in range(10):
    bar = "#" * int(60*pos[d]/s)
    print(f"    [{d/10:.1f},{(d+1)/10:.1f})  {100*pos[d]/s:5.2f}%  {bar}")
print(f"\n  fraction in the middle 40% of the interval: {100*mid_hits/mid_tot:.2f}%"
      f"   (uniform would be 40.00%)")
