"""The n=5 sets with exactly ONE working opening at the largest flank (fast: early exit at 2)."""
import math, sys, time
from itertools import combinations

def tight_or_fail(c, n=5):
    """Return (count_capped_at_2, first_working_j)."""
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    cnt = 0; first = -1
    for j in range(e):
        a = n*j + 1
        ok = True
        for d in c:
            if not (lo <= (d*a) % M <= hi): ok = False; break
        if ok:
            cnt += 1
            if first < 0: first = j
            if cnt >= 2: return 2, first
    return cnt, first

HI = int(sys.argv[1])
t0 = time.time(); tight = []; zero = []
for c in combinations(range(1, HI+1), 4):
    if math.gcd(math.gcd(c[0],c[1]), math.gcd(c[2],c[3])) != 1: continue
    cnt, j = tight_or_fail(c)
    if cnt == 0: zero.append(c)
    elif cnt == 1: tight.append((c, j))
print(f"[1,{HI}]  ({time.time()-t0:.1f}s)   FAILURES(0 openings): {len(zero)}   TIGHT(exactly 1): {len(tight)}")
if zero: print(f"  failures: {zero[:10]}")
print(f"  max element among tight sets: {max(max(c) for c,_ in tight)}")
print(f"  max d_min among tight: {max(c[0] for c,_ in tight)}   max d_max among tight: {max(c[3] for c,_ in tight)}")
print()
for c, j in sorted(tight):
    print(f"   {str(c):>20}  j={j:<3}  ratios {tuple(round(x/c[3],3) for x in c)}")
