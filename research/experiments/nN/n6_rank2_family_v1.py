"""n=6: is the set of difference sets NEEDING the second-largest flank finite and bounded?

If the largest flank works except on a bounded explicit list, the n=6 proof splits exactly as
n=5's does: a finite check on the list, and a margin argument above it.
"""
import math, sys, time
from itertools import combinations

def works_at(c, e, n):
    M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        ok = True
        for d in c:
            if not (lo <= (d*a) % M <= hi): ok = False; break
        if ok: return True
    return False

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

n, k = 6, 5
for HI in (int(x) for x in sys.argv[1:]):
    t0 = time.time()
    tot = 0; rank2 = []; rank3plus = []
    for c in combinations(range(1, HI+1), k):
        if not prim(c): continue
        tot += 1
        if works_at(c, c[-1], n): continue
        rank2.append(c)
        if not works_at(c, c[-2], n): rank3plus.append(c)
    print(f"[1,{HI}]  {tot:>9} sets  ({time.time()-t0:.1f}s)")
    print(f"   need rank 2 (largest fails): {len(rank2):>4}   max element {max(max(c) for c in rank2) if rank2 else '-'}")
    print(f"   need rank 3+ (two largest both fail): {len(rank3plus)}")
    if rank3plus: print(f"      WITNESSES: {rank3plus[:10]}")
    print()
print("=== the rank-2 family in full (largest flank fails, second works) ===")
HI = int(sys.argv[-1])
fam = [c for c in combinations(range(1, HI+1), k) if prim(c) and not works_at(c, c[-1], n)]
for c in fam: print(f"   {c}")
print(f"total {len(fam)}; all have d_max <= {max(c[-1] for c in fam)}, d_min <= {max(c[0] for c in fam)}")
