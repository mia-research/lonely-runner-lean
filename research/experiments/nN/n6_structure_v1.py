"""n=6: (a) is the rank-2 family infinite?  (b) is the TIGHT family bounded?

(a) matters for how a proof is shaped; (b) matters for whether a proof is shaped at all.
The n=5 proof shape needs the set of BARELY-working cases to be finite and bounded.
"""
import math, sys, time
from itertools import combinations

def works_at(c, e, n=6):
    M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): return True
    return False

def count_top2(c, n=6):
    cnt = 0
    for e in sorted(set(c), reverse=True)[:2]:
        M = n*e; lo, hi = e, (n-1)*e
        for j in range(e):
            a = n*j + 1
            if all(lo <= (d*a) % M <= hi for d in c):
                cnt += 1
                if cnt >= 2: return 2
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

print("=== (a) the family (3, 3m, 3m+3, 3m+6, b): does the largest flank keep failing? ===")
hits = []
for m in range(2, 60):
    base = (3, 3*m, 3*m+3, 3*m+6)
    for b in range(3*m+7, 3*m+60):
        c = base + (b,)
        if not prim(c): continue
        if not works_at(c, b):
            hits.append(c)
            break
print(f"   rank-2 members found for m = 2..59: {len(hits)}")
print(f"   examples: {hits[:8]}")
print(f"   largest member: {hits[-1] if hits else '-'}")
print(f"   -> the rank-2 family is {'UNBOUNDED (grows without limit)' if len(hits) > 20 else 'not obviously unbounded'}")
print()

print("=== (b) the TIGHT family (<=1 working opening across the two largest flanks) ===")
for HI in (int(x) for x in sys.argv[1:]):
    t0 = time.time()
    tight = [c for c in combinations(range(1, HI+1), 5) if prim(c) and count_top2(c) <= 1]
    zero  = [c for c in tight if count_top2(c) == 0]
    print(f"   [1,{HI}]  tight {len(tight):>4}   with ZERO openings {len(zero)}   "
          f"max element {max(max(c) for c in tight) if tight else '-'}   ({time.time()-t0:.1f}s)")
    if zero: print(f"       ZERO-opening witnesses (would refute the candidate): {zero[:5]}")
