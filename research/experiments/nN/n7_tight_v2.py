"""Order 7 tight family, pushed further -- does it stabilise like 5 and 6, or keep growing?

Fair comparison matters: at n=5 the family was measured to [1,200] and at n=6 to [1,80],
whereas the first n=7 run only reached [1,20].  Pushed here, with the max element recorded
so 'tracks the boundary' can be distinguished from 'has settled'.
"""
import math, sys, time
from itertools import combinations

def count_top2(c, n=7, cap=2):
    cnt = 0
    for e in sorted(set(c), reverse=True)[:2]:
        M = n*e; lo, hi = e, (n-1)*e
        for j in range(e):
            a = n*j + 1
            ok = True
            for d in c:
                if not (lo <= (d*a) % M <= hi): ok = False; break
            if ok:
                cnt += 1
                if cnt >= cap: return cap
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print(f"{'range':>9} {'sets':>9} {'TIGHT':>6} {'zero':>5} {'max elt':>8} {'time':>7}")
for hi in (20, 24, 28, 32):
    t0 = time.time(); tight = []; zero = 0
    for c in combinations(range(1, hi+1), 6):
        if not prim(c): continue
        w = count_top2(c)
        if w <= 1:
            tight.append(c)
            if w == 0: zero += 1
    n_sets = sum(1 for c in combinations(range(1, hi+1), 6) if prim(c))
    mx = max(max(c) for c in tight) if tight else 0
    print(f"{('[1,'+str(hi)+']'):>9} {n_sets:>9} {len(tight):>6} {zero:>5} {mx:>8} {time.time()-t0:>6.1f}s")
