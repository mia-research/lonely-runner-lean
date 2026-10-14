"""Corrected: a = (e*s + 5u) mod 5e covers EVERY admissible a, so the question is not
'does some u work' (it must) but 'is the smallest working u BOUNDED'.

If u is bounded by a constant U, the residue reduces to a finite check over u in [0,U].
Also: the e = 4 mod 5 family that failed the truncated search -- is it special?
"""
import math
from itertools import combinations
from collections import Counter

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def clear_all(c, a, e):
    M = 5*e
    return all(e <= (d*a) % M <= 4*e for d in c)

def smallest_u(c):
    e = c[-1]; s = pow(e, -1, 5); M = 5*e
    for u in range(e):
        if clear_all(c, (e*s + 5*u) % M, e): return u
    return None

for hi in (30, 40, 50):
    sets = []
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        e = c[-1]
        if e % 5 == 0 or sum(1 for d in c[:-1] if d % 5 == 0) != 1: continue
        if e <= 4*c[0] or e <= 15: continue
        sets.append(c)
    us = [smallest_u(c) for c in sets]
    bad = [c for c, u in zip(sets, us) if u is None]
    mx = max(u for u in us if u is not None)
    worst = [c for c, u in zip(sets, us) if u == mx]
    print(f"[1,{hi}]  dominant-case sets {len(sets):>6}   no working u: {len(bad)}"
          f"   max smallest-u = {mx}   at {worst[:2]}")
print()
print("=== the e = 4 mod 5 family: is its smallest u larger? ===")
hi = 50
byres = {}
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]
    if e % 5 == 0 or sum(1 for d in c[:-1] if d % 5 == 0) != 1: continue
    if e <= 4*c[0] or e <= 15: continue
    u = smallest_u(c)
    r = e % 5
    t, s_, m_ = byres.get(r, (0, 0, 0))
    byres[r] = (t+1, s_+u, max(m_, u))
print(f"{'e mod 5':>8} {'sets':>7} {'mean u':>8} {'max u':>7}")
for r in sorted(byres):
    t, s_, m_ = byres[r]
    print(f"{r:>8} {t:>7} {s_/t:>8.2f} {m_:>7}")
