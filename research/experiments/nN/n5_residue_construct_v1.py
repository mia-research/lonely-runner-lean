"""A perturbed construction for the residue's dominant case.

Case: exactly one non-flank multiple 5m; flank e with 5 not dividing e.
Take a = e*s + t with e*s = 1 mod 5 (so t = 0 mod 5, write t = 5u).
  * the multiple:  m*a mod e = m*t mod e   -- controlled entirely by t
  * a non-multiple d: d*a mod 5e = e*q_d + d*t  (when d*t < e and no wrap), q_d = d*s mod 5
    so it needs q_d in {1,2,3} and d*t small enough.
Note q_d = d * e^{-1} mod 5, so 'q_d != 4' is the same residue-miss condition as Case II.

Tested: does some t = 5u with 0 <= u < e clear everything?  And is the SMALLEST such t small?
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

hi = 40
sets = []
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]
    if e % 5 == 0: continue
    if sum(1 for d in c[:-1] if d % 5 == 0) != 1: continue
    if e <= 4*c[0] or e <= 15: continue
    sets.append(c)
print(f"dominant residue case (one inner 5-multiple, 5 does not divide e) in [1,{hi}]: {len(sets)}\n")

works = 0; qd_ok = 0; udist = Counter(); fails = []
for c in sets:
    e = c[-1]
    s = pow(e, -1, 5)
    # q_d for the non-multiples
    qs = [(d * s) % 5 for d in c[:-1] if d % 5]
    if all(q in (1,2,3) for q in qs): qd_ok += 1
    found = None
    for u in range(e):
        a = e*s + 5*u
        if a >= 5*e: break
        if clear_all(c, a, e): found = u; break
    if found is not None:
        works += 1; udist[min(found, 9)] += 1
    elif len(fails) < 5: fails.append(c)
print(f"   some a = e*s + 5u (u < e) clears everything : {works} / {len(sets)}")
print(f"   sets where every q_d is in {{1,2,3}}          : {qd_ok} / {len(sets)}")
print(f"   smallest working u (9 = 9 or more)          : {dict(sorted(udist.items()))}")
if fails: print(f"   failures: {fails}")
