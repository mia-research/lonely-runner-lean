"""UNIFIED prime theorem: at prime n, if no NON-FLANK disparity is divisible by n, the flank
hosts a lonely opening -- whether or not n divides e.

  n does not divide e : a = e*s with e*s = 1 mod n     (the earlier theorem)
  n divides e         : a = k*e + 1, d*a mod ne = e*(dk mod n) + d,
                        clear iff dk mod n not in {0, n-1}.
                        Each non-flank d forbids exactly one k (namely (n-1)*d^{-1});
                        there are n-1 choices of k and at most n-2 disparities -> PIGEONHOLE.
"""
import math
from itertools import combinations

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def clear_all(c, a, e, n):
    M = n*e
    return all(e <= (d*a) % M <= (n-1)*e for d in c)

def witness(c, n):
    """Return a working a by the unified construction, or None."""
    e = c[-1]
    if e % n:
        s = pow(e, -1, n)
        return e*s
    for k in range(1, n):
        if all((d*k) % n not in (0, n-1) for d in c[:-1]):
            return k*e + 1
    return None

print("unified construction, checked on every set with no non-flank disparity divisible by n")
print(f"{'n':>3} {'card':>5} {'range':>9} {'sets':>9} {'construction works':>19}")
for n, card, hi in ((5,4,60), (5,4,90), (7,4,40), (7,5,26), (7,6,18), (11,6,18), (13,6,18)):
    tot = ok = 0; bad = []
    for c in combinations(range(1, hi+1), card):
        if not prim(c): continue
        if any(d % n == 0 for d in c[:-1]): continue     # excluded by hypothesis
        tot += 1
        e = c[-1]
        a = witness(c, n)
        if a is not None and clear_all(c, a, e, n): ok += 1
        elif len(bad) < 3: bad.append((c, a))
    print(f"{n:>3} {card:>5} {('[1,'+str(hi)+']'):>9} {tot:>9} {ok:>19}"
          + ("" if ok == tot else f"   *** {bad} ***"))
print()
print("=== new coverage at n=5, card 4 (P1' = no NON-FLANK multiple of 5) ===")
for hi in (60, 120):
    tot = p1 = p1p = union = rem = 0
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        tot += 1; e = c[-1]
        old = all(d % 5 != 0 for d in c)              # old P1: nothing divisible by 5
        new = all(d % 5 != 0 for d in c[:-1])         # new P1': no NON-FLANK multiple
        rat = e <= 4*c[0]
        small = e <= 15
        if old: p1 += 1
        if new: p1p += 1
        if new or rat or small: union += 1
        else: rem += 1
    print(f"[1,{hi}]  sets {tot}")
    print(f"    old P1  (nothing div by 5)     : {p1:>8}  ({100*p1/tot:5.2f}%)")
    print(f"    new P1' (no non-flank multiple): {p1p:>8}  ({100*p1p/tot:5.2f}%)")
    print(f"    union P1' u ratio u small      : {union:>8}  ({100*union/tot:5.2f}%)")
    print(f"    residue                        : {rem:>8}  ({100*rem/tot:5.2f}%)")
