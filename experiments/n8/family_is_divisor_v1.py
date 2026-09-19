"""COMPOSITION: gcd_covariant + divisor_reduces say the family of s_i is ALWAYS a divisor system.

blocks(s_j, A, s_i)  <->  blocks(a_j, A, b_j)   with  g=gcd(s_j,s_i), a_j=s_j/g, b_j=s_i/g.
And b_j | s_i BY CONSTRUCTION.  So the constraints on the s_i-family live at moduli dividing s_i --
which is exactly the divisor-closed setting, for an ARBITRARY profile.

If so, the whole divisor-closed apparatus applies per-family, universally, not as a special case.
"""
from itertools import combinations
from math import gcd
from collections import Counter

def blocks(sj, A, si):
    M = 8*si; r = (sj*A) % M
    return min(r, M-r) < si
def blocks_red(a, A, b):
    M = 8*b; r = (a*A) % M
    return min(r, M-r) < b

bad_div = 0; bad_equiv = 0; tot = 0
distinct = Counter()
for combo in combinations(range(2, 22), 6):
    S = (1,) + combo
    for si in S:
        mods = set()
        A = si + ((1-si) % 8)
        while A <= 7*si:
            for sj in S:
                if sj == si: continue
                g = gcd(sj, si); a, b = sj//g, si//g
                tot += 1
                if si % b != 0: bad_div += 1                    # b must divide s_i
                if blocks(sj, A, si) != blocks_red(a, A, b): bad_equiv += 1
                mods.add(b)
            A += 8
        distinct[len(mods)] += 1
print(f"checks: {tot:,}")
print(f"  b_j fails to divide s_i           : {bad_div}")
print(f"  reduced blocking differs from full: {bad_equiv}")
print(f"\n  => every candidate family is a DIVISOR SYSTEM at moduli dividing s_i,")
print(f"     for an arbitrary profile -- not only for divisor-closed profiles.")
print(f"\n  distinct reduced moduli per family: {dict(sorted(distinct.items()))}")
