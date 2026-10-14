"""n=5 residue: look for a PATTERN in the working openings.

Residue = some disparity divisible by 5, d_max > 4 d_min, d_max > 15.

Algebra to test against.  Write a = 5j+1 (so a = 1 mod 5, 1 <= a < 5e).
  * a NON-multiple d is clear iff   d*a mod 5e  in [e, 4e]
  * a MULTIPLE d = 5m  is clear iff m*a mod e  in [e/5, 4e/5]      (the 5 cancels)
The prime theorem picks a = e*s with e*s = 1 mod 5; then every non-multiple is clear
(residue e*(ds mod 5)) and every multiple sits at residue 0 -- blocked.
So: where do the working a actually sit, relative to e?
"""
import math
from itertools import combinations

def working_as(c, n=5):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    out = []
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): out.append(a)
    return out, e

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c) and e > 4*c[0] and e > 15

hi = 40
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
print(f"residue sets in [1,{hi}]: {len(sets)}\n")
print("sample, with the working a's and their residues mod e:")
print(f"{'set':>22} {'e':>4} {'#5-mult':>8} {'working a (a mod e)':>46}")
for c in sets[:18]:
    ws, e = working_as(c)
    n5 = sum(1 for d in c if d % 5 == 0)
    s = ", ".join(f"{a}({a%e})" for a in ws[:5])
    print(f"{str(c):>22} {e:>4} {n5:>8}   {s}")
print()
# Is a mod e ever 0 in the residue?  (the prime theorem's choice) -- should be never
zero_mod_e = 0; tot_w = 0
for c in sets:
    ws, e = working_as(c)
    for a in ws:
        tot_w += 1
        if a % e == 0: zero_mod_e += 1
print(f"working openings with a = 0 mod e : {zero_mod_e} of {tot_w}"
      f"   (the prime theorem's a; expected 0 in the residue)")
