"""The residue, split by WHERE the 5-multiple sits.  (The flank's own condition is vacuous:
the flank is always at exactly 1/5 at its own opening, so only NON-FLANK multiples constrain.)

  Case I   : 5 does not divide e, and no non-flank disparity is a multiple of 5
             -> the prime theorem applies only if 5 also does not divide e... it does not here,
                so Case I is empty inside the residue by construction.
  Case II  : 5 | e  (the flank itself is the multiple)
  Case III : 5 does not divide e, but some non-flank disparity is a multiple of 5
"""
import math
from itertools import combinations
from fractions import Fraction as F

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c) and e > 4*c[0] and e > 15

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

hi = 40
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
caseII = [c for c in sets if c[-1] % 5 == 0]
caseIII = [c for c in sets if c[-1] % 5 != 0]
# Case III splits again: is the non-flank multiple alone?
print(f"residue sets in [1,{hi}]: {len(sets)}")
print(f"   Case II  (5 | e, flank is the multiple)      : {len(caseII):>6}  ({100*len(caseII)/len(sets):5.2f}%)")
print(f"   Case III (5 does not divide e, inner multiple): {len(caseIII):>6}  ({100*len(caseIII)/len(sets):5.2f}%)")
print()
for name, grp in (("Case II", caseII), ("Case III", caseIII)):
    mn = min(n_open(c) for c in grp)
    tight = [c for c in grp if n_open(c) <= 1]
    print(f"{name}: min working openings {mn}   tight sets {len(tight)}"
          + (f"   max elt among tight {max(max(c) for c in tight)}" if tight else ""))
print()
print("=== Case II: is there a rule?  e = 5M, so look at a mod M as well as a mod e ===")
print(f"{'set':>20} {'e':>4} {'M':>4} {'working a (a mod e, a mod M)':>52}")
for c in caseII[:10]:
    e = c[-1]; M = e // 5; Mod = 5*e
    ws = [5*j+1 for j in range(e) if all(e <= (d*(5*j+1)) % Mod <= 4*e for d in c)]
    s = ", ".join(f"{a}({a%e},{a%M})" for a in ws[:4])
    print(f"{str(c):>20} {e:>4} {M:>4}   {s}")
