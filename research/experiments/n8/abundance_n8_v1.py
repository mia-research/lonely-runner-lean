#!/usr/bin/env python3
"""ABUNDANCE structure at n=8: BSM in PARAMETER space (first AND last a), plus the widths.

Units of 1/56.  Slot I_s = [8s+1, 8s+7], width 6.  Runner j: bad intervals
B_{j,k} = [7(8k+7)/a, 7(8k+9)/a], so
    interval WIDTH  = 14/a_j        PERIOD = 56/a_j
Sign range a_j in (j-1, j+1), so a_j < 7 always.

LEMMA 1 (one interval per slot).  A slot is narrower than any runner's period, and two of a
runner's intervals meet one slot only if PERIOD <= slotwidth + width, i.e. 56/a <= 6 + 14/a,
i.e. a >= 7.  Excluded.  So EACH RUNNER CONTRIBUTES AT MOST ONE INTERVAL TO EACH SLOT.

LEMMA 2 (width budget).  Hence slot I_s is covered only if the runners touching it satisfy
    sum over touching j of 14/a_j  >=  6,   i.e.   sum of 1/a_j  >=  3/7.
This is a HARD per-slot constraint and it is where abundance bites: a runner cannot blanket
a slot unless it is wide, and width falls off as 1/a_j.
Exact Fraction only.
"""
from fractions import Fraction as F
from itertools import combinations

R = list(range(2, 7))
def rng(j): return (F(j-1), F(j+1))
SLOTW, NEED = F(6), F(3, 7)

print("LEMMA 1 check: period vs slot width + interval width, at the worst a_j = j+1")
for j in R:
    a = F(j+1)
    print(f"  runner {j}, a={a}: period {F(56)/a} > slotwidth+width {SLOTW + F(14)/a}"
          f"  -> {F(56)/a > SLOTW + F(14)/a}")
print()
print("Interval WIDTH 14/a_j over each sign range (slot width = 6):")
for j in R:
    lo, hi = rng(j)
    print(f"  runner {j}: a in ({lo},{hi})  width in ({F(14)/hi}, {F(14)/lo})"
          f" = ({float(F(14)/hi):.3f}, {float(F(14)/lo):.3f})"
          + ("   CAN blanket a whole slot" if F(14)/lo > SLOTW else "   too narrow alone"))
print()
print("LEMMA 2: which subsets can EVER supply width 6 to one slot (sum 1/a_j >= 3/7)?")
never = []
for r in range(1, 6):
    for S in combinations(R, r):
        best = sum(F(1, j-1) for j in S)        # maximised as each a_j -> j-1
        ok = best >= NEED
        if not ok: never.append(S)
        if r <= 2:
            print(f"  {list(S)}: max sum 1/a_j = {best} = {float(best):.4f}"
                  f"  {'CAN' if ok else 'CANNOT'} reach 3/7 = {float(NEED):.4f}")
print()
print(f"  subsets that can NEVER cover a slot: {[list(s) for s in never]}")
print()
print("So every slot must be touched by runner 2, or runner 3, or two or more of {4,5,6};")
print("and {5,6} only in the extreme corner a_5 -> 4, a_6 -> 5.")
