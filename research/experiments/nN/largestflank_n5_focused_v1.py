"""n=5 DoorLargestFlank, focused: the cases the [1,80] exhaustive sweep does NOT cover.

Exhaustive over primitive 4-subsets of [1,80] gave 0 failures (1,473,833 sets).  A subject at
order 5 can also present a COLLAPSED difference set (card 1, 2 or 3) when two runners are
equidistant in speed, and can present large / structured values.  Those are checked here.
A failure anywhere kills the candidate theorem, so this is looking for one.
"""
import math, random
from fractions import Fraction as F
from itertools import combinations

INV = F(1,5)
def circDist(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)
def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
def fo(e, j): return (F(j) + INV)/e
def largest_works(c):
    ds = [F(x) for x in c]; e = F(max(c))
    return any(lonely(ds, fo(e, j)) for j in range(int(e)))

def run(name, sets, cap=None):
    cnt, bad, ex = 0, 0, []
    for c in sets:
        c = tuple(sorted(set(int(x) for x in c)))
        if len(c) < 1 or c[0] < 1: continue
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        if not largest_works(c):
            bad += 1
            if len(ex) < 6: ex.append(c)
        if cap and cnt >= cap: break
    print(f"  {name:<46} tested {cnt:>8}   FAILURES {bad:>4}  {ex if ex else ''}")
    return bad

random.seed(555)
tot = 0
print("=== collapsed difference sets (card 1, 2, 3) -- NOT in the 4-subset sweep ===")
tot += run("all 1-subsets of [1,200]", [(a,) for a in range(1,201)])
tot += run("all 2-subsets of [1,200]", combinations(range(1,201), 2))
tot += run("all 3-subsets of [1,120]", combinations(range(1,121), 3))

print("=== structured 4-sets ===")
tot += run("primitive APs a+di, a<=80, d<=80", [(a,a+d,a+2*d,a+3*d) for a in range(1,81) for d in range(1,81)])
tot += run("geometric-ish (a, 2a+r, 4a+r, 8a+r)", [(a, 2*a+r, 4*a+r, 8*a+r) for a in range(1,200) for r in range(-3,4)])
tot += run("(1,2,3,X) X<=3000", [(1,2,3,X) for X in range(4,3001)])
tot += run("(a,a+1,a+2,a+3) a<=2000", [(a,a+1,a+2,a+3) for a in range(1,2001)])
tot += run("(1,a,a+1,2a) a<=1500", [(1,a,a+1,2*a) for a in range(2,1501)])

print("=== wide random ===")
tot += run("random 4-subsets of [1,5000], 250k", [tuple(random.sample(range(1,5001),4)) for _ in range(250000)])
tot += run("random (tiny,big,big,big), 150k", [(random.randint(1,30), *sorted(random.sample(range(500,10**6),3))) for _ in range(150000)])
tot += run("random near-equal quadruples, 150k", [tuple(sorted({random.randint(10**5,10**5+40) for _ in range(6)}))[:4] for _ in range(150000)])

print()
print(f"TOTAL n=5 LARGEST-FLANK FAILURES ACROSS ALL FAMILIES: {tot}")
