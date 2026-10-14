"""Is the parity effect arithmetic resonance -- gcd(d, n) > 1 -- rather than parity as such?

Mechanism under test.  A disparity d with g = gcd(d, n) has its readings confined to a coarse
lattice (Thm 4.13's cage is the grid-instant face of this), and a coarse lattice OVER-BLOCKS:
measured earlier, d = 8 at e = 16, n = 8 blocks 8 openings where the generic count is 4.
At PRIME n no disparity resonates; at even n about half do.  If resonance is the driver, the
failure rate should split sharply by whether the set contains a resonant disparity.
"""
import math
from itertools import combinations

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

k, hi = 6, 15
card = k + 1
sets = [c for c in combinations(range(1, hi+1), card) if prim(c)]
print(f"k = {k} blockers (card {card}), {len(sets)} primitive sets of [1,{hi}]")
print(f"{'n':>3} {'par':>5} {'#resonant sets':>15} {'fail|res':>10} {'rate|res':>9} "
      f"{'fail|clean':>11} {'rate|clean':>11} {'ratio':>7}")
for n in range(7, 15):
    res_t = res_f = cl_t = cl_f = 0
    for c in sets:
        resonant = any(math.gcd(d, n) > 1 for d in c)
        bad = not works(c, n)
        if resonant:
            res_t += 1; res_f += bad
        else:
            cl_t += 1; cl_f += bad
    rr = res_f / res_t if res_t else 0
    rc = cl_f / cl_t if cl_t else 0
    ratio = (rr / rc) if rc > 0 else float('inf') if rr > 0 else 1.0
    print(f"{n:>3} {'even' if n%2==0 else 'odd':>5} {res_t:>15} {res_f:>10} {rr:>9.5f} "
          f"{cl_f:>11} {rc:>11.5f} {ratio:>7.2f}")
print()
print("ratio = (failure rate among sets containing a disparity resonant with n)")
print("        / (failure rate among sets with no such disparity)")
