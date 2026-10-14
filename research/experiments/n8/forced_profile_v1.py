"""LEAD: the max-reach chain is FORCED.

To use comb s at level m=1 from reach x, need s.x in (7,9), and the new reach is 9/s.  Maximising
reach at every step drives s -> 7/x, so

        x_0 = 1,  s_j = 7/x_{j-1},  x_j = 9/s_j = (9/7) x_{j-1}

giving x_j = (9/7)^j and s_j = 7^j/9^(j-1) -- a GEOMETRIC profile with ratio 9/7, descending
7, 5.444, 4.235, 3.294, 2.562, 1.993.  Six combs, reach (9/7)^6 = 4.5172, exactly what the LP found.

So the configuration that maximises EARLY reach is essentially pinned.  Question: what does it do
LATER?  If maximising early reach forces a profile that clears early, that is an interlocking
obstruction -- the two demands fight.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
def Rdir(S, RMAX=200.0):
    c=[1.0]
    for s in S:
        k=1
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        ok=True
        for s in S:
            m=(s*(R+1e-12))%8.0
            if m<1.0 or m>7.0: ok=False; break
        if ok: return R
    return None
# the forced geometric profile, with s_7 = S just above 7
r=9/7
geo=[7.0/(r**j) for j in range(6)]          # 7, 5.444, ..., 1.993
geo=sorted(geo)
print("  the forced max-reach profile (ratio 9/7 descending from 7):")
print("    readings      : 1, " + ", ".join(f"{x:.4f}" for x in geo))
for eps in (0.0, 0.01, 0.05, 0.1, 0.3):
    S=[1.0]+geo[:-1]+[7.0+eps]
    S=[1.0]+sorted(S[1:])
    R=Rdir(S)
    print(f"    S = {7.0+eps:.3f} : first clear R = {R:.6f}   band {int(R//8) if R else None}")
print()
print("  for contrast, perturbing the ratio away from 9/7:")
for ratio in (1.15, 1.20, 1.2857, 1.35, 1.45):
    g=sorted([7.0/(ratio**j) for j in range(6)])
    S=[1.0]+g[:-1]+[7.45]
    S=[1.0]+sorted(S[1:])
    R=Rdir(S)
    print(f"    ratio {ratio:.4f}: readings 1, " + ", ".join(f"{x:.3f}" for x in sorted(S[1:]))
          + f"   R = {R:.5f}")
print()
print("  and the actual R-maximiser found by search, for comparison:")
best=[1.0,2.3580,3.1372,4.1865,5.2224,5.7887,7.4379]
print("    readings 1, " + ", ".join(f"{x:.4f}" for x in best[1:]))
print(f"    ratios between consecutive: " + ", ".join(f"{best[i+1]/best[i]:.4f}" for i in range(6)))
print(f"    R = {Rdir(best):.6f}")
