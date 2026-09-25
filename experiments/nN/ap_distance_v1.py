"""How far from an AP are the sets we called "not deformations of the AP"?  Measured, not asserted.

Scale-invariant distance to the AP: rho(S) = min over k > 0 of max_i |d_(i)/(k*i) - 1|, d_(i) sorted.
(The min over k is attained where the largest and smallest ratio d_(i)/i balance:
k = 2 / (1/max_r + 1/min_r) in the relative metric; computed exactly with fractions.)
Compared: the 22 scale-free residual members (residual_members_v4), the constructed near-AP
deformations (|e_i| <= k/100, k/10), and the AP-local radius 1/85 of ap_local_v1.
"""
from fractions import Fraction as F
exec(open('residual_members_v4.py').read().split("# where do the scale-free members clear?")[0])
def rho(S):
    r = [F(d, i + 1) for i, d in enumerate(sorted(S))]
    lo, hi = min(r), max(r)
    k = 2 / (1 / lo + 1 / hi)          # balances |lo/k - 1| and |hi/k - 1|
    return max(abs(x / k - 1) for x in r)
vals = sorted(rho(S) for S in found)
print(f"22 scale-free residual members: rho min {float(vals[0]):.3f}, median {float(vals[len(vals)//2]):.3f}, max {float(vals[-1]):.3f}")
rnd2 = random.Random(39)
for k, E in ((10000, 100), (10000, 1000)):
    v = sorted(rho(tuple(sorted(k * (i + 1) + rnd2.randrange(-E, E + 1) for i in range(7)))) for _ in range(200))
    print(f"AP deformations k={k}, |e|<={E}: rho max {float(v[-1]):.4f}")
print(f"AP-local radius (ap_local_v1, proved): relative deviation < 1/85 = {1/85:.4f}")
