"""The right coordinate: R = n * d_min * t at the first isolation, order 8 (cap R < n-1 = 7).

The minimal OPENING INDEX is unbounded (the near-AP family needs k = m at flank 16m), but that is a
coordinate artefact: the instant there is t = (m + 1/8)/(16m), so R = 1 + 1/(8m) -> 1. This measures R
itself, the framework's own reading, across regimes.
"""
import random, math
from fractions import Fraction as F
TH = F(1, 8)
def cd(x):
    f = x % 1; return min(f, 1 - f)
def first_isolation_R(D):
    """smallest lonely instant among flank openings, returned as R = 8*d_min*t"""
    dmin = min(D); best = None
    for e in D:
        for k in range(0, 4000):
            t = (F(k) + TH) / e
            if best is not None and 8 * dmin * t >= best: break
            if all(cd(d * t) >= TH for d in D):
                R = 8 * dmin * t
                if best is None or R < best: best = R
                break
    return best
rng = random.Random(31)
print("R at the first isolation (cap for order 8 is R < 7)\n")
def report(name, gen, n):
    Rs = []
    for _ in range(n):
        D = gen()
        R = first_isolation_R(D)
        if R is None: print("   FAILURE", D); continue
        Rs.append((R, D))
    Rs.sort(key=lambda x: x[0])
    mx = Rs[-1]
    med = Rs[len(Rs)//2][0]
    print(f"  {name:<34} sets {len(Rs):<5} median R {float(med):.4f}   max R {float(mx[0]):.4f}  = {mx[0]}")
    print(f"      {'':<32} worst set {mx[1]}")
report("integer, d_max <= 30", lambda: sorted(rng.sample(range(1,31),7)), 1200)
report("integer, d_max <= 300", lambda: sorted(rng.sample(range(1,301),7)), 800)
report("integer, d_max <= 5000", lambda: sorted(rng.sample(range(1,5001),7)), 300)
print()
print("  the near-AP family in R:")
for m in [1,10,100,1000]:
    D = sorted([2,3,4,5,6,7,16*m])
    print(f"    m={m:<6} R = {first_isolation_R(D)}")
