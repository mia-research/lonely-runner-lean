"""For |J| = 3 flanks the union bound gives 3*(1/4) = 3/4 < 1, so clear openings are ABUNDANT.
Prop 6.11 was withdrawn for naming an opening without BOUNDING it. So the real question:

    how large is the FIRST clear opening index k on a |J| = 3 live flank?

If bounded, an index bound is attainable and the case closes natively.
"""
from fractions import Fraction as F
from collections import Counter
import random

def first_clear(ratios, kmax=4000):
    """runner j in the way at opening k iff k*f_j + rho_j/8 is within 1/8 of an integer."""
    movers = [(r - int(r) if r >= 0 else r - (r.numerator // r.denominator), r)
              for r in ratios if r.denominator != 1]
    ints = [r for r in ratios if r.denominator == 1]
    if any(int(r) % 8 == 0 for r in ints): return None      # not live
    for k in range(0, kmax):
        ok = True
        for f, r in movers:
            x = k * f + r / 8
            d = x - F(round(float(x)))
            if abs(d) < F(1, 8): ok = False; break
        if ok: return k
    return -1

rng = random.Random(20260919)
idx = Counter(); miss = 0; tot = 0; big = []
for _ in range(4000):
    v = sorted(rng.sample(range(0, 200), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        for e in ds:
            if e == 0: continue
            ae = abs(e); ratios = [F(d, ae) for d in ds]
            if sum(1 for r in ratios if r.denominator != 1) != 3: continue
            k = first_clear(ratios)
            if k is None: continue
            tot += 1
            if k == -1: miss += 1
            else:
                idx[k] += 1
                if k > 8 and len(big) < 5: big.append((v, i, e, k))
print(f"live flanks with |J| = 3 : {tot:,}")
print(f"  no clear opening below k = 4000 : {miss:,}")
ks = sorted(idx)
print(f"  first clear opening index k     : {dict((k, idx[k]) for k in ks[:12])}")
print(f"  max first-clear index observed  : {max(ks) if ks else '-'}")
if big:
    print(f"\n  flanks needing k > 8:")
    for v,i,e,k in big: print(f"     v={v} subject {i} flank e={e}  first clear k={k}")
