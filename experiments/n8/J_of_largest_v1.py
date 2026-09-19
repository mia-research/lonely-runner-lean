"""At the largest flank e, every other ratio has 0 < |rho| < 1, hence is NON-INTEGER.
So the largest flank always has |J| = 6 -- the MAXIMUM number of movers -- and it is always clear.
If so, high |J| is not hard: the shadowed flanks should have LOW |J|.  Test both."""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)
def status(ds, e, kmax=5000):
    ae = abs(e); ratios = [F(d, ae) for d in ds]
    if any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios): return ('dead', None)
    movers = [r for r in ratios if r.denominator != 1]
    for k in range(kmax):
        ok = True
        for r in movers:
            x = k*frac(r) + r/8
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return ('clear', len(movers))
    return ('shadowed', len(movers))

rng = random.Random(20260919)
Jlargest = Counter(); Jshadow = Counter(); Jclear = Counter(); tot=0
for _ in range(4000):
    v = sorted(rng.sample(range(0, 400), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        emax = max(ds, key=abs)
        st, J = status(ds, emax)
        if J is not None: Jlargest[J] += 1
        for e in ds:
            s, J2 = status(ds, e)
            if J2 is None: continue
            tot += 1
            (Jshadow if s == 'shadowed' else Jclear)[J2] += 1
print(f"|J| at the LARGEST flank: {dict(sorted(Jlargest.items()))}")
print(f"   -> the largest flank carries the maximum number of movers\n")
print(f"live flanks: {tot:,}")
print(f"  |J| of CLEAR flanks   : {dict(sorted(Jclear.items()))}")
print(f"  |J| of SHADOWED flanks: {dict(sorted(Jshadow.items()))}")
tc = sum(Jclear.values()); ts = sum(Jshadow.values())
print(f"\n  shadow rate by |J|:")
for J in sorted(set(Jclear) | set(Jshadow)):
    a, b = Jclear[J], Jshadow[J]
    print(f"     |J| = {J}: {100*b/max(a+b,1):6.3f}%  ({b:,} of {a+b:,})")
