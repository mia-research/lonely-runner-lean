"""162 of 1,333 |J|=3 live flanks are shadowed.  The union bound 3/4 < 1 assumed density 1/4 per
runner, true only for equidistributed f.  For rational f = p/q the orbit is q points and the density
can be much higher.  So: what are the fractional parts of the SHADOWED flanks?"""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)

def analyse(ratios, kmax=2000):
    ints = [r for r in ratios if r.denominator == 1]
    if any(int(r) % 8 == 0 for r in ints): return None
    movers = [r for r in ratios if r.denominator != 1]
    if len(movers) != 3: return None
    for k in range(0, kmax):
        ok = True
        for r in movers:
            x = k * frac(r) + r / 8
            if abs(x - F(round(float(x)))) < F(1, 8): ok = False; break
        if ok: return ('clear', k, [frac(r) for r in movers])
    return ('shadowed', None, [frac(r) for r in movers])

rng = random.Random(20260919)
sh_den = Counter(); cl_den = Counter(); sh_ex = []
for _ in range(4000):
    v = sorted(rng.sample(range(0, 200), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        for e in ds:
            if e == 0: continue
            res = analyse([F(d, abs(e)) for d in ds])
            if res is None: continue
            kind, k, fs = res
            dens = tuple(sorted(f.denominator for f in fs))
            (sh_den if kind == 'shadowed' else cl_den)[dens] += 1
            if kind == 'shadowed' and len(sh_ex) < 6: sh_ex.append((fs, dens))
print("SHADOWED |J|=3 flanks, by the denominators of the three fractional parts:")
for d, c in sh_den.most_common(10): print(f"   {d}  x{c}")
print(f"\n   total shadowed: {sum(sh_den.values()):,}")
print(f"   max denominator appearing in a shadowed flank: "
      f"{max((max(d) for d in sh_den), default=0)}")
print("\nCLEAR |J|=3 flanks, same statistic (top 8):")
for d, c in cl_den.most_common(8): print(f"   {d}  x{c}")
print(f"   max denominator appearing in a clear flank: {max((max(d) for d in cl_den), default=0)}")
print("\n  examples of shadowed fractional parts:")
for fs, d in sh_ex: print(f"     {[str(f) for f in fs]}   denominators {d}")
