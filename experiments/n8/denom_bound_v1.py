"""CLAIM: a live |J|=3 flank with some fractional part of denominator >= 5 always has a clear
opening -- and at a small index.  If so, |J|=3 reduces to a finite enumeration over denominators <=4.
Test at scale, and find the index bound."""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)

def first_clear(movers, kmax=3000):
    for k in range(0, kmax):
        ok = True
        for r in movers:
            x = k * frac(r) + r / 8
            if abs(x - F(round(float(x)))) < F(1, 8): ok = False; break
        if ok: return k
    return None

rng = random.Random(20260919)
big_shadow = []; idx_by_maxden = Counter(); tot = 0; maxidx = 0
small_shadow = 0
for _ in range(15000):
    v = sorted(rng.sample(range(0, 400), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        for e in ds:
            if e == 0: continue
            ae = abs(e); ratios = [F(d, ae) for d in ds]
            ints = [r for r in ratios if r.denominator == 1]
            if any(int(r) % 8 == 0 for r in ints): continue
            movers = [r for r in ratios if r.denominator != 1]
            if len(movers) != 3: continue
            tot += 1
            md = max(frac(r).denominator for r in movers)
            k = first_clear(movers)
            if k is None:
                if md >= 5: big_shadow.append((v, i, e, [str(frac(r)) for r in movers]))
                else: small_shadow += 1
            else:
                if md >= 5:
                    idx_by_maxden[k] += 1; maxidx = max(maxidx, k)
print(f"live |J|=3 flanks tested: {tot:,}")
print(f"  shadowed with all denominators <= 4 : {small_shadow:,}")
print(f"  shadowed with some denominator >= 5 : {len(big_shadow):,}   <-- claim says 0")
for b in big_shadow[:4]: print(f"      {b}")
print(f"\n  for max-denominator >= 5, first clear opening index distribution:")
print(f"     {dict(sorted(idx_by_maxden.items())[:12])}")
print(f"     largest first-clear index: {maxidx}")
