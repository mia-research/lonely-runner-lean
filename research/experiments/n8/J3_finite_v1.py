"""|J|=3 splits: denominator >= 5 gives a clear opening at index <= 8 (0 exceptions in 2,648).
The residue is denominators <= 4, which is FINITE: fractional parts in {1/2,1/3,2/3,1/4,3/4},
whole parts mod 8 (only rho/8 mod 1 enters).  Enumerate the complete shadowing list."""
from fractions import Fraction as F
from itertools import product
from collections import Counter

FRACS = [F(1,2), F(1,3), F(2,3), F(1,4), F(3,4)]

def shadowed(cfg, kmax=200):
    """cfg = list of (whole mod 8, frac). in the way at k iff k*f + rho/8 within 1/8 of an integer."""
    for k in range(kmax):
        ok = True
        for w, f in cfg:
            rho = F(w) + f
            x = k*f + rho/8
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return False
    return True

tot = 0; sh = []
for fs in product(FRACS, repeat=3):
    for ws in product(range(8), repeat=3):
        cfg = list(zip(ws, fs))
        tot += 1
        if shadowed(cfg): sh.append(cfg)
print(f"configurations enumerated (5^3 fracs x 8^3 whole classes): {tot:,}")
print(f"  SHADOWING configurations: {len(sh):,}   ({100*len(sh)/tot:.3f}%)\n")
byf = Counter(tuple(sorted(str(f) for _, f in c)) for c in sh)
print("  by fractional-part multiset:")
for k, v in byf.most_common(): print(f"     {k}  x{v}")
print(f"\n  distinct fractional-part multisets that can shadow: {len(byf)}")
print(f"  do any involve a denominator-3 part? "
      f"{any('3' in ''.join(k) for k in byf)}")
print(f"\n  sample shadowing configurations (whole mod 8, frac):")
for c in sh[:6]: print(f"     {[(w, str(f)) for w, f in c]}")
