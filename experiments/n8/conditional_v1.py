"""Conditional density along the divisibility order.

If b | b', then q mod b = (q mod b') mod b, so
    P[ q mod b in I(b) | q mod b' in I(b') ] = |{ r in I(b') : r mod b in I(b) }| / |I(b')|
is a pure TWO-MODULUS quantity.  If it has a positive floor c, a chain of length k gives
density >= c^k > 0 -- and that is existence for chain profiles.
"""
from fractions import Fraction as F

def I(b): return (-(-(b-1)//8), (7*b-1)//8)

def cond(b, bp):
    lo, hi = I(bp); lo2, hi2 = I(b)
    tot = hi - lo + 1
    good = sum(1 for r in range(lo, hi+1) if lo2 <= r % b <= hi2)
    return F(good, tot), good, tot

mn = None; marg = None
rows = []
for bp in range(2, 900):
    for b in range(2, bp):
        if bp % b: continue
        c, g, t = cond(b, bp)
        rows.append((c, b, bp))
        if mn is None or c < mn: mn, marg = c, (b, bp, g, t)
print(f"pairs b | b' with 2 <= b < b' < 900 : {len(rows):,}")
print(f"  MINIMUM conditional density : {mn} = {float(mn):.6f}   at b={marg[0]}, b'={marg[1]}"
      f"  ({marg[2]}/{marg[3]})")
import statistics
f = [float(r[0]) for r in rows]
print(f"  conditional density: min {min(f):.4f}  median {statistics.median(f):.4f}  max {max(f):.4f}")
print(f"  zero conditional densities (would break the product): "
      f"{sum(1 for r in rows if r[0]==0)}")
print()
print("  smallest cases:")
for c, b, bp in sorted(rows)[:8]:
    print(f"     b={b:<4} b'={bp:<5} conditional {c} = {float(c):.4f}"
          f"   b'/b = {bp//b}   b mod 8 = {b%8}, b' mod 8 = {bp%8}")
