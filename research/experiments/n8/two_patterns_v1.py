"""NOT two inverted pairs of points -- two inverted PATTERNS.

The +1 pattern: all x with s*x = 1 (mod 8) for some reading s, i.e. right endpoints (8k+1)/s.
The -1 pattern: all x with s*x = -1 (mod 8), i.e. left endpoints (8k-1)/s.
These are inverted images of one another under x -> 8-x.

CLAIM: the AP's four isolation events are exactly where the two patterns COINCIDE, and the
coincidence is forced by the Klein property u^2 = 1 mod 8:
    x = u  is a +1 endpoint of reading u        (u*u = u^2 = 1 mod 8)
    x = u  is a -1 endpoint of reading 8-u      (u*(8-u) = -u^2 = -1 mod 8)
"""
from fractions import Fraction as F

print("1. the Klein identity that forces the coincidence")
for u in (1,3,5,7):
    print(f"   u={u}:  u*u = {u*u} = {u*u % 8} mod 8    u*(8-u) = {u*(8-u)} = {u*(8-u) % 8} mod 8"
          f"   -> +1 endpoint of reading {u}, -1 endpoint of reading {8-u}")

print("\n2. check on the AP (readings 1..7): each odd x is a +1 endpoint of one reading")
print("   and a -1 endpoint of another")
S = list(range(1,8))
for x in (1,3,5,7):
    plus  = [s for s in S if (s*x) % 8 == 1]
    minus = [s for s in S if (s*x) % 8 == 7]
    print(f"   x={x}:  +1 endpoint of readings {plus}   -1 endpoint of readings {minus}")

print("\n3. do the two patterns coincide ONLY at the odd integers, within [1,7]?")
both = []
for num in range(8, 57):                   # x = num/8 * ... scan rationals p/q, q <= 12
    pass
hits = []
for q in range(1, 13):
    for p in range(q, 7*q+1):
        x = F(p, q)
        if not (1 <= x <= 7): continue
        plus  = [s for s in S if (F(s)*x).denominator == 1 and int(F(s)*x) % 8 == 1]
        minus = [s for s in S if (F(s)*x).denominator == 1 and int(F(s)*x) % 8 == 7]
        if plus and minus: hits.append((x, plus, minus))
hits = sorted(set((h[0], tuple(h[1]), tuple(h[2])) for h in hits))
print(f"   points in [1,7] (denominators <= 12) lying on BOTH patterns: {len(hits)}")
for x, pl, mi in hits:
    print(f"      x={x}   +1 for {list(pl)}   -1 for {list(mi)}"
          + ("   <-- odd integer" if x.denominator == 1 and x.numerator % 2 else ""))
