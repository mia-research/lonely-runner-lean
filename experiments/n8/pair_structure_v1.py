"""Two actions on the spine {1,3,5,7}:
   reflection  u -> 8-u     : orbits {1,7}, {3,5}   -- two inverted pairs
   units       u -> w*u     : one orbit of all four (8 | s*u  iff  8 | s, u odd)
So the AP's four isolation events are ONE orbit under the full group, but TWO under reflection alone.

Where does the pair structure {1,7} vs {3,5} survive the merge?  Scan.
"""
from fractions import Fraction as F
from math import gcd
from collections import Counter

print("1. the two orbit structures")
print(f"   reflection u -> 8-u : " + "  ".join(f"{u}<->{8-u}" for u in (1,3)))
print(f"   units: 3*1=3, 3*3=9=1, 3*5=15=7, 3*7=21=5 mod 8  -> multiplication by 3 swaps the pairs")
print(f"   so <reflection, x3> acts transitively on {{1,3,5,7}}: one orbit of size 4\n")

def blocks(sb, k, a):
    M = 8*a; r = (sb*(8*k+1)) % M
    return min(r, M-r) < a

print("2. where does {1,7} vs {3,5} survive?  blocking rate by (alpha mod 8, beta)")
tab = Counter(); cnt = Counter()
for g in (1,2,3):
    for beta in range(2, 30):
        for alpha in range(1, 200):
            if gcd(alpha, beta) != 1: continue
            a0, a = alpha*g, beta*g
            for k in range(0, 200):
                if not (a <= 8*k+1 <= 7*a): continue
                cls = 'pm1' if alpha % 8 in (1,7) else ('pm3' if alpha % 8 in (3,5) else 'even')
                cnt[(cls, beta)] += 1
                if blocks(a0, k, a): tab[(cls, beta)] += 1
print(f"   {'beta':>5} {'alpha=+/-1':>12} {'alpha=+/-3':>12} {'alpha even':>12}   split?")
for beta in range(2, 14):
    row = []
    for cls in ('pm1','pm3','even'):
        c = cnt[(cls,beta)]
        row.append(100*tab[(cls,beta)]/c if c else float('nan'))
    split = "YES" if abs(row[0]-row[1]) > 5 else ""
    print(f"   {beta:>5} {row[0]:>11.2f}% {row[1]:>11.2f}% {row[2]:>11.2f}%   {split}")
